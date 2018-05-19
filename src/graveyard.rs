#[macro_use]
extern crate nom;

extern crate fnv;
use fnv::FnvHashMap;

extern crate slab;
use slab::Slab;

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use std::{
	fmt,
	env,
	io::{
		self,
		Write,
	},
};

#[derive(Clone, Debug)]
struct Position(Vec<u8>);
impl Position {
	pub fn new() -> Self {
		Position(vec![])
	}
	pub fn push_branch(&mut self, b: u8) {
		self.0.push(b);
	}
	pub fn pop_branch(&mut self, b: u8) {

	}
}


#[derive(Clone, PartialEq, Hash)]
enum Term {
	I, K, S,
	Var(char),
	Ap(usize, usize),
	Abs(char, usize),
}

struct TermBase {
	slab: TSlab,
	slab_locator: FnvHashMap<usize, usize>, //term digest to slab key
	refcounts: FnvHashMap<usize, usize>, // slab key to refcounts
}
impl TermBase {
	pub fn new() -> Self {
		TermBase {
			slab: TSlab::with_capacity(128),
			slab_locator: FnvHashMap::default(),
			refcounts: FnvHashMap::default(),
		}
	}

	pub fn define(&mut self, t: Term) -> usize {
		let mut hasher = DefaultHasher::new();
		t.hash(&mut hasher);
		if let Some(slab_key) = self.slab.get(hasher.finish()) {
			slab_key
		} else {
			self.slab.insert(t)
		}
	}


	fn outermost_leftmost(key: usize) -> usize {
		let t = self.slab[key];

	}

	fn try_rewrite_root(key: usize) -> usize {

	}
}


impl Term {
	fn outermost_leftmost(&mut self, tb: &mut TermBase) -> bool {
		if self.try_rewrite_root(tb) {
			return true
		}
		use Term::*;
		match self {
			I|K|S|Var(_) => false,
			Ap(l, r) => {
				tb.slab[l].outermost_leftmost(tslab)
				|| tb.slab[r].outermost_leftmost(tslab)
			}
			Abs(v, term) => tb.slab[term].outermost_leftmost(tslab),
		}
	}

	fn try_rewrite_root(&mut self) -> bool {
		if let Term::Ap(ref l, ref r) = self {
			// I 
			if &Term::I == l.me() {
				*self = r.clone();
				return true
			}

			// K
			if let Term::Ap(ref ll, ref lr) = l {
				if ll == Term::K {
					*self = lr.clone();
					return true
				}
			}

			// S
			if let Term::Ap(ref ll, ref lr) = l {
				if let Term::Ap(ref lll, ref llr) = ll {
					if lll == Term::S {
						*self = Term::Ap(Box::new((
							Term::Ap(Box::new((
								llr.clone(),
								r.clone(),
							))),
							Term::Ap(Box::new((
								lr.clone(),
								r.clone(),
							))),
						)));
						return true
					}
				}
			}
		}
		false
	}
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
        	Term::Ap(ref l, ref r) => {
    			write!(f, "{:?}", l)?;
        		if let Term::Ap(_,_) = r {
        			write!(f, "({:?})", r)
        		} else {
        			write!(f, "{:?}", r)
        		}
        	},
        	Term::Abs(v, _) => {
        		write!(f, "[")?;
        		let mut n = self;
        		while let Term::Abs(v, ref term) = n {
        			write!(f, "{}", v)?;
        			n = term;
        		}
        		write!(f, "]")?;
    			if let Term::Ap(_,_) = n {
        			write!(f, "({:?})", n)
        		} else {
        			write!(f, "{:?}", n)
        		}
        	},
        	Term::I => write!(f, "I"),
        	Term::K => write!(f, "K"),
        	Term::S => write!(f, "S"),
        	Term::Var(c) => write!(f, "{}", c),
        }
    }
}

fn normalize(mut t: Term) {
	println!("   {:?}", &t);
	for _ in 0..30 {
		if !t.outermost_leftmost() {
			println!("nf.");
			return
		}
		println!("-> {:?}", &t);
	}
	println!("...");
}

fn nest_right(holding: &mut Option<Term>, abs: &mut Vec<char>, inner: Term) {
	if let Some(ref mut h) = holding {
		*h = Term::Ap(Box::new((
			h.clone(),
			inner,
		)));
	} else {
		*holding = Some(inner);
	}
	while let Some(v) = abs.pop() {
		if let Some(ref mut h) = holding {
			*h = Term::Abs(Box::new((
				v,
				h.clone(),
			)));
		} else {
			panic!();
		}
	}
}

type TSlab = Slab<Term>;

fn get_term(s: &[u8]) -> (usize, Option<Term>) {
	let mut abs = vec![];
	let mut abs_on = false;
	let mut holding: Option<Term> = None;
	let mut at = 0;
	while at < s.len() {
		if abs_on {
			match s[at] as char {
				' ' => (),
				']' => abs_on = false,
				'S'|'K'|'I'|'['|'('|')' => return (at, None),
				v => abs.push(v),
			}
		} else {
			match s[at] as char {
				' ' => (),
				'[' => abs_on = true,
				']' => return (at, None),
				'(' => {
					let (x, t) = get_term(&s[at+1..]);
					at += x;
					if let Some(t) = t {
						nest_right(&mut holding, &mut abs, t);
					} else {
						return (at, None)
					}
				},
				')' => {at += 1; break;}
				'S' => nest_right(&mut holding, &mut abs, Term::S),
				'K' => nest_right(&mut holding, &mut abs, Term::K),
				'I' => nest_right(&mut holding, &mut abs, Term::I),
				v => nest_right(&mut holding, &mut abs, Term::Var(v)),
			};
		}
		at += 1;
	}
	if abs_on || !abs.is_empty() {
		return (at, None)
	}
	(at, holding)
}

fn main() {
	let mut tslab: TSlab = Slab::with_capacity(128);
	let args: Vec<String> = env::args().collect();
	if args.len() != 2 {
		print!("Expecting 1 arg!");
	}
	if let (n, Some(t)) = get_term(& args[1].as_bytes()) {
		if n == args[1].as_bytes().len() {
			normalize(t);
			return;
		}
	}
	print!("Failed to parse!");
}

