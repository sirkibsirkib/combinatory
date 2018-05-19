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

#[derive(Copy, Clone, Debug, PartialEq)]
enum RewriteKey {
	NormalForm,
	CanRewrite,
	Unknown,
}

#[derive(Debug)]
struct TermEntry {
	term: Term,
	rewrite_key: RewriteKey,
	refcounts: usize,
}


#[derive(Clone, PartialEq, Hash, Copy, Debug)]
enum Term {
	I, K, S,
	Var(char),
	Ap(usize, usize),
	Abs(char, usize),
}

type TSlab = Slab<TermEntry>;

#[derive(Debug)]
struct TermBase {
	slab: TSlab,
	slab_locator: FnvHashMap<usize, usize>, //term digest to slab key
	i_key: usize,
	k_key: usize,
	s_key: usize,
}
impl TermBase {
	pub fn new() -> Self {
		let mut t = TermBase {
			slab: TSlab::with_capacity(128),
			slab_locator: FnvHashMap::default(),
			i_key: 0,
			k_key: 0,
			s_key: 0,
		};
		t.i_key = t.find_and_ref_up(Term::I);
		t.k_key = t.find_and_ref_up(Term::K);
		t.s_key = t.find_and_ref_up(Term::S);
		t
	}

	fn find_and_ref_up(&mut self, term: Term) -> usize {
		let h = {
			let mut hasher = DefaultHasher::new();
			term.hash(&mut hasher);
			hasher.finish() as usize
		};
		if let Some(&slab_key) = self.slab_locator.get(&h) {
			self.slab[slab_key].refcounts += 1;
			slab_key
		} else {
			let slab_key = self.slab.insert(TermEntry {
				term: term,
				rewrite_key: RewriteKey::Unknown,
				refcounts: 1,
			});
			self.slab_locator.insert(h, slab_key);
			slab_key
		}
	}

	fn ref_down(&mut self, key: usize) {
		//TODO invalid keys. removing stuff too often somewhere
		self.slab[key].refcounts -= 1;
		if self.slab[key].refcounts == 0{
			self.slab.remove(key);
		}
	}

	fn ref_up(&mut self, key: usize) {
		self.slab[key].refcounts += 1;
	}

	fn root_can_rewrite(&mut self, key: usize) -> bool {
		let t = self.slab[key].term;
		if let Term::Ap(l, r) = t {
			if l == self.i_key {
				return true
			}
			if let Term::Ap(ll, lr) = self.slab[l].term {
				if ll == self.k_key {
					return true
				}
			}
			if let Term::Ap(ll, lr) = self.slab[l].term {
				if let Term::Ap(lll, llr) = self.slab[ll].term {
					if lll == self.s_key {
						return true
					}
				}
			}
		}
		false
	}

	fn root_rewrite(&mut self, key: usize) -> usize {
		let t = self.slab[key].term;
		if let Term::Ap(l, r) = t {
			if l == self.i_key {
				self.ref_down(key); // delete Ix
				self.ref_down(l); 	// delete I
				return r;           // keep   x
			}

			// K
			if let Term::Ap(ll, lr) = self.slab[l].term {
				if ll == self.k_key {
					self.ref_down(key);	// delete Kxy
					self.ref_down(l);	// delete Kx
					self.ref_down(ll); 	// delete K
					self.ref_down(r);	// delete y
					return lr; 			// keep   x
				}
			}

			// S
			if let Term::Ap(ll, lr) = self.slab[l].term {
				if let Term::Ap(lll, llr) = self.slab[ll].term {
					if lll == self.s_key {
						let left = self.find_and_ref_up(Term::Ap(llr, r));
						let right = self.find_and_ref_up(Term::Ap(lr, r));
						let whole = self.find_and_ref_up(Term::Ap(left, right));
						self.ref_down(key); // delete Sxyz
						self.ref_down(l);	// delete Sxy
						self.ref_down(ll);	// delete Sx
						return whole;
					}
				}
			}
		}
		key //no change!
	}

	fn normal_form(&mut self, key: usize) -> bool {
		self.assure_rewrite_key_known(key);
		self.slab[key].rewrite_key == RewriteKey::NormalForm
	}

	fn assure_rewrite_key_known(&mut self, key: usize) {
		if self.slab[key].rewrite_key == RewriteKey::Unknown {
			if match self.slab[key].term {
				Term::I |
				Term::K |
				Term::S |
				Term::Var(_) => true,
				Term::Ap(l, r) => {
					self.normal_form(l)
					&& self.normal_form(r)
					&& !self.root_can_rewrite(key)
				}
				Term::Abs(v, term) => self.normal_form(term),
			} {
				self.slab[key].rewrite_key = RewriteKey::NormalForm;
			} else {
				self.slab[key].rewrite_key = RewriteKey::CanRewrite;
			}
		}
	}


	fn outermost_leftmost(&mut self, key: usize) -> usize {
		self.assure_rewrite_key_known(key);
		if self.normal_form(key) {
			return key;
		}
		use RewriteKey::*;
		let t = self.slab[key].term;
		let new_key = self.root_rewrite(key);
		if new_key != key {
			// self.ref_up(new_key);
			// self.ref_down(key);
			return new_key;
		}
		match t {
			Term::I |
			Term::K |
			Term::S |
			Term::Var(_) => panic!("normal form didnt catch"),
			Term::Ap(l, r) => {
				let x = self.outermost_leftmost(l);
				if x != l {
					let z = self.find_and_ref_up(Term::Ap(x, r));
					self.ref_down(key);
					return z;
				}
				let x = self.outermost_leftmost(r);
				if x != r {
					let z = self.find_and_ref_up(Term::Ap(l, x));
					self.ref_down(key);
					return z;
				}
				panic!("WTF shortcut didnt help me");
			},
			Term::Abs(v, term) => {
				let x = self.outermost_leftmost(term);
				if x != term {
					let z = self.find_and_ref_up(Term::Abs(v, x));
					self.ref_down(key);
					return z;
				}
				panic!("WTF MANG");
			}
		}
	}

	fn ref_down_recursively(&mut self, key: usize) {
		let t = self.slab[key].term;
		match t {
			Term::I |
			Term::K |
			Term::S |
			Term::Var(_) => (),
			Term::Ap(l, r) => {
				self.ref_down_recursively(l);
				self.ref_down_recursively(r);
			},
			Term::Abs(v, term) => {
				self.ref_down_recursively(term);
			}
		}
		self.ref_down(key);
	}

	fn print_maybe_parens(&self, key: usize) {
		// println!("MAYBE PARENS {:?}", key);
		let t = self.slab[key].term;
		if let Term::Ap(_,_) = t {
			print!("(");
			self.print_term(key);
			print!(")");
		} else {
			self.print_term(key);
		}
	}

	fn print_term(&self, key: usize) {
		let t = self.slab[key].term;
        match t {
        	Term::Ap(l, r) => {
        		self.print_term(l);
        		self.print_maybe_parens(r);
        	},
        	Term::Abs(v, _) => {
        		print!("[");
        		let mut k = key;
        		while let Term::Abs(v, term) = self.slab[k].term {
        			print!("{}", v);
        			k = term;
        		}
        		print!("]");
        		self.print_maybe_parens(k);
        	},
        	Term::I => print!("I"),
        	Term::K => print!("K"),
        	Term::S => print!("S"),
        	Term::Var(c) => print!("{}", c),
        }
	}

	// fn parse(&mut self, s: &[u8]) -> Option<usize> {
	// 	let mut at = 0;
	// 	let mut term = 
	// 	self.parse_inner_term(s, &mut at)
	// }

	// fn parse_inner_abs(&mut self, s: &[u8], at: &mut usize) -> Option<usize> {
		
	// }

	// fn parse_inner_term(&mut self, s: &[u8], at: &mut usize) -> Option<usize> {
	// 	while *at < s.len() {
	// 		match s[*at] as char {
	// 			' ' => (),
	// 			'[' => parse_inner_abs()
	// 			']' => return (at, None),
	// 			'(' => {
	// 				let (x, t) = self.parse(&s[at+1..]);
	// 				at += x;
	// 				if let Some(t) = t {
	// 					self.nest_right(&mut holding, &mut abs, t);
	// 				} else {
	// 					return (at, None)
	// 				}
	// 			},
	// 			')' => {at += 1; break;}
	// 			'S' => self.nest_right(&mut holding, &mut abs, Term::S),
	// 			'K' => self.nest_right(&mut holding, &mut abs, Term::K),
	// 			'I' => self.nest_right(&mut holding, &mut abs, Term::I),
	// 			v => self.nest_right(&mut holding, &mut abs, Term::Var(v)),
	// 		}
	// 	}
	// }


	// fn nest_right(&mut self, holding: &mut Option<Term>, abs: &mut Vec<char>, inner: Term) {
	// 	if let Some(ref mut h) = holding {
	// 		let t = Term::Ap()
	// 		*h = Term::Ap(Box::new((
	// 			h.clone(),
	// 			inner,
	// 		)));
	// 	} else {
	// 		*holding = Some(inner);
	// 	}
	// 	while let Some(v) = abs.pop() {
	// 		if let Some(ref mut h) = holding {
	// 			*h = Term::Abs(Box::new((
	// 				v,
	// 				h.clone(),
	// 			)));
	// 		} else {
	// 			panic!();
	// 		}
	// 	}
	// }



	// fn parse(&mut self, s: &[u8]) -> (usize, Option<usize>) {
	// 	let mut abs = vec![];
	// 	let mut abs_on = false;
	// 	let mut holding: Option<Term> = None;
	// 	let mut at = 0;
	// 	while at < s.len() {
	// 		if abs_on {
	// 			match s[at] as char {
	// 				' ' => (),
	// 				']' => abs_on = false,
	// 				'S'|'K'|'I'|'['|'('|')' => return (at, None),
	// 				v => abs.push(v),
	// 			}
	// 		} else {
	// 			match s[at] as char {
	// 				' ' => (),
	// 				'[' => abs_on = true,
	// 				']' => return (at, None),
	// 				'(' => {
	// 					let (x, t) = self.parse(&s[at+1..]);
	// 					at += x;
	// 					if let Some(t) = t {
	// 						self.nest_right(&mut holding, &mut abs, t);
	// 					} else {
	// 						return (at, None)
	// 					}
	// 				},
	// 				')' => {at += 1; break;}
	// 				'S' => self.nest_right(&mut holding, &mut abs, Term::S),
	// 				'K' => self.nest_right(&mut holding, &mut abs, Term::K),
	// 				'I' => self.nest_right(&mut holding, &mut abs, Term::I),
	// 				v => self.nest_right(&mut holding, &mut abs, Term::Var(v)),
	// 			};
	// 		}
	// 		at += 1;
	// 	}
	// 	if abs_on || !abs.is_empty() {
	// 		return (at, None)
	// 	}
	// 	(at, holding)
	// }
}

struct Parser<'a, 'b> {
	tb: &'a mut TermBase,
	at: usize,
	src: &'b [u8],
}

impl<'a, 'b> Parser<'a, 'b> {
	pub fn parse(tb: &'a mut TermBase, src: &'b [u8]) -> Option<usize> {
		let mut parser = Parser {
			tb,
			at: 0,
			src,
		};
		let x = parser.parse_term();
		if parser.at != src.len() {
			parser.cleanup(x);
			return None
		} else {
			x
		}
	}

	fn cleanup(&mut self, key: Option<usize>) {
		if let Some(key) = key {
			self.tb.ref_down_recursively(key);
		}
		self.at = self.src.len()
	}

	fn push_raw_term(&mut self, o: &mut Option<usize>, t: Term) {
		// println!("printing {:?}", t);
		let n = self.tb.find_and_ref_up(t);
		self.push_raw_term2(o, n)
	}

	fn push_raw_term2(&mut self, o: &mut Option<usize>, n: usize) {
		if let Some(prev) = *o {
			let a = Term::Ap(prev, n);
			let q = self.tb.find_and_ref_up(a);
			*o = Some(q);
		} else {
			*o = Some(n);
		}
	}

	fn parse_term(&mut self) -> Option<usize> {
		let mut o: Option<usize> = None;
		loop {
			let c = self.src[self.at] as char;
			self.at += 1;
			match c {
				' ' => (),
				'(' => {
					if let Some(x) = self.parse_term() {
						self.push_raw_term2(&mut o, x);
					} else {
						self.cleanup(o);
						return None;
					}
				},
				')' => return o,
				'S' => self.push_raw_term(&mut o, Term::S),
				'K' => self.push_raw_term(&mut o, Term::K),
				'I' => self.push_raw_term(&mut o, Term::I),
				 v  => self.push_raw_term(&mut o, Term::Var(v)),
			};
			if self.at >= self.src.len() {
				break;
			}
		}
		o
	}
	fn digest_abs(&mut self, c: char) {
		//TODO push down abstractions! gonna be fun. include that in rewriting
	}
}




fn main() {
	let mut tb = TermBase::new();
	let args: Vec<String> = env::args().collect();
	if args.len() != 2 {
		print!("Expecting 1 arg!");
	}
	if let Some(mut k) = Parser::parse(&mut tb, &args[1].as_bytes()) {
		// print!("<{:?}> ", k);
		print!("   ");
		tb.print_term(k);
		println!();
		// println!(">> {:?}", &tb);
		for _ in 0..20 {
			if tb.normal_form(k) {
				return;
			}
			k = tb.outermost_leftmost(k);
			print!("-> ");
			tb.print_term(k);
			println!();
		}
		println!("...");
	} else {
		println!("Failed to parse");
	}
}

