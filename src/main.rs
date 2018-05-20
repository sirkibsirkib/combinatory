#[macro_use]
extern crate nom;

extern crate fnv;
use fnv::{FnvHashMap, FnvHashSet};

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
}


#[derive(Clone, PartialEq, Hash, Copy, Debug)]
enum Term {
	I, K, S,
	Var(char),
	Ap(usize, usize),
	Abs(char, usize),
}
impl Term {
	pub fn atomic(&self) -> bool {
		match self {
			Term::I |
			Term::K |
			Term::S |
			Term::Var(_) => true,
			Term::Ap(_,_) |
			Term::Abs(_,_) => false,
		}
	}
}

type TSlab = Slab<TermEntry>;

#[derive(Debug)]
struct TermBase {
	slab: TSlab,
	slab_locator: FnvHashMap<usize, usize>, //term digest to slab key
	defined: FnvHashMap<char, usize>,
	i_key: usize,
	k_key: usize,
	s_key: usize,
}
impl TermBase {
	pub fn new() -> Self {
		let mut t = TermBase {
			slab: TSlab::with_capacity(128),
			slab_locator: FnvHashMap::default(),
			defined: FnvHashMap::default(),
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
			slab_key
		} else {
			let slab_key = self.slab.insert(TermEntry {
				term: term,
				rewrite_key: RewriteKey::Unknown,
			});
			self.slab_locator.insert(h, slab_key);
			slab_key
		}
	}

	fn root_can_rewrite(&mut self, key: usize) -> bool {
		let t = self.slab[key].term;
		if let Term::Abs(v, a) = t {
			let q = self.slab[a].term;
			if q.atomic() {
				return true
			} else if let Term::Ap(al, ar) = q {
				return true
			}
		}
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
		if let Term::Abs(v, a) = t {
			let q = self.slab[a].term;
			if q.atomic() {
				if let Term::Var(x) = q {
					if v == x { return self.i_key }
				}
				let k = self.k_key;
				return self.find_and_ref_up(Term::Ap(k, a));
			} else if let Term::Ap(al, ar) = q {
				let s = self.s_key;
				let new_left = self.find_and_ref_up(Term::Abs(v, al));
				let new_right = self.find_and_ref_up(Term::Abs(v, ar));
				let inner = self.find_and_ref_up(Term::Ap(s, new_left));
				let outer = self.find_and_ref_up(Term::Ap(inner, new_right));
				return outer;
			}
		}
		if let Term::Ap(l, r) = t {
			if l == self.i_key {
				// self.ref_down(key); // delete Ix
				// self.ref_down(l); 	// delete I
				return r;           // keep   x
			}

			// K
			if let Term::Ap(ll, lr) = self.slab[l].term {
				if ll == self.k_key {
					// self.ref_down(key);	// delete Kxy
					// self.ref_down(l);	// delete Kx
					// self.ref_down(ll); 	// delete K
					// self.ref_down(r);	// delete y
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
						// self.ref_down(key); // delete Sxyz
						// self.ref_down(l);	// delete Sxy
						// self.ref_down(ll);	// delete Sx
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
				Term::Abs(v, term) => {
					!self.root_can_rewrite(key)
					&& self.normal_form(term)
				}
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
					return z;
				}
				let x = self.outermost_leftmost(r);
				if x != r {
					let z = self.find_and_ref_up(Term::Ap(l, x));
					return z;
				}
				panic!("WTF shortcut didnt help me");
			},
			Term::Abs(v, term) => {
				let x = self.outermost_leftmost(term);
				if x != term {
					let z = self.find_and_ref_up(Term::Abs(v, x));
					return z;
				}
				panic!("WTF MANG");
			}
		}
	}

	// fn is_redex(&self, key: usize) -> bool {
	// 	let t = self.slab[key].term;
	// 	if t.atomic() {
	// 		return false;
	// 	}
	// 	match t {
	// 		Term::Ap(l, r) => {
	// 			self.ref_down_recursively(l);
	// 			self.ref_down_recursively(r);
	// 		},
	// 		Term::Abs(v, term) => {
	// 			self.ref_down_recursively(term);
	// 		}
	// 	}
	// }

	fn print_maybe_parens(&self, key: usize) {
		if self.slab[key].term.atomic() {
			self.print_term(key);
		} else {
			print!("(");
			self.print_term(key);
			print!(")");
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

	fn gc_all_but_defined(&mut self) {
		let x: Vec<_> = self.defined.values().map(|x| *x).collect();
		self.gc_all_but(x.into_iter())
	}

	fn gc_all_but(&mut self, roots: impl Iterator<Item=usize>) {
		let mut set = FnvHashSet::default();
		set.insert(self.i_key);
		set.insert(self.k_key);
		set.insert(self.s_key);
		for root in roots {
			for key in Traverser::new(self, TraversalOrder::LeftmostOutermost, root) {
				set.insert(key);
				print!("... <{}> ", key);
				self.print_term(key);
				println!();
			}
		}
		println!("retaining {:?} things", set.len());
		self.slab.retain(|key, _| set.contains(&key));
	}



	fn define(&mut self, varname: char, key: usize) {
		self.defined.insert(varname, key);
	}
}

enum TraversalOrder {
	LeftmostOutermost,
}

struct Traverser<'a> {
	tb: &'a TermBase,
	traversal_order: TraversalOrder,
	stack: Vec<usize>,
}
impl<'a> Traverser<'a> {
	pub fn new(tb: &'a TermBase, traversal_order: TraversalOrder, root: usize) -> Traverser<'a> {
		Traverser {
			tb,
			traversal_order,
			stack: vec![root],
		}
	}
}

impl<'a> Iterator for Traverser<'a>{
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
    	if let Some(key) = self.stack.pop() {
    		match self.tb.slab[key].term {
	        	Term::Ap(l, r) => {
	        		match self.traversal_order {
	        			TraversalOrder::LeftmostOutermost => {
	        				self.stack.push(r);
			        		self.stack.push(l);
			        		Some(key)
	        			}
	        		}
	        	},
	        	Term::Abs(v, k) => {
	        		match self.traversal_order {
	        			TraversalOrder::LeftmostOutermost => {
	        				self.stack.push(k);
	        				Some(key)
	        			}
	        		}
	        	},
	        	Term::I |
	        	Term::K |
	        	Term::S |
	        	Term::Var(_) => Some(key),
	        }
    	} else {
    		None
    	}
    }
}

struct Parser<'a, 'b> {
	tb: &'a mut TermBase,
	at: usize,
	abs: Vec<char>,
	src: &'b [u8],
}

impl<'a, 'b> Parser<'a, 'b> {
	pub fn parse(tb: &'a mut TermBase, src: &'b [u8]) -> Option<usize> {
		let mut parser = Parser {
			tb,
			at: 0,
			src,
			abs: vec![],
		};
		let x = parser.parse_term();
		if parser.at != src.len() {
			// parser.cleanup(x);
			return None
		} else {
			x
		}
	}

	// fn cleanup(&mut self, key: Option<usize>) {
	// 	if let Some(key) = key {
	// 		self.tb.ref_down_recursively(key);
	// 	}
	// 	self.at = self.src.len()
	// }

	fn push_raw_term(&mut self, o: &mut Option<usize>, t: Term, abs_vec: &mut Vec<char>) {
		// println!("printing {:?}", t);
		let n = self.tb.find_and_ref_up(t);
		self.push_raw_term2(o, n, abs_vec)
	}

	fn push_raw_term2(&mut self, o: &mut Option<usize>, n: usize, abs_vec: &mut Vec<char>) {
		let mut x = if let Some(mut prev) = *o {
			let a = Term::Ap(prev, n);
			let q = self.tb.find_and_ref_up(a);
			q
		} else {
			n
		};
		for v in abs_vec.drain(..).rev() {
			let new_term = Term::Abs(v, x);
			x = self.tb.find_and_ref_up(new_term);
		}
		*o = Some(x)	
	}

	fn parse_abs(&mut self) {
		println!("parse abs");
		loop {
			let c = self.src[self.at] as char;
			self.at += 1;
			
		}

	}

	fn parse_term(&mut self) -> Option<usize> {
		let mut o: Option<usize> = None;
		let mut abs_vec = vec![];
		let mut abs = false;
		loop {
			let c = self.src[self.at] as char;
			self.at += 1;
			if abs {
				match c {
					' ' => (),
					'('|')'|'S'|'K'|'I'|'[' => return None,
				 	']' => abs = false,
					 v  => {
					 	if let Some(&key) = self.tb.defined.get(&v) {
					 		return None;
					 	} else {
					 		abs_vec.push(v);
					 	}				 	
					},
				}
			} else {
				match c {
					'[' => abs = true,
					' ' => (),
					'(' => {
						if let Some(x) = self.parse_term() {
							self.push_raw_term2(&mut o, x, &mut abs_vec);
						} else {
							// self.cleanup(o);
							return None;
						}
					},
					']' => return None,
					')' => return o,
					'S' => self.push_raw_term(&mut o, Term::S, &mut abs_vec),
					'K' => self.push_raw_term(&mut o, Term::K, &mut abs_vec),
					'I' => self.push_raw_term(&mut o, Term::I, &mut abs_vec),
					 v  => {
					 	if let Some(&key) = self.tb.defined.get(&v) {
					 		println!("MATCHED defined TERM {:?}", v);
					 		self.push_raw_term2(&mut o, key, &mut abs_vec);
					 	} else {
					 		self.push_raw_term(&mut o, Term::Var(v), &mut abs_vec);
					 	}				 	
					},
				};
			}
			if self.at >= self.src.len() {
				break;
			}
		}
		o
	}
}

use std::io::{BufRead};


fn main() {
	let mut tb = TermBase::new();
	let stdin = io::stdin();
    let mut iterator = stdin.lock().lines();
    'outer: loop {
    	let line1 = iterator.next().unwrap().unwrap();
    	let bytes = line1.as_bytes();
    	// if bytes.len()
    	if bytes.len() >= 3 && bytes[1] as char == '=' {
    		if let Some(mut k) = Parser::parse(&mut tb, &bytes[2..]) {
    			println!("DEFINING");
    			tb.define(bytes[0] as char, k);
    			println!("defined <{},{}>", bytes[0] as char, k);
    		}
    	} else if bytes.len() >= 3 && bytes[0] as char == '>' && bytes[1] as char == '*' {
    		if let Some(mut k) = Parser::parse(&mut tb, &bytes[2..]) {
    			println!("REWRITING");
				print!("   ");
				tb.print_term(k);
				println!();
				for _ in 0..20 {
					if tb.normal_form(k) {
						continue 'outer;
					}
					k = tb.outermost_leftmost(k);
					print!("-> ");
					tb.print_term(k);
					println!();
				}
				println!("...");
			}
    	} else {
    		println!("Failed to understand");
    	}
    	// tb.gc_all_but_defined();
	}
}
 //    let line2 = iterator.next().unwrap().unwrap();


	// let args: Vec<String> = env::args().collect();
	// if args.len() != 2 {
	// 	print!("Expecting 1 arg!");
	// 	return;
	// }
	// if let Some(mut k) = Parser::parse(&mut tb, &args[1].as_bytes()) {
	// 	// print!("<{:?}> ", k);
	// 	print!("   ");
	// 	tb.print_term(k);
	// 	println!();
	// 	// println!(">> {:?}", &tb);
	// 	for _ in 0..20 {
	// 		tb.gc_all_but(std::iter::once(k));
	// 		if tb.normal_form(k) {
	// 			return;
	// 		}
	// 		k = tb.outermost_leftmost(k);
	// 		print!("-> ");
	// 		tb.print_term(k);
	// 		println!();
	// 	}
	// 	println!("...");
	// } else {
	// 	println!("Failed to parse");
	// }
// }

