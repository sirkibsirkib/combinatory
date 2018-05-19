extern crate slab;
use slab::Slab;

use std::fmt;
use std::io;
use std::io::Write;

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

#[derive(Clone, PartialEq)]
enum Term {
	Ap(Box<(Term, Term)>),
	Abs(Box<(char, Term)>),
	I, K, S, // constants
	Var(char),
}

impl Term {
	fn try_rewrite_root(&mut self) -> bool {
		if let Term::Ap(me) = self {
			// I 
			if let Term::I = me.0 {
				*self = me.1.clone();
				return true
			}

			// K
			if let Term::Ap(ref me_left) = me.0 {
				if me_left.0 == Term::K {
					*self = me_left.1.clone();
					return true
				}
			}

			// S
			if let Term::Ap(ref me_left) = me.0 {
				if let Term::Ap(ref me_left_left) = me_left.0 {
					if me_left_left.0 == Term::S {
						// *self = Term::Var('q');
						*self = Term::Ap(Box::new((
							Term::Ap(Box::new((
								me_left_left.1.clone(),
								me.1.clone(),
							))),
							Term::Ap(Box::new((
								me_left.1.clone(),
								me.1.clone(),
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
        	Term::Ap(ref x) => {
    			write!(f, "{:?}", x.0)?;
        		if let Term::Ap(_) = x.1 {
        			write!(f, "({:?})", x.1)
        		} else {
        			write!(f, "{:?}", x.1)
        		}
        	},
        	Term::Abs(ref x) => {
    			write!(f, "[{}]", x.0)?;
    			if let Term::Ap(_) = x.1 {
        			write!(f, "({:?})", x.1)
        		} else {
        			write!(f, "{:?}", x.1)
        		}
        	},
        	Term::I => write!(f, "I"),
        	Term::K => write!(f, "K"),
        	Term::S => write!(f, "S"),
        	Term::Var(c) => write!(f, "{}", c),
        }
    }
}

fn root_rewrite_show(mut t: Term) {
	println!("{:?}", &t);
	t.try_rewrite_root();
	println!(" -> {:?}\n", &t);
}

fn main() {
	let mut slab: Slab<Term> = Slab::with_capacity(1024);

	let mut t1 = Term::Ap(Box::new((
		Term::I,
		Term::Var('a'),
	)));
	let mut t2 = Term::Ap(Box::new((
		Term::Ap(Box::new((
			Term::K,
			Term::Var('p'),
		))),
		Term::Var('q'),
	)));
	let mut t3 = Term::Ap(Box::new((
		Term::Ap(Box::new((
			Term::Ap(Box::new((
				Term::S,
				Term::Var('x'),
			))),
			Term::Var('y'),
		))),
		Term::Var('z'),
	)));
	root_rewrite_show(t1);
	root_rewrite_show(t2);
	root_rewrite_show(t3);
}
