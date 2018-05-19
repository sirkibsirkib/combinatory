use fnv::FnvHashMap;
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

#[derive(Copy, Debug, Hash)]
struct TermEntry {
	term: Term,
	rewrite_key: RewriteKey,
	refcounts: usize,
}


#[derive(Clone, PartialEq, Hash)]
enum Term {
	I, K, S,
	Var(char),
	Ap(usize, usize),
	Abs(char, usize),
}

type TSlab = Slab<TermEntry>;

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

	fn find_and_ref_up(term: Term) -> usize {
		let mut hasher = DefaultHasher::new();
		term.hash(&mut hasher);
		if let Some(slab_key) = self.slab.get(hasher.finish()) {
			self.slab[slab_key].refcounts += 1;
			slab_key
		} else {
			self.slab.insert(TermEntry {
				term: term,
				rewrite_key: RewriteKey::Unknown,
				refcounts: 1,
			})
		}
	}

	fn ref_down(&mut self, key: usize) {
		self.slab[key].refcounts -= 1;
		if self.slab[key].refcounts == 0{
			self.slab.remove(key);
		}
	}

	fn ref_up(&mut self, key: usize) {
		self.slab[key].refcounts += 1;
	}

	fn root_can_rewrite(self, key: usize) -> bool {
		let t = self.slab[key];
		if let Term::Ap(l, r) = self {
			if l = self.i_key {
				return true
			}
			if let Term::Ap(ll, lr) = l {
				if ll == self.k_key {
					return true
				}
			}
			if let Term::Ap(ll, lr) = l {
				if let Term::Ap(lll, llr) = ll {
					if lll == self.s_key {
						return true
					}
				}
			}
		}
		false
	}

	fn root_rewrite(&mut self, key: usize) -> usize {
		let t = self.slab[key];
		if let Term::Ap(l, r) = self {
			// I 
			if l = self.i_key {
				self.ref_down(key); // delete Ix
				self.ref_down(l); 	// delete I
				return r;           // keep   x
			}

			// K
			if let Term::Ap(ll, lr) = l {
				if ll == self.k_key {
					self.ref_down(key);	// delete Kxy
					self.ref_down(l);	// delete Kx
					self.ref_down(ll); 	// delete K
					self.ref_down(r);	// delete y
					return lr; 			// keep   x
				}
			}

			// S
			if let Term::Ap(ll, lr) = l {
				if let Term::Ap(lll, llr) = ll {
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

	fn assure_rewrite_key_known(&mut self, key: usize) {
		if let t.rewrite_key == Unknown {
			use Term::*;
			if match {
				I|K|S|Var(_) => true,
				Ap(l, r) => {
					if self.normal_form(l)
					&& self.normal_form(r)
					&& !self.root_can_rewrite(key)
				}
				Abs(v, term) => self.normal_form(term),
			} {
				t.rewrite_key = NormalForm;
			} else {
				t.rewrite_key = CanRewrite;
			}
		}
	}


	fn outermost_leftmost(&mut self, key: usize) -> usize {
		self.assure_rewrite_key_known(key);
		use RewriteKey::*;
		let t = self.slab[key];
		let new_key = self.root_rewrite(key);
		if new_key != key {
			self.increment_refs(rewrites_to_key);
			self.decrement_refs(key);
			return new_key;
		}
		match t {
			I|K|S|Var(_) => panic!("normal form didnt catch"),
			Ap(l, r) => {
				let x = outermost_leftmost(l);
				if x != l {
					let z = self.find_and_ref_up(Term::Ap(x, r))
					self.decrement_refs(key);
					return z;
				}
				let x = outermost_leftmost(r);
				if x != r {
					let z = self.find_and_ref_up(Term::Ap(x, r))
					self.decrement_refs(key);
					return z;
				}
				panic!("WTF shortcut didnt help me");
			}
			Abs(v, term) => {
				let x = outermost_leftmost(term);
				if x != term {
					let z = self.find_and_ref_up(Term::Abs(v, x))
					self.decrement_refs(key);
					return z;
				}
				panic!("WTF MANG");
			}
		}
	}
}
