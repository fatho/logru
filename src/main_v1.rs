use std::rc::Rc;
use std::vec::Vec;
use std::boxed::Box;
use std::cell::RefCell;

// #[derive(Debug, Copy, Clone)]
// enum Person {
//     Alice, Bob, Eve, Peter
// }


#[derive(Debug)]
struct LVar<T>(Rc<RefCell<Option<T>>>);


impl<T> Clone for LVar<T> {
    fn clone(&self) -> Self {
        LVar(self.0.clone())
    }
}

trait Undoable {
    fn undo(&mut self);
}

struct Assignment<T>(LVar<T>);

impl<T> Undoable for Assignment<T> {
    fn undo(&mut self) {
        *(self.0).0.borrow_mut() = None;
    }
}

struct UnificationContext<'a>(Vec<Box<Undoable + 'a>>);

impl<'a> UnificationContext<'a> {
    fn new() -> Self {
        UnificationContext(Vec::new())
    }

    fn register<T: 'a>(mut self, var: LVar<T>) -> Self {
        self.0.push(Box::new(Assignment(var)));
        self
    }

    fn persist(&mut self) {
        self.0.clear()
    }
}

impl<'a> Drop for UnificationContext<'a> {
    fn drop(&mut self) {
        for assignment in self.0.iter_mut() {
            assignment.undo()
        }
    }
}


trait Unify {
    fn unify<'a>(&mut self, other: &mut Self, context: UnificationContext<'a>) -> Option<UnificationContext<'a>> where Self: 'a;
}


impl<T> Unify for LVar<T> where T: Unify + Clone {
    fn unify<'a>(&mut self, other: &mut Self, context: UnificationContext<'a>) -> Option<UnificationContext<'a>> where Self: 'a {
        if self.0.borrow().is_none() {
            {
                let v1 = Rc::get_mut(&mut self.0).unwrap();
                *v1 = (*other.0).clone();
            }
            Some(context.register(self.clone()))
        } else if other.0.borrow().is_none() {
            {
                let v1 = Rc::get_mut(&mut other.0).unwrap();
                *v1 = (*self.0).clone();
            }
            Some(context.register(other.clone()))
        } else {
            let mut val1 = self.0.borrow_mut();
            let mut val2 = other.0.borrow_mut();
            val1.as_mut().unwrap().unify(val2.as_mut().unwrap(), context)
        }
        // let mut v1 = self.0.borrow_mut();
        // match *v1 {
        //     None => {
        //         *v1 = (*other.0).borrow().clone();
        //         Some(context.register(self.clone()))
        //     },
        //     Some(ref mut val1) => {
        //         let mut v2 = other.0.borrow_mut();
        //         match *v2 {
        //             None => {
        //                 *v2 = Some(val1.clone());
        //                 Some(context.register(self.clone()))
        //             },
        //             Some(val2) => {
        //                 val1.unify(&mut val2, context)
        //             }
        //         }
        //     }
        // }
    }
}


fn fv<T>() -> LVar<T> {
    LVar(Rc::new(RefCell::new(None)))
}

fn bv<T>(val: T) -> LVar<T> {
    LVar(Rc::new(RefCell::new(Some(val))))
}


#[derive(Debug, Clone)]
enum N {
    Z, S(LVar<N>)
}


impl Unify for N {
    fn unify<'a>(&mut self, other: &mut Self, context: UnificationContext<'a>) -> Option<UnificationContext<'a>> where Self: 'a {
        match self {
            N::Z => match other {
                N::Z => Some(context),
                N::S(_) => None
            },
            N::S(arg) => match other {
                N::Z => None,
                N::S(arg2) => arg.unify(arg2, context)
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Add(LVar<N>, LVar<N>, LVar<N>);

// fn parent()


fn main() {
    let mut a = N::S(bv(N::S(bv(N::Z))));
    let mut b = N::S(fv());
    let mut c = N::S(bv(N::Z));

    println!("Before:\n  a: {:?}\n  b: {:?}\n", a, b);

    {
        println!("a =:= b");
        let success = a.unify(&mut b, UnificationContext::new());
        if success.is_some() {
            println!("Unifiable!")
        } else {
            println!("Not unifiable!")
        }
        println!("After:\n  a: {:?}\n  b: {:?}\n", a, b);
    }

    println!("Undone:\n  a: {:?}\n  b: {:?}\n", a, b);

    {
        println!("a =:= b");
        let success = a.unify(&mut b, UnificationContext::new());

        match success {
            None => println!("Not unifiable!"),
            Some(context) => {
                println!("Unifiable!");
                println!("After:\n  a: {:?}\n  b: {:?}\n", a, b);
                println!("a =:= c");
                let success = a.unify(&mut c, context);
                if success.is_some() {
                    println!("Unifiable!");
                    println!("After:\n  a: {:?}\n  b: {:?}\n", a, b);
                } else {
                    println!("Not unifiable!")
                }
            }
        }
    }
    println!("Lost:\n  a: {:?}\n  b: {:?}\n", a, b);
    // forall(|x| lhs(Add(bv(N::Z), x, x)));
    // forall(|x y z| lhs(Add(S(x), y, S(z))).follows_from(Add(x, y z));
}
