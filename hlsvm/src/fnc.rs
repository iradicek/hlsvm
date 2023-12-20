//! All the parts to build a function. This is a public high-level interface to the virtual-machines code.

use crate::symbol::Symbol;

/// Static types (for variables and function signatures).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Tuple { elts: Box<[Type]> },
    Fnc { params: Box<[Type]>, ret: Box<Type> },
}

/// Function parameter (name and type).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: Symbol,
    pub ty: Type,
}

/// A virtual-machine operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    /// Pushes a local variable to the top of the stack.
    Local {
        sym: Symbol,
    },

    /// Pushes a constant to the top of the stack.
    IntConst {
        value: isize,
    },

    /// All binary operations pop two values from the stack and push the result on the stack.
    IntAdd,
    IntSub,
    IntMul,
    IntLeq,

    /// If-then-else pops a condition from the stack and depending whether it's
    /// true or false executes a squence of operations in appropriate branch.
    /// Each branch should result in a single value (of the same type `ty`) pushed to stack
    /// and hence the whole operation pops condition and pushes a result to the stack.
    Ite {
        ty: Type,
        bthen: Box<[Op]>,
        belse: Box<[Op]>,
    },

    /// Resolves name to a function with n params. Pops n values from the stack, calls
    /// the function and pushes the result to the stack.
    Call {
        name: Symbol,
    },
}

/// A single function, defined by its signature an a sequence of operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fnc {
    params: Box<[Param]>,
    ret: Type,
    ops: Box<[Op]>,
}

impl Fnc {
    pub fn new(params: Box<[Param]>, ret: Type, ops: Box<[Op]>) -> Self {
        Self { params, ret, ops }
    }

    pub fn params(&self) -> &[Param] {
        &self.params
    }

    pub fn ret(&self) -> &Type {
        &self.ret
    }

    pub fn ops(&self) -> &[Op] {
        &self.ops
    }
}
