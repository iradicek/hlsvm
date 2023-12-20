//!
//! # High Level Stack Virtual Machine
//!
//! A (currently) very simple virtual machine that type-checks and runs stack-based code. The high-level (public) code
//! does not have any jump operations, that is control-flow is limited to built-in higher-level constructs
//! (if, call, ...).
//!

pub(crate) mod ctx;
pub mod fnc;
pub(crate) mod instr;
pub mod symbol;
pub mod value;
pub mod vm;

/// A helper when an Option expression result is expected to be None.
pub(crate) fn expect_none<T>(x: Option<T>) {
    match x {
        None => (),
        Some(_) => panic!("Expected None"),
    }
}

#[cfg(test)]
mod tests;
