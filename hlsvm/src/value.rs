//! Runtime value managmen. This quite simple for time being.

use std::rc::Rc;

/// A runtime value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Int {
        value: isize,
    },
    /// An immutable sequence of values (e.g., tuple, struct, array).
    Block {
        elts: Rc<[Value]>,
    },
}
