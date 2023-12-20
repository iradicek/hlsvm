//! Internal moduke for context that tracks types of stack values during code generation.
use immutable_map::TreeMap;

use crate::{fnc::Type, symbol::Symbol};

/// A type for the context (stack) value.
#[derive(Debug, Clone)]
struct CtxValue<'a> {
    /// Depth (offset) of the stack when added.
    depth: usize,
    // Note: Context cannot outlive code generation and hence any type
    // that is referenced is going to be short-lived, so we can keep only reference.
    ty: &'a Type,
}

/// A context / mapping of variables to their types and offset on the stack.
#[derive(Clone)]
pub struct Ctx<'a> {
    /// Current depth of the stack.
    depth: usize,
    /// Immutable mapping from symbols to context values.
    map: TreeMap<&'a Symbol, CtxValue<'a>>,
}

impl<'a> Ctx<'a> {
    pub fn new() -> Self {
        Self {
            depth: 0,
            map: TreeMap::new(),
        }
    }

    /// Adds a non-variable value to context.
    pub fn add_value(self) -> Self {
        Self {
            depth: self.depth + 1,
            map: self.map,
        }
    }

    /// Drops a non-variable value from context.
    pub fn drop_value(self) -> Self {
        Self {
            depth: self.depth - 1,
            map: self.map,
        }
    }

    /// Adds a symbol mapping to stack.
    pub fn add_symbol(&self, symbol: &'a Symbol, ty: &'a Type) -> Self {
        let new_depth = self.depth + 1;
        let val = CtxValue {
            depth: new_depth,
            ty,
        };
        let new_map = self.map.insert(symbol, val);
        Self {
            depth: new_depth,
            map: new_map,
        }
    }

    /// Finds a symbol in the context. Returns it's offset from the top of the stack and type.
    pub fn get_symbol(&self, symbol: &'a Symbol) -> Option<(usize, &'a Type)> {
        self.map
            .get(symbol)
            .map(|val| (self.depth - val.depth, val.ty))
    }
}
