//! A symbol (name) managment.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    rc::Rc,
};

use crate::expect_none;

/// An internal structure to keep mapping between symbols (which are actually just integers)
/// to their names. Symbols are integers because we internally don't care about their names
/// (we just need to distinguish them), but for error reporting (and eventually debugging) it's
/// convenient to also keep their names.
pub(crate) struct SymbolTable {
    forward: HashMap<usize, String>,
    back: HashMap<String, usize>,
}

/// A symbol that represents an unique name (e.g., for variables and functions).
pub struct Symbol {
    // A reference to a symbol table where this symbol is stored. A symbol table can be mutable
    // and referenced by multiple symbols, so we need to wrap it in Rc and RefCell.
    table: Rc<RefCell<SymbolTable>>,
    index: usize,
}

impl SymbolTable {
    pub fn new() -> Self {
        let forward = HashMap::new();
        let back = HashMap::new();
        Self { forward, back }
    }

    /// Creates a symbol (index) from a string. If the table contains symbol it returns it,
    /// otherwise it creates a fresh symbol.
    /// TODO: We return only an index here as symbol requires a Rc-RefCell reference to the table,
    /// which the table itself does not have. Hence the user of the table is required to convert this
    /// to the symbol.
    pub fn symbol_from_string(&mut self, s: &str) -> usize {
        match self.back.get(s) {
            Some(index) => *index,
            None => {
                let new_index = self.forward.len();
                expect_none(self.forward.insert(new_index, s.to_string()));
                expect_none(self.back.insert(s.to_string(), new_index));
                new_index
            }
        }
    }

    /// Converts symbol to a string from which it was created.
    fn symbol_to_string(&self, s: &Symbol) -> String {
        self.forward.get(&s.index).unwrap().clone()
    }
}

impl Symbol {
    pub(crate) fn new(table: Rc<RefCell<SymbolTable>>, index: usize) -> Self {
        Self { table, index }
    }

    /// The integer value of the symbol. This is available only internally, as it's
    /// and implementation detail.
    pub(crate) fn index(&self) -> usize {
        self.index
    }

    /// Checks that two symbols belong to the same table. This is useful for all
    /// comparison operations, as it does not make sense to compare to symbols
    /// from different tables.
    fn check_table(&self, other: &Self) {
        if !std::ptr::eq(self.table.as_ptr(), other.table.as_ptr()) {
            panic!("Comparison of symbols from different tables.")
        }
    }
}

// Note: we need to implement a lot of traits manually because we esentially want symbol
//  to behave as an integer, but we cannot ignore that it keeps a reference to the table
//  where it was created. Most of the traits call underlying operaton on the integer value
//  and either ignore the table reference or check that it makes sense (where appropriate).

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.check_table(other);
        self.index == other.index
    }
}

impl Eq for Symbol {}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.check_table(other);
        self.index.cmp(&other.index)
    }
}

impl Hash for Symbol {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Include only index in debug since table is not debug
        f.debug_struct("Symbol")
            .field("index", &self.index)
            .finish()
    }
}

impl From<&Symbol> for String {
    fn from(sym: &Symbol) -> Self {
        sym.table.borrow().symbol_to_string(sym)
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Display symbol from a string representation
        let s: String = self.into();
        write!(f, "{}", s)
    }
}

impl Clone for Symbol {
    fn clone(&self) -> Self {
        Self {
            table: Rc::clone(&self.table),
            index: self.index,
        }
    }
}
