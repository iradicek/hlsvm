//! Internal (low-level) instructions.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Instr {
    // Integer stuff
    IntConst { value: isize },
    IntAdd,
    IntSub,
    IntMul,
    // TODO:
    //IntDiv,
    //IntGt,
    //IntGte,
    //IntLt,
    IntLte,

    // TODO: Different integer sizes

    // Stack manipulation stuff
    //Push,
    //Pop,
    Peek { offset: usize },
    Drop { size: usize },

    // Block stuff
    //MkBlock { size: u8 },
    //GetField { index: u8 },

    // Reference
    //MkRef,
    //GetRef,
    //SetRef,

    // Jump stuff
    Jmp { offset: isize },
    JmpZ { offset: isize },
    //JmpNZ { target: usize },

    // Function calling
    CallDirect { target: usize },
    //CallIndirect { target: usize, args: u8 },
    Ret,
}
