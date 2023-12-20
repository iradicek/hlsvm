//! Virtual machine module is the main entry-point to the library and used to manage
//! most of other resources.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ctx::Ctx;
use crate::expect_none;
use crate::fnc::{Fnc, Op, Param, Type};
use crate::instr::Instr;
use crate::symbol::{Symbol, SymbolTable};
use crate::value::Value;

/// Virtual machine is used to manage resources, type-check and run functions.
pub struct Vm {
    code: Vec<Instr>,
    stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    symbols: Rc<RefCell<SymbolTable>>,
    fncs: HashMap<usize, (Box<[Param]>, Type, usize)>,
}

/// A call frame during runtime.
#[derive(Debug, Clone, Copy)]
struct CallFrame {
    /// Target for the return instruction.
    pub target: usize,
}

/// Errors that can happen during virtual machine operation.
#[derive(Debug, Clone)]
pub enum VmError {
    /// Attempt to define a function with name that already exists.
    FunctionAlreadyExists { name: String },
    /// Attempt to reference function with name that does not exist.
    UnknownFunction { name: String },
    /// Attempt to reference a symbol (e.g., a variable name) that does not exist.
    UnknownSymbol { name: String },
    /// Invalid number of arguments to a function.
    InvalidArgsNum { expected: usize, got: usize },
    /// Invalid type of argument to a function.
    InvalidArgType { index: usize, expected: Type },
    /// Mismatched type in a function body.
    MismatchedType { expected: Type, actual: Type },
    /// Invalid stack operation (e.g., attempt to pop on empty stack).
    InvalidStack,
}

impl Vm {
    /// Creates a frsh virtual machine (with no functions defined).
    pub fn new() -> Self {
        let code = Vec::new();
        let stack = Vec::new();
        let call_stack = Vec::new();
        let symbols = Rc::new(RefCell::new(SymbolTable::new()));
        let fncs = HashMap::new();
        Self {
            code,
            stack,
            call_stack,
            symbols,
            fncs,
        }
    }

    /// Creates a symbol object from a (string) name.
    pub fn get_symbol(&self, name: &str) -> Symbol {
        let idx = self.symbols.borrow_mut().symbol_from_string(name);
        let table = Rc::clone(&self.symbols);
        Symbol::new(table, idx)
    }

    /// Add a new function to the virtual machine. The name has to be distinct from
    /// other function names that are already defined.
    pub fn add_fnc(&mut self, name: Symbol, fnc: Fnc) -> Result<(), VmError> {
        match self.fncs.get(&name.index()) {
            Some(_) => Err(VmError::FunctionAlreadyExists {
                name: String::from(&name),
            }),
            None => {
                let num_args = fnc.params().len();
                let params = fnc.params().to_vec().into_boxed_slice();
                expect_none(
                    self.fncs
                        .insert(name.index(), (params, fnc.ret().clone(), self.code.len())),
                );

                let mut ctx = Ctx::new();
                for p in fnc.params().iter() {
                    ctx = ctx.add_symbol(&p.name, &p.ty)
                }
                let mut code = Vec::new();
                self.lower_ops(&mut code, fnc.ops(), ctx, fnc.ret(), num_args)?;
                self.code.append(&mut code);
                self.code.push(Instr::Ret);
                Ok(())
            }
        }
    }

    /// Runs a defined function (denoted by the name) with arguments. Returns result from running
    /// the function or error.
    pub fn run_fnc(&mut self, name: Symbol, args: Box<[Value]>) -> Result<Value, VmError> {
        let pc = match self.fncs.get(&name.index()) {
            Some((params, _ret, pc)) => {
                let num_params = params.len();
                let num_args = args.len();
                if num_params != num_args {
                    return Err(VmError::InvalidArgsNum {
                        expected: num_params,
                        got: num_args,
                    });
                }
                for (i, (p, v)) in params.iter().zip(args.iter()).enumerate() {
                    if !type_check_value(v, &p.ty) {
                        return Err(VmError::InvalidArgType {
                            index: i,
                            expected: p.ty.clone(),
                        });
                    }
                }
                Some(*pc)
            }
            None => None,
        };
        match pc {
            Some(pc) => {
                // Note: Akward conversion to Vec, see: https://github.com/rust-lang/rust/issues/59878
                for arg in args.into_vec() {
                    self.push(arg)
                }
                Ok(self.run_from(pc))
            }
            None => Err(VmError::UnknownFunction {
                name: String::from(&name),
            }),
        }
    }

    /// Pops (any) value from a runtime stack.
    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    /// Peeks (any) value at some offset from a runtime stack.
    fn peek(&mut self, offset: usize) -> Value {
        let idx = self.stack.len() - offset - 1;
        self.stack.get(idx).unwrap().clone()
    }

    /// Pops an integer value from a runtime stack. If top value is not
    /// an integer the machine will panic.
    fn pop_int(&mut self) -> isize {
        match self.pop() {
            Value::Int { value } => value,
            _ => panic!("Value not an int"),
        }
    }

    /// Pushes a new value on a runtime stack.
    fn push(&mut self, value: Value) {
        self.stack.push(value)
    }

    /// Pushes an integer value on a runtime stack.
    fn push_int(&mut self, value: isize) {
        self.push(Value::Int { value })
    }

    /// Runs code on the machine (given the current state of stack, ...) starting from some program counter.
    fn run_from(&mut self, pc: usize) -> Value {
        let mut pc = pc;
        loop {
            // TODO: Should be unchecked, but avoiding unsafe for now
            let instr = self.code.get(pc).unwrap();
            match instr {
                Instr::Peek { offset } => {
                    let v = self.peek(*offset);
                    self.push(v)
                }
                Instr::IntConst { value } => self.push_int(*value),
                Instr::IntAdd => {
                    let v2 = self.pop_int();
                    let v1 = self.pop_int();
                    self.push_int(v1 + v2)
                }
                Instr::IntSub => {
                    let v2 = self.pop_int();
                    let v1 = self.pop_int();
                    self.push_int(v1 - v2)
                }
                Instr::IntMul => {
                    let v2 = self.pop_int();
                    let v1 = self.pop_int();
                    self.push_int(v1 * v2)
                }
                Instr::IntLte => {
                    let v2 = self.pop_int();
                    let v1 = self.pop_int();
                    self.push_int(if v1 <= v2 { 1 } else { 0 });
                }
                Instr::Ret => match self.call_stack.pop() {
                    None => return self.stack.pop().unwrap(),
                    Some(CallFrame { target }) => {
                        pc = target;
                        continue;
                    }
                },
                Instr::CallDirect { target } => {
                    let new_frame = CallFrame { target: pc + 1 };
                    self.call_stack.push(new_frame);
                    pc = *target;
                    continue;
                }
                Instr::JmpZ { offset } => {
                    let offset = *offset;
                    if self.pop_int() == 0 {
                        pc = ((pc as isize) + offset) as usize;
                        continue;
                    }
                }
                Instr::Jmp { offset } => {
                    let offset = *offset;
                    pc = ((pc as isize) + offset) as usize;
                    continue;
                }
                Instr::Drop { size } => {
                    let size = *size;
                    let v = self.pop();
                    for _ in 0..size {
                        self.pop();
                    }
                    self.push(v);
                }
            }

            pc += 1;
        }
    }

    /// Lowers a sequence of high-level operations into lower-level instructions. The code is emmited into
    /// the vector `code`. `ctx` represents current (static) knowledge of the stack, `expected_type` is the type
    /// that the last expression in the sequence should have, and `args_to_clean` is a number of stack values
    /// that need to be cleaned (dropped) at the end (most likely representing arguments passed to the function
    /// that need to be cleaned up before return).
    fn lower_ops(
        &self,
        code: &mut Vec<Instr>,
        ops: &[Op],
        ctx: Ctx,
        expected_type: &Type,
        args_to_clean: usize,
    ) -> Result<(), VmError> {
        let mut ctx = ctx;
        let mut stack_types = Vec::new();

        for op in ops {
            match op {
                // Local variable (already located somewhere on the stack) is peek-ed
                // on the top of the stack.
                Op::Local { sym } => match ctx.get_symbol(sym) {
                    None => return Err(VmError::UnknownSymbol { name: sym.into() }),
                    Some((stack_loc, ty)) => {
                        code.push(Instr::Peek { offset: stack_loc });
                        ctx = push_stack(&mut stack_types, ctx, ty)
                    }
                },
                // Constant has a mathing low-level instruction
                Op::IntConst { value } => {
                    code.push(Instr::IntConst { value: *value });
                    ctx = push_stack(&mut stack_types, ctx, &Type::Int)
                }
                // All binary operations also have a low-level matching instruction,
                // but we additionally check argument types and push result type to stack.
                Op::IntAdd => {
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    code.push(Instr::IntAdd);
                    ctx = push_stack(&mut stack_types, ctx, &Type::Int)
                }
                Op::IntSub => {
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    code.push(Instr::IntSub);
                    ctx = push_stack(&mut stack_types, ctx, &Type::Int)
                }
                Op::IntMul => {
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    code.push(Instr::IntMul);
                    ctx = push_stack(&mut stack_types, ctx, &Type::Int)
                }
                Op::IntLeq => {
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Int)?;
                    code.push(Instr::IntLte);
                    ctx = push_stack(&mut stack_types, ctx, &Type::Bool)
                }
                // If-then-else does not have a matching low-level instructions. Rather we
                // emit then and else blocks separately and connect everything with
                // appropriate jumps.
                Op::Ite { ty, bthen, belse } => {
                    // We expect a boolean conditional on the top of the stack
                    ctx = pop_stack(&mut stack_types, ctx, &Type::Bool)?;

                    // Generate code for blocks (both need to be of the same type)
                    let mut then_code = Vec::new();
                    self.lower_ops(&mut then_code, bthen, ctx.clone(), ty, 0)?;
                    let mut else_code = Vec::new();
                    self.lower_ops(&mut else_code, belse, ctx.clone(), ty, 0)?;

                    // Compute jump offsets
                    let else_offset = then_code.len() + 2;
                    let end_offset = else_code.len() + 1;

                    // Jump to else on condition being false
                    code.push(Instr::JmpZ {
                        offset: else_offset as isize,
                    });
                    // Otherwise fallthrough to then branch
                    code.append(&mut then_code);
                    // At the end of then branch jump to end
                    code.push(Instr::Jmp {
                        offset: end_offset as isize,
                    });
                    // Else automatically falls through to end
                    code.append(&mut else_code);

                    ctx = push_stack(&mut stack_types, ctx, ty);
                }
                // Call is direcly mapped to low-level instruction. We just additionally check
                // type of the arguments.
                Op::Call { name } => match self.fncs.get(&name.index()) {
                    None => {
                        return Err(VmError::UnknownFunction {
                            name: name.to_string(),
                        })
                    }
                    Some((params, ret, ptr)) => {
                        for p in params.iter() {
                            ctx = pop_stack(&mut stack_types, ctx, &p.ty)?;
                        }
                        code.push(Instr::CallDirect { target: *ptr });
                        ctx = push_stack(&mut stack_types, ctx, ret)
                    }
                },
            }
        }

        let _ = pop_stack(&mut stack_types, ctx, expected_type)?;
        let stack_to_clean = stack_types.len() + args_to_clean;
        if stack_to_clean > 0 {
            code.push(Instr::Drop {
                size: stack_to_clean,
            })
        }

        Ok(())
    }
}

impl Default for Vm {
    fn default() -> Self {
        Self::new()
    }
}

/// Pushes a new value (actually type of a value) onto (static) stack.
fn push_stack<'a, 'b>(types: &mut Vec<&'b Type>, ctx: Ctx<'a>, ty: &'b Type) -> Ctx<'a> {
    types.push(ty);
    ctx.add_value()
}

/// Pops a value (actually type of a value) from (static) stack. Also checks that the
/// value is of an expected type.
fn pop_stack<'a>(
    types: &mut Vec<&Type>,
    ctx: Ctx<'a>,
    expected_type: &Type,
) -> Result<Ctx<'a>, VmError> {
    match types.pop() {
        None => Err(VmError::InvalidStack),
        Some(ty) => {
            check_type(expected_type, ty)?;
            Ok(ctx.drop_value())
        }
    }
}

/// Checks weether two types match. Returns appropriate error in case they do not match.
fn check_type(expected: &Type, actual: &Type) -> Result<(), VmError> {
    if expected == actual {
        Ok(())
    } else {
        Err(VmError::MismatchedType {
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }
}

/// Checks that a (runtime) value is of a certain type.
fn type_check_value(value: &Value, ty: &Type) -> bool {
    match value {
        Value::Int { value: _ } => *ty == Type::Int,
        Value::Block { elts } => {
            if let Type::Tuple { elts: t_elts } = ty {
                if elts.len() == t_elts.len() {
                    elts.iter()
                        .zip(t_elts.iter())
                        .all(|(v, t)| type_check_value(v, t))
                } else {
                    false
                }
            } else {
                false
            }
        }
    }
}
