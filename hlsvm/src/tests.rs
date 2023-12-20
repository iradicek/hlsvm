use crate::{
    fnc::{Fnc, Op, Param, Type},
    value::Value,
    vm::{Vm, VmError},
};

#[test]
pub fn test_add() -> Result<(), VmError> {
    let mut vm = Vm::new();
    let params = Box::new([
        Param {
            name: vm.get_symbol("x"),
            ty: Type::Int,
        },
        Param {
            name: vm.get_symbol("y"),
            ty: Type::Int,
        },
    ]);
    let body = Box::new([
        Op::Local {
            sym: vm.get_symbol("x"),
        },
        Op::Local {
            sym: vm.get_symbol("y"),
        },
        Op::IntAdd,
    ]);
    let fnc = Fnc::new(params, Type::Int, body);
    let add = vm.get_symbol("add");
    vm.add_fnc(add.clone(), fnc)?;
    let args = Box::new([Value::Int { value: 35 }, Value::Int { value: 7 }]);
    let res = vm.run_fnc(add, args)?;
    assert_eq!(res, Value::Int { value: 42 });
    Ok(())
}

#[test]
pub fn test_fact() -> Result<(), VmError> {
    let mut vm = Vm::new();
    let params = Box::new([Param {
        name: vm.get_symbol("n"),
        ty: Type::Int,
    }]);
    let fact = vm.get_symbol("fact");
    let body = Box::new([
        Op::Local {
            sym: vm.get_symbol("n"),
        },
        Op::IntConst { value: 1 },
        Op::IntLeq,
        Op::Ite {
            ty: Type::Int,
            bthen: Box::new([Op::IntConst { value: 1 }]),
            belse: Box::new([
                Op::Local {
                    sym: vm.get_symbol("n"),
                },
                Op::IntConst { value: 1 },
                Op::IntSub,
                Op::Call { name: fact.clone() },
                Op::Local {
                    sym: vm.get_symbol("n"),
                },
                Op::IntMul,
            ]),
        },
    ]);
    let fnc = Fnc::new(params, Type::Int, body);
    vm.add_fnc(fact.clone(), fnc)?;
    let args = Box::new([Value::Int { value: 5 }]);
    let res = vm.run_fnc(fact, args)?;
    assert_eq!(res, Value::Int { value: 120 });
    Ok(())
}
