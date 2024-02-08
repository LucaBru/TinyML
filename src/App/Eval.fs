(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

// evaluator
//

let rec eval_expr (venv: value env) (e: expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x -> lookup venv x

    | Lambda(x, _, e) -> Closure(venv, x, e)

    | App(e1, e2) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2

        match v1 with
        | Closure(venv', x, e) ->
            let venv' = (x, v2) :: venv'
            eval_expr venv' e

        | _ -> unexpected_error "non-closure on left hand of application"

    | IfThenElse(guard_expr, true_branch_expr, _) when eval_expr venv guard_expr = VLit(LBool true) ->
        eval_expr venv true_branch_expr

    | IfThenElse(guard_expr, _, Some false_branch_expr) when eval_expr venv guard_expr = VLit(LBool false) ->
        eval_expr venv false_branch_expr

    | BinOp(e1, "+", e2) -> math_op (+) (+) venv e1 e2
    | BinOp(e1, "-", e2) -> math_op (-) (-) venv e1 e2
    | BinOp(e1, "*", e2) -> math_op (*) (*) venv e1 e2
    | BinOp(e1, "/", e2) -> math_op (/) (/) venv e1 e2
    | BinOp(e1, "%", e2) -> math_op (%) (%) venv e1 e2
    | BinOp(e1, ">", e2) -> numerical_bool_op (>) (>) venv e1 e2
    | BinOp(e1, ">=", e2) -> numerical_bool_op (>=) (>=) venv e1 e2
    | BinOp(e1, "<", e2) -> numerical_bool_op (<) (<) venv e1 e2
    | BinOp(e1, "<=", e2) -> numerical_bool_op (<=) (<=) venv e1 e2
    | BinOp(e1, "=", e2) -> numerical_equal (=) venv e1 e2
    | BinOp(e1, "<>", e2) -> numerical_equal (<>) venv e1 e2
    | BinOp(e1, "and", e2) -> bool_op (&&) venv e1 e2
    | BinOp(e1, "or", e2) -> bool_op (||) venv e1 e2
    
    | UnOp("not", e) -> un_op_not (not) venv e
    | UnOp("-", e) -> minus_op venv e

    | Tuple expressions -> VTuple(expressions |> List.map (fun expr -> eval_expr venv expr))

    | Let(var_name, _, value_expr, in_expr) ->
        let v1 = eval_expr venv value_expr
        eval_expr ((var_name, v1) :: venv) in_expr

    | LetRec(name, _, Lambda(lambda_param, _, lambda_body), in_expr) ->
        eval_expr ((name, RecClosure(venv, name, lambda_param, lambda_body)) :: venv) in_expr

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and math_op op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2

    match v1, v2 with
    | VLit(LString x), VLit(LString y) -> VLit(LString(x + y))
    | VLit(LInt x), VLit(LInt y) -> VLit(LInt(op_int x y))
    | VLit(LFloat x), VLit(LFloat y) -> VLit(LFloat(op_float x y))
    | VLit(LInt x), VLit(LFloat y) -> VLit(LFloat(op_float (float x) y))
    | VLit(LFloat x), VLit(LInt y) -> VLit(LFloat(op_float x (float y)))
    | _ ->
        unexpected_error
            "eval_expr: illegal operands in binary operator (+): %s + %s"
            (pretty_value v1)
            (pretty_value v2)

and numerical_bool_op op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2

    match v1, v2 with
    | VLit(LInt x), VLit(LInt y) -> VLit(LBool(op_int x y))
    | VLit(LFloat x), VLit(LFloat y) -> VLit(LBool(op_float x y))
    | VLit(LInt x), VLit(LFloat y) -> VLit(LBool(op_float (float x) y))
    | VLit(LFloat x), VLit(LInt y) -> VLit(LBool(op_float x (float y)))
    | _ -> unexpected_error $"eval_expr: illegal operands in binary operator (+): {pretty_value v1} + {pretty_value v2}"

and numerical_equal op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2

    match v1, v2 with
    | VLit(LInt x), VLit(LInt y) -> VLit(LBool(op x y))
    | _ -> unexpected_error $"eval_expr: The =/<> operator works only on int"

and bool_op op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2

    match v1, v2 with
    | VLit(LBool x), VLit(LBool y) -> VLit(LBool(op x y))
    | _ -> unexpected_error $"eval_expr: The and/or operator works only on bool"

and un_op_not op env e =
    let v = eval_expr env e

    match v with
    | VLit(LBool x) -> VLit(LBool(op x))
    | _ -> unexpected_error "eval_expr: The not operator works only on bool"

and minus_op env e =
    let v = eval_expr env e

    match v with
    | VLit(LInt x) -> VLit(LInt(-x))
    | VLit(LFloat x) -> VLit(LFloat(-x))
    | _ -> unexpected_error "eval_expr: The minus operator works only on int and float"
