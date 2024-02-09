(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let mutable private c = 0

let fresh_typevar () =
    let id = c
    c <- c + 1
    TyVar id

// to use in the tests
let reset_typevar_counter () = c <- 0

let set_typevar_count value = c <- value

let rec is_typevar_into_type type_var t =
    let rec is_inner = is_typevar_into_type type_var

    match t with
    | TyVar name when type_var = name -> true
    | TyArrow(t1, t2) -> is_inner t1 || is_inner t2
    | TyTuple types_list -> List.exists (fun tuple_t -> is_inner tuple_t) types_list
    | _ -> false

let rec apply_subst t subst =
    match t with
    | TyName _ -> t
    | TyVar type_var ->
        try
            subst
            |> List.find (fun (in_subst_type_var, _) -> type_var = in_subst_type_var)
            |> snd
        with :? System.Collections.Generic.KeyNotFoundException ->
            t

    | TyArrow(t1, t2) -> TyArrow(apply_subst t1 subst, apply_subst t2 subst)
    | TyTuple types -> TyTuple(List.map (fun in_tuple_type -> apply_subst in_tuple_type subst) types)

let apply_subst_scheme (Forall(pol_vars, t)) (subst: subst) =
    let theta' =
        List.filter (fun (type_var, t) -> pol_vars |> Set.contains type_var |> not) subst

    Forall(pol_vars, apply_subst t theta')

let apply_subst_env env subst =
    env |> List.map (fun (var, scheme) -> (var, apply_subst_scheme scheme subst))

//into the substitution you have the same type variable maps from different types (which can't be unified by a substitutions)
let conflict_in_subst subst =
    List.tryFind
        (fun ((type_var1, t1), (type_var2, t2)) -> type_var1 = type_var2 && t1 <> t2)
        (List.allPairs subst subst)

//into the substitution there exists a map from ai -> ti s.t ai is into ti
let circularity_in_subst subst =
    List.tryFind (fun (type_var, t) -> is_typevar_into_type type_var t) subst

let compose_subst subst1 subst2 =
    // application of the first one to the codomain of the second one
    let composed_subst =
        (List.map (fun (type_var, t) -> (type_var, apply_subst t subst1)) subst2)
        @ subst1
        |> List.distinct

    //search for conflicts
    let conflicts = conflict_in_subst composed_subst

    match conflicts with
    | Some((conflict_type_var, t1), (_, t2)) ->
        raise (
            type_error
                $"compose substitution error: conflict type variable {pretty_ty (TyVar conflict_type_var)} maps to type {t1} and {t2}"
        )
    | _ -> ()

    //search for circularity
    let circularity = circularity_in_subst composed_subst

    match circularity with
    | Some(circular_type_var, t) ->
        raise (type_error $"compose substitution error: circular type variable {circular_type_var} maps to type {t}")
    | _ -> ()

    composed_subst

let ($) = compose_subst

let rec unify t1 t2 =
    match t1, t2 with
    | TyName c1, TyName c2 when c1 = c2 -> []
    | _, TyVar type_var -> [ (type_var, t1) ]
    | TyVar type_var, _ -> [ (type_var, t2) ]
    | TyArrow(t1, t2), TyArrow(t3, t4) -> (unify t1 t3) $ (unify t2 t4)
    | TyTuple tuple1, TyTuple tuple2 when tuple1.Length = tuple2.Length ->
        List.fold
            (fun subst_composition (type_in_tuple1, type_in_tuple2) ->
                subst_composition $ unify type_in_tuple1 type_in_tuple2)
            []
            (List.zip tuple1 tuple2)

    | _ -> raise (type_error $"unification error: {t1} is incompatible with {t2}")

let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyVar type_var -> Set.singleton type_var
    | TyArrow(t1, t2) -> freevars_ty t1 + freevars_ty t2
    | TyTuple type_list -> List.fold (fun acc t -> acc + freevars_ty t) Set.empty type_list

let freevars_scheme (Forall(tvs, t)) = freevars_ty t - tvs

let rec freevars_scheme_env env =
    List.fold (fun acc (_, type_scheme) -> acc + freevars_scheme type_scheme) Set.empty env

let rec inst (Forall(free_vars: Set<tyvar>, t)) =
    let polymorphic_vars_subst =
        free_vars
        |> Set.toList
        |> List.map (fun polymorphic_var -> (polymorphic_var, fresh_typevar ()))

    apply_subst t polymorphic_vars_subst

let gen env t =
    Forall(freevars_ty t - freevars_scheme_env env, t)

(*
    language's operators
        note that each operator is followed by a list of compatible types
        the language allows the use of operators on operands of the same types (as F#)
        operators are polymorphic (as F#)
        the order in the list count since the first is inferred if no information on the operands are available (as F#)

        the code is open to accept new operators, you only need to push them into this lists
*)
let math_binary_operators =
    [ ("+", [ TyInt; TyFloat; TyChar; TyString ])
      ("-", [ TyInt; TyFloat ])
      ("*", [ TyInt; TyFloat ])
      ("/", [ TyInt; TyFloat ])
      ("%", [ TyInt; TyFloat ]) ]

let comparison_binary_operators =
    [ ("<", [ TyInt; TyFloat ])
      ("<=", [ TyInt; TyFloat ])
      (">", [ TyInt; TyFloat ])
      (">=", [ TyInt; TyFloat ])
      ("<>", [ TyInt; TyFloat; TyChar; TyString; TyBool ])
      ("=", [ TyInt; TyFloat; TyChar; TyString; TyBool ])
      ("and", [ TyBool ])
      ("or", [ TyBool ]) ]

let unary_operators = [ ("not", [ TyBool ]); ("-", [ TyInt; TyFloat ]) ]

let binary_operators = math_binary_operators @ comparison_binary_operators

let (|MathOperator|ComparisonOperator|) op =
    if List.exists (fun (o, _) -> o = op) math_binary_operators then
        MathOperator
    else
        ComparisonOperator

let rec typeinfer_expr (env: scheme env) (e: expr) : ty * subst =
    match e with
    | Lit(LInt _) -> TyInt, []
    | Lit(LBool _) -> TyBool, []
    | Lit(LFloat _) -> TyFloat, []
    | Lit(LString _) -> TyString, []
    | Lit(LChar _) -> TyChar, []
    | Lit LUnit -> TyUnit, []

    | Var var_name ->
        try
            let s = lookup env var_name
            let t = inst s
            t, []
        with :? System.Collections.Generic.KeyNotFoundException ->
            raise (type_error $"type inference: variable '{var_name}' not found in the environment")

    | Lambda(param, type_annotation, body) ->
        let param_type = fresh_typevar ()

        //why the type_annotation_subst is necessary? And why already here? Take as example => fun (x:float) -> x + y
        let type_annotation_subst =
            match type_annotation with
            | None -> []
            | Some t -> unify param_type t

        let env_within_param =
            (param, Forall(Set.empty, apply_subst param_type type_annotation_subst)) :: env

        let t2, subst1 = typeinfer_expr env_within_param body

        let theta = subst1 $ type_annotation_subst
        let t1 = apply_subst param_type theta

        apply_subst (TyArrow(t1, t2)) theta, theta

    | App(left_expr, right_expr) ->
        let t1, subst1 = typeinfer_expr env left_expr
        let t2, subst2 = typeinfer_expr (apply_subst_env env subst1) right_expr
        let application_type = fresh_typevar ()
        let subst3 = unify t1 (TyArrow(t2, application_type))
        let t = apply_subst application_type subst3
        t, subst3 $ subst2

    | IfThenElse(e1, e2, Some e3) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool
        let t2, s3 = typeinfer_expr env e2
        let t3, s4 = typeinfer_expr env e3
        let s5 = unify t2 t3
        let s = s5 $ s4 $ s3 $ s2 $ s1
        apply_subst t2 s, s

    | Tuple expressions ->
        let mutable previous_subst = []

        let tuple_types =
            expressions
            |> List.map (fun expr ->
                let inferred_type, previous_subst =
                    typeinfer_expr (apply_subst_env env previous_subst) expr

                inferred_type)

        TyTuple tuple_types, previous_subst

    | BinOp(left_expr, op, right_expr) ->
        let left_type, subst1 = typeinfer_expr env left_expr
        let right_type, subst2 = typeinfer_expr env right_expr

        //requires that the two operand can became the same type
        let same_operand_subst = unify left_type right_type

        let operation_type = apply_subst left_type (same_operand_subst $ subst2 $ subst1)

        try
            let _, operands_types_allowed = binary_operators |> List.find (fun (o, _) -> op = o)

            let theta =
                (match operation_type with
                 | TyVar _ ->
                     (*
                        in this case both operators' types are type variable so i need to force them to be specific type
                        otherwise i can apply an operator to types that don't support it
                     *)
                     let forced_type = operands_types_allowed |> List.head
                     unify operation_type forced_type

                 | _ ->
                     (*
                        in this case at least one of the two is a type different from TyVar so i require
                        that it is one of the ones recognized from the operator, if not an exception is throws
                     *)
                     operands_types_allowed
                     |> List.find (fun allowed_type -> allowed_type = operation_type)
                     |> ignore

                     [])
                $ same_operand_subst
                $ subst2
                $ subst1

            match op with
            | MathOperator -> operation_type, theta
            | ComparisonOperator -> TyBool, theta

        with :? System.Collections.Generic.KeyNotFoundException ->
            raise (type_error $"type inference: the operator {op} is not defined for type {operation_type}")

    | UnOp(op, expr) ->
        let expr_type, subst = typeinfer_expr env expr

        printfn $"operator {op} => expression type: {expr_type}"

        try
            (* same behaviour of the lambda*)
            match expr_type with
            | TyVar _ ->
                let forced_type =
                    List.find (fun (o, _) -> o = op) unary_operators |> snd |> List.head

                let type_annotation_subst = unify expr_type forced_type
                let theta = type_annotation_subst $ subst
                apply_subst forced_type theta, theta

            | _ ->
                List.find (fun (o, _) -> o = op) unary_operators
                |> snd
                |> List.find (fun acceptable_ty -> acceptable_ty = expr_type)
                |> ignore

                apply_subst expr_type subst, subst
        with :? System.Collections.Generic.KeyNotFoundException ->
            raise (type_error $"type inference: unary operator {op} not defined for type {expr_type}")

    | Let(var_name, type_annotation, value_expr, in_expr) ->
        let t1, subst1 = typeinfer_expr env value_expr

        let type_annotation_subst =
            match type_annotation with
            | None -> []
            | Some t -> unify t1 t

        let subst1_env = apply_subst_env env (subst1 $ type_annotation_subst)
        let sigma1 = gen subst1_env t1
        let t2, subst2 = typeinfer_expr ((var_name, sigma1) :: subst1_env) in_expr
        let theta = type_annotation_subst $ subst2 $ subst1
        apply_subst t2 theta, theta

    | LetRec(lambda_name, type_annotation, (Lambda(_, _, _) as lambda), in_expression) ->
        let lambda_type = fresh_typevar ()

        let t1, subst1 =
            typeinfer_expr ((lambda_name, Forall(Set.empty, lambda_type)) :: env) lambda

        let type_annotation_subst =
            match type_annotation with
            | None -> []
            | Some t -> unify t1 t

        let env1 = apply_subst_env env (subst1 $ type_annotation_subst)
        let t2, subst2 = typeinfer_expr ((lambda_name, gen env1 t1) :: env1) in_expression
        let subst3 = unify lambda_type (apply_subst t1 subst1)
        let theta = type_annotation_subst $ subst3 $ subst2 $ subst1
        apply_subst t2 theta, theta

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

// type checker
//
// optionally, a simple type checker (without type inference) could be implemented
// you might start implementing this for simplicity and eventually write the type inference once you gain familiarity with the code

let rec typecheck_expr (env: ty env) (e: expr) : ty =
    match e with
    | Lit(LInt _) -> TyInt
    | Lit(LFloat _) -> TyFloat
    | Lit(LString _) -> TyString
    | Lit(LChar _) -> TyChar
    | Lit(LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x -> lookup env x

    | Let(x, None, e1, e2) ->
        let t1 = typecheck_expr env e1
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Let(x, Some t, e1, e2) ->
        let t1 = typecheck_expr env e1

        if t <> t1 then
            type_error "type %O differs from type %O in let-binding" t1 t

        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Lambda(x, Some t, e) ->
        let env' = (x, t) :: env
        let te = typecheck_expr env' e
        TyArrow(t, te)

    | Lambda(x, None, e) -> type_error "unannotated lambdas are not supported by the type checker"

    | App(e1, e2) ->
        let t2 = typecheck_expr env e2

        match typecheck_expr env e1 with
        | TyArrow(ta, tb) ->
            if ta <> t2 then
                type_error "argument has type %O while function parameter has type %O in application" t2 ta

            tb
        | t1 -> type_error "left hand of application is not an arrow type: %O" t1

    //TODO implement if e1 then e2
    | IfThenElse(e1, e2, Some e3) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyBool then
            type_error "bool expected in if guard, but got %O" t1

        let t2 = typecheck_expr env e2
        let t3 = typecheck_expr env e3

        if t2 <> t3 then
            type_error "then and else branches have different types: %O and %O" t2 t3

        t2

    | IfThenElse(condition, expression, None) ->
        let t1 = typecheck_expr env condition

        if t1 <> TyBool then
            type_error "bool expected in if guard, but got %O" t1

        typecheck_expr env expression


    //TODO missing &&, ||, <>, %
    | BinOp(e1, ("+" | "-" | "*" | "/" as op), e2) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyInt then
            type_error "left hand of (%s) operator is not an int: %O" op t1

        let t2 = typecheck_expr env e2

        if t2 <> TyInt then
            type_error "right hand of (%s) operator is not an int: %O" op t2

        TyInt

    //TODO missing minus
    | UnOp("not", e) ->
        let t = typecheck_expr env e

        if t <> TyBool then
            type_error "operand of not-operator is not a bool: %O" t

        TyBool

    | BinOp(e1, "=", e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        if t1 <> t2 then
            type_error "left and right hands of equality operator are different: %O and %O" t1 t2

        TyBool

    | BinOp(e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyInt then
            type_error "left hand of (%s) operator is not an int: %O" op t1

        let t2 = typecheck_expr env e2

        if t2 <> TyInt then
            type_error "right hand of (%s) operator is not an int: %O" op t2

        TyBool

    | Tuple es -> TyTuple(List.map (typecheck_expr env) es)


    // TODO optionally complete this implementation

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
