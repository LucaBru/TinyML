(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

exception CompositionError of string

exception UnificationError of string

exception EnvironmentError of string

type subst = (tyvar * ty) list

let mutable c = 0

let fresh_typevar =
    let id = c
    c <- c + 1
    id

let reset_typevar_counter = c <- 0

let rec is_typevar_into_type type_var t =
    let rec is_inner = is_typevar_into_type type_var

    match t with
    | TyVar name when type_var = name -> true
    | TyArrow(t1, t2) -> is_inner t1 || is_inner t2
    | TyTuple(head :: tail) -> is_inner head || is_inner (TyTuple tail)
    | _ -> false

// TODO implement this
let compose_subst (s1: subst) (s2: subst) : subst =

    let exists_conflict_subst =
        List.allPairs s1 s2
        |> List.filter (fun (sub1, sub2) -> fst sub1 = fst sub2 && snd sub1 <> snd sub2)
        |> List.isEmpty
        |> not

    if exists_conflict_subst then
        raise (CompositionError "Error while compose substitutions, domains are not disjoint")

    let substitutions = List.distinct s1 @ s2

    let exists_circularity =
        List.allPairs (List.map fst substitutions) (List.map snd substitutions)
        |> List.exists (fun (type_var, t) -> is_typevar_into_type type_var t)

    if exists_circularity then
        raise (CompositionError "Error while compose substitutions, found circularity")

    substitutions

let ($) = compose_subst

// TODO implement this
let rec unify (t1: ty) (t2: ty) : subst =
    match t1, t2 with
    | TyName c1, TyName c2 when c1 = c2 -> []
    | TyVar type_var, t
    | t, TyVar type_var -> (type_var, t) :: []
    | TyArrow(t1, t2), TyArrow(t3, t4) -> (unify t1 t3) $ (unify t2 t4)
    | TyTuple(t1 :: tail), TyTuple(t1' :: tail') -> (unify t1 t1') $ (unify (TyTuple tail) (TyTuple tail'))
    | _ -> raise (UnificationError "Error while unify, some types are incoherent each other")

// TODO implement this
let rec apply_subst (t: ty) (s: subst) : ty =
    match t with
    | TyName constant_type -> TyName constant_type
    | TyVar type_var ->
        let t = List.tryFind (fun elm -> fst elm = type_var) s

        match t with
        | Some s -> snd s
        | None -> TyVar type_var
    | TyArrow(t1, t2) -> TyArrow(apply_subst t1 s, apply_subst t2 s)
    | TyTuple l -> TyTuple(l |> List.map (fun elm -> apply_subst elm s))

let apply_subst_scheme (scheme: scheme) (s: subst) =
    match scheme with
    | Forall(pol_vars, t) ->
        let is_typevar_polymorphic type_var =
            pol_vars |> Set.exists (fun var -> type_var = var)

        let theta' =
            s |> List.filter (fun (type_var, _) -> is_typevar_polymorphic type_var |> not)

        Forall(pol_vars, apply_subst t theta')

let apply_subst_env (env: scheme env) (s: subst) : scheme env =
    env |> List.map (fun (var, scheme) -> (var, apply_subst_scheme scheme s))

// TODO implement this
let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyVar type_var -> Set.empty.Add(type_var)
    | TyArrow(t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyTuple(head :: tail) -> Set.union (freevars_ty head) (freevars_ty (TyTuple tail))
    | TyTuple [] -> Set.empty

// TODO implement this
let freevars_scheme (Forall(tvs, t)) = Set.difference (freevars_ty t) tvs

// TODO implement this
let rec freevars_scheme_env (env: scheme env) =
    match env with
    | head_scheme :: tail -> Set.union (freevars_scheme (snd head_scheme)) (freevars_scheme_env tail)
    | [] -> Set.empty

let rec re (free_vars: Set<tyvar>) t =
    let rec re_inner = re free_vars

    match t with
    | TyName t -> TyName t
    | TyVar type_var when free_vars |> Set.exists (fun elm -> type_var = elm) -> TyVar fresh_typevar
    | TyVar type_var -> TyVar type_var
    | TyArrow(t1, t2) -> TyArrow(re_inner t1, re_inner t2)
    | TyTuple l -> TyTuple(l |> List.map (fun elm -> re_inner elm))

let inst (s: scheme) =
    match s with
    | Forall(pol_vars, t) -> re pol_vars t

let gen (env: scheme env) t =
    let polymorphic_vars = Set.difference (freevars_ty t) (freevars_scheme_env env)
    Forall(polymorphic_vars, t)

// basic environment: add builtin operators at will
//

let gamma0 =
    [ ("+", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("-", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("*", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("/", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("<", TyArrow(TyInt, TyArrow(TyInt, TyBool))) ]

// type inference
//

let rec typeinfer_expr (env: scheme env) (e: expr) : ty * subst =
    match e with
    | Lit(LInt _) -> TyInt, []
    | Lit(LBool _) -> TyBool, []
    | Lit(LFloat _) -> TyFloat, []
    | Lit(LString _) -> TyString, []
    | Lit(LChar _) -> TyChar, []
    | Lit LUnit -> TyUnit, []

    | Var n ->
        try
            let s = lookup env n
            let t = inst s
            (t, [])
        with :? System.Collections.Generic.KeyNotFoundException ->
            raise (EnvironmentError $"Environment error, variable '{n}' not found in the env")

    | Lambda(param, t, e) ->
        let param_type =
            match t with
            | Some p_t -> p_t
            | None -> TyVar fresh_typevar

        let env_within_lambda_param = (param, Forall(Set.empty, param_type)) :: env
        let t2, subst1 = typeinfer_expr env_within_lambda_param e
        let t1 = apply_subst param_type subst1
        (TyArrow(t1, t2), subst1)


    | App(e1, e2) ->
        let t1, subst1 = typeinfer_expr env e1
        let t2, subst2 = typeinfer_expr (apply_subst_env env subst1) e2
        let var = TyVar fresh_typevar
        let subst3 = unify t1 (TyArrow(t2, var))
        let t = apply_subst var subst3
        (t, subst3 $ subst2)

    | IfThenElse(e1, e2, Some e3) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool
        let t2, s3 = typeinfer_expr env e2
        let t3, s4 = typeinfer_expr env e3
        let s5 = unify t2 t3
        let s = s5 $ s4 $ s3 $ s2 $ s1
        apply_subst t2 s, s

    | Tuple l ->
        let mutable previous_subst = []

        let types =
            l
            |> List.mapi (fun index e ->
                let t, previous_subst = typeinfer_expr (apply_subst_env env previous_subst) e
                t)

        (TyTuple types, previous_subst)

    | BinOp(e1, op, e2) -> typeinfer_expr env (App(App(Var op, e1), e2))



    // TODO complete this implementation

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

    | IfThenElse(e1, e2, Some e3) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyBool then
            type_error "bool expected in if guard, but got %O" t1

        let t2 = typecheck_expr env e2
        let t3 = typecheck_expr env e3

        if t2 <> t3 then
            type_error "then and else branches have different types: %O and %O" t2 t3

        t2

    | BinOp(e1, ("+" | "-" | "*" | "/" as op), e2) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyInt then
            type_error "left hand of (%s) operator is not an int: %O" op t1

        let t2 = typecheck_expr env e2

        if t2 <> TyInt then
            type_error "right hand of (%s) operator is not an int: %O" op t2

        TyInt

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
