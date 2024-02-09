(*
* TinyML
* Ast.fs: abstract syntax tree
*)

module TinyML.Ast

open Printf

// errors
//

exception SyntaxError of string * FSharp.Text.Lexing.LexBuffer<char>
exception TypeError of string
exception UnexpectedError of string

let throw_formatted exnf fmt = ksprintf (fun s -> raise (exnf s)) fmt

let unexpected_error fmt = throw_formatted UnexpectedError fmt

// types
//

type tyvar = int

type ty =
    | TyName of string
    | TyArrow of ty * ty
    | TyVar of tyvar
    | TyTuple of ty list

// pseudo data constructors for literal types
let TyFloat = TyName "float"
let TyInt = TyName "int"
let TyChar = TyName "char"
let TyString = TyName "string"
let TyBool = TyName "bool"
let TyUnit = TyName "unit"

type scheme = Forall of tyvar Set * ty

// literals
//

type lit =
    | LInt of int
    | LFloat of float
    | LString of string
    | LChar of char
    | LBool of bool
    | LUnit

let private (|TyLit|_|) name =
    function
    | TyName s when s = name -> Some()
    | _ -> None

// active patterns for literal types
let (|TyFloat|_|) = (|TyLit|_|) "float"
let (|TyInt|_|) = (|TyLit|_|) "int"
let (|TyChar|_|) = (|TyLit|_|) "char"
let (|TyString|_|) = (|TyLit|_|) "string"
let (|TyBool|_|) = (|TyLit|_|) "bool"
let (|TyUnit|_|) = (|TyLit|_|) "unit"

// expressions
//

type binding = bool * string * ty option * expr // (is_recursive, id, optional_type_annotation, expression)

and expr =
    | Lit of lit
    | Lambda of string * ty option * expr
    | App of expr * expr
    | Var of string
    | LetIn of binding * expr
    | IfThenElse of expr * expr * expr option
    | Tuple of expr list
    | BinOp of expr * string * expr
    | UnOp of string * expr

// pseudo constructors for let bindings
let Let (x, tyo, e1, e2) = LetIn((false, x, tyo, e1), e2)
let LetRec (x, tyo, e1, e2) = LetIn((true, x, tyo, e1), e2)

// active patterns for let bindings
let (|Let|_|) =
    function
    | LetIn((false, x, tyo, e1), e2) -> Some(x, tyo, e1, e2)
    | _ -> None

let (|LetRec|_|) =
    function
    | LetIn((true, x, tyo, e1), e2) -> Some(x, tyo, e1, e2)
    | _ -> None

// environment
//

type 'a env = (string * 'a) list

let lookup env (x: string) =
    let _, v = List.find (fun (x', v) -> x = x') env
    v

// values
//

type value =
    | VLit of lit
    | VTuple of value list
    | Closure of value env * string * expr
    | RecClosure of value env * string * string * expr

// others
//

type interactive =
    | IExpr of expr
    | IBinding of binding

// pretty printers
//

// utility function for printing lists by flattening strings with a separator
let rec flatten p sep es =
    match es with
    | [] -> ""
    | [ e ] -> p e
    | e :: es -> sprintf "%s%s %s" (p e) sep (flatten p sep es)

// print pairs within the given env using p as printer for the elements bound within
let pretty_env p env =
    sprintf "[%s]" (flatten (fun (x, o) -> sprintf "%s=%s" x (p o)) ";" env)

// print any tuple given a printer p for its elements
let pretty_tupled p l = flatten p ", " l

let letters = [| 'a' .. 'z' |] |> Array.map (fun c -> c.ToString())

let rec greek_letter (number: int) =
    if number < 26 then
        letters[number]
    else
        greek_letter (number - 26) + letters[number % 26]

let rec type_vars_into_type t =
    match t with
    | TyVar numb -> Set.singleton numb
    | TyArrow(domain, codomain) -> type_vars_into_type domain + type_vars_into_type codomain
    | TyTuple types -> List.fold (fun acc tuple_type -> acc + type_vars_into_type tuple_type) Set.empty types
    | _ -> Set.empty

let pretty_ty t =
    let type_vars =
        type_vars_into_type t
        |> List.ofSeq
        |> List.sort
        |> List.mapi (fun index type_var -> (type_var, greek_letter index))

    let rec inner_pretty_type t =
        match t with
        | TyName s -> s
        | TyArrow(t1, t2) ->
            let domain_str = (inner_pretty_type t1)
            let codomain_str = (inner_pretty_type t2)

            match t1 with
            | TyArrow(_, _) -> sprintf "(%s) -> %s" domain_str codomain_str
            | _ -> sprintf "%s -> %s" domain_str codomain_str
        | TyVar n ->
            let _, greek_letter = List.find (fun (type_var, _) -> type_var = n) type_vars
            $"'{greek_letter}"
        | TyTuple ts -> sprintf "(%s)" (pretty_tupled inner_pretty_type ts)

    inner_pretty_type t

let pretty_lit lit =
    match lit with
    | LInt n -> sprintf "%d" n
    | LFloat n -> sprintf "%g" n
    | LString s -> sprintf "\"%s\"" s
    | LChar c -> sprintf "%c" c
    | LBool true -> "true"
    | LBool false -> "false"
    | LUnit -> "()"

//low to high priority binary operators
let binary_operators_priority =
    [ [ "or" ]
      [ "and" ]
      [ ">"; ">="; "<"; "<="; "="; "<>" ]
      [ "+"; "-" ]
      [ "*"; "/"; "%" ] ]

let rec pretty_expr e =
    match e with
    | Lit lit -> pretty_lit lit

    | Lambda(x, None, e) -> sprintf "fun %s -> %s" x (pretty_expr e)
    | Lambda(x, Some t, e) -> sprintf "fun (%s : %s) -> %s" x (pretty_ty t) (pretty_expr e)

    | App(e1, e2) ->
        match e2 with
        | UnOp _
        | App _ -> sprintf "%s (%s)" (pretty_expr e1) (pretty_expr e2)
        | _ -> sprintf "%s %s" (pretty_expr e1) (pretty_expr e2)

    | Var x -> x

    | Let(x, None, e1, e2) -> sprintf "let %s = %s in %s" x (pretty_expr e1) (pretty_expr e2)

    | Let(x, Some t, e1, e2) -> sprintf "let %s : %s = %s in %s" x (pretty_ty t) (pretty_expr e1) (pretty_expr e2)

    | LetRec(x, None, e1, e2) -> sprintf "let rec %s = %s in %s" x (pretty_expr e1) (pretty_expr e2)

    | LetRec(x, Some tx, e1, e2) ->
        sprintf "let rec %s : %s = %s in %s" x (pretty_ty tx) (pretty_expr e1) (pretty_expr e2)

    | IfThenElse(e1, e2, e3o) ->
        let s = sprintf "if %s then %s" (pretty_expr e1) (pretty_expr e2)

        match e3o with
        | None -> s
        | Some e3 -> sprintf "%s else %s" s (pretty_expr e3)

    | Tuple es -> sprintf "(%s)" (pretty_tupled pretty_expr es)

    | BinOp(e1, op, e2) ->
        let operator_priority =
            List.findIndex (fun op_list -> List.contains op op_list) binary_operators_priority

        let expr_string expr =
            match expr with
            | App _
            | UnOp _ -> sprintf "(%s)" (pretty_expr expr)
            | BinOp(_, nested_expr_op, _) ->
                let nested_operator_priority =
                    List.findIndex (fun op_list -> List.contains nested_expr_op op_list) binary_operators_priority

                if nested_operator_priority < operator_priority then
                    sprintf "(%s)" (pretty_expr expr)
                else
                    sprintf "%s" (pretty_expr expr)
            | _ -> sprintf "%s" (pretty_expr expr)

        sprintf "%s %s %s" (expr_string e1) op (expr_string e2)

    | UnOp(op, e) ->
        match op, e with
        | ("not", UnOp("-", _)) -> sprintf "%s (%s)" op (pretty_expr e)
        | _ -> sprintf "%s %s" op (pretty_expr e)

    | _ -> unexpected_error "pretty_expr: %s" (pretty_expr e)

let rec pretty_value v =
    match v with
    | VLit lit -> pretty_lit lit

    | VTuple vs -> pretty_tupled pretty_value vs

    | Closure(env, x, e) -> sprintf "<|%s;%s;%s|>" (pretty_env pretty_value env) x (pretty_expr e)

    | RecClosure(env, f, x, e) -> sprintf "<|%s;%s;%s;%s|>" (pretty_env pretty_value env) f x (pretty_expr e)


#nowarn "60"

type ty with

    override self.ToString() = pretty_ty self

type expr with

    override self.ToString() = pretty_expr self

type value with

    override self.ToString() = pretty_value self
