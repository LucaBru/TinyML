(*
* TinyML
* Main.fs: main code
*)

module TinyML.Main

open System
open FSharp.Common
open TinyML.Ast

let parse_from_TextReader rd filename parser =
    Parsing.parse_from_TextReader SyntaxError rd filename (1, 1) parser Lexer.tokenize Parser.tokenTagToTokenId

let parse_from_string line filename parser =
    Parsing.parse_from_string SyntaxError line filename (1, 1) parser Lexer.tokenize Parser.tokenTagToTokenId

let interpret_expr tenv venv e =
#if DEBUG
    printfn "AST:\t%A\npretty:\t%s" e (pretty_expr e)
#endif
    let inferred_type, substitution = Typing.typeinfer_expr tenv e
    //let t = Typing.typecheck_expr tenv e
#if DEBUG
    printfn "type:\t%s" (pretty_ty inferred_type)
#endif
    let v = Eval.eval_expr venv e
#if DEBUG
    printfn "value:\t%s\n" (pretty_value v)
#endif
    Typing.apply_subst inferred_type substitution, v

let trap f =
    try
        f ()
    with
    | SyntaxError(msg, lexbuf) ->
        printfn
            "\nsyntax error: %s\nat token: \"%s\"\nlocation: %O"
            msg
            (Array.fold (sprintf "%s%c") "" lexbuf.Lexeme)
            lexbuf.EndPos
    | TypeError msg -> printfn "\ntype error: %s" msg
    | UnexpectedError msg -> printfn "\nunexpected error: %s" msg

let main_interpreter filename =
    trap
    <| fun () ->
        printfn "loading source file '%s'..." filename
        use fstr = new IO.FileStream(filename, IO.FileMode.Open)
        use rd = new IO.StreamReader(fstr)
        let prg = parse_from_TextReader rd filename Parser.program
        let t, v = interpret_expr [] [] prg
        printfn "type:\t%s\nvalue:\t%s" (pretty_ty t) (pretty_value v)

let main_interactive () =
    printfn "entering interactive mode..."
    let mutable tenv = []

    let mutable venv = []

    while true do
        trap
        <| fun () ->
            printf "\n> "
            stdout.Flush()
            let line = Console.ReadLine()

            let x, (t, v) =
                match parse_from_string line "LINE" Parser.interactive with
                | IExpr e -> "it", interpret_expr tenv venv e

                | IBinding(_, x, _, _ as b) ->
                    let t, v = interpret_expr tenv venv (LetIn(b, Var x)) // TRICK: put the variable itself as body after the in
                    // update global environments
                    tenv <- (x, Forall(Set.empty, t)) :: tenv
                    venv <- (x, v) :: venv
                    x, (t, v)

            printfn "val %s : %s = %s" x (pretty_ty t) (pretty_value v)


[<EntryPoint>]
let main argv =
    let r =
        try
            if argv.Length < 1 then
                main_interactive ()
            else
                main_interpreter argv.[0]

            0
        with e ->
            printfn "\nexception caught: %O" e
            1

    Console.ReadLine() |> ignore
    r
