module ``Test inference algorithm``

open NUnit.Framework
open TinyML.Typing
open TinyML.Ast

let empty_sub: subst = []

let int_arrow_bool = TyArrow(TyInt, TyBool)

let negate =
    Lambda("x", None, IfThenElse(Var "x", Lit(LBool false), Some(Lit(LBool true))))

let env_within_y = [ ("y", Forall(Set.empty, int_arrow_bool)) ]

[<SetUp>]
let ``set up`` () = reset_typevar_counter ()

[<Test>]
let ``I-VAR`` () =
    Assert.AreEqual((int_arrow_bool, empty_sub), typeinfer_expr env_within_y (Var "y"))

[<Test>]
let ``I-ABS`` () =
    Assert.AreEqual((TyArrow(TyBool, TyBool), [ (0, TyBool) ]), typeinfer_expr [] negate)

[<Test>]
let ``I_APP`` () =
    Assert.AreEqual((TyBool, [ (0, TyBool) ]), typeinfer_expr [] (App(negate, Lit(LBool false))))

[<Test>]
let ``Application with unification error`` () =
    Assert.Throws<UnificationError>(fun () -> typeinfer_expr [] (App(negate, Lit(LInt 2))) |> ignore)
    |> ignore

[<Test>]
let ``I-TUP`` () =
    let tuple = Tuple([ negate; Var "y"; Lit(LInt 0); App(negate, Lit(LBool true)) ])
    let types = [ TyArrow(TyBool, TyBool); int_arrow_bool; TyInt; TyBool ]

    Assert.AreEqual((TyTuple types, empty_sub), typeinfer_expr env_within_y tuple)

[<Test>]
let ``I-LET-REC`` () =
    printfn "let rec"
    let l = Lambda ("x", None, IfThenElse (Var "x", Lit (LInt 0), Some (App (Var "f", Lit (LBool true)))))
    let rec_lambda = LetRec ("f", None, l, Lit (LInt 0))
    //rec_lambda => let rec f = fun x -> if x then 0 else f 1 in 0
    //type of rec_lambda = int -> int
    Assert.AreEqual ((TyArrow (TyInt, TyInt), [(0, TyArrow (TyInt, TyInt))]), typeinfer_expr [] rec_lambda)