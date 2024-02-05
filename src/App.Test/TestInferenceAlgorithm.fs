module ``Test inference algorithm``

open NUnit.Framework
open TinyML.Typing
open TinyML.Ast

let empty_sub: subst = []

let int_arrow_bool = TyArrow(TyName "int", TyName "bool")

let negate =
    Lambda("x", None, IfThenElse(Var "x", Lit(LBool false), Some(Lit(LBool true))))

let env_within_y = [ ("y", Forall(Set.empty, int_arrow_bool)) ]

[<SetUp>]
let ``set up`` () = reset_typevar_counter

[<Test>]
let ``I-VAR`` () =
    Assert.AreEqual((int_arrow_bool, empty_sub), typeinfer_expr env_within_y (Var "y"))

[<Test>]
let ``I-ABS`` () =
    Assert.AreEqual((TyArrow(TyName "bool", TyName "bool"), [ (0, TyName "bool") ]), typeinfer_expr [] negate)

[<Test>]
let ``I_APP`` () =
    Assert.AreEqual((TyName "bool", [ (0, TyName "bool") ]), typeinfer_expr [] (App(negate, Lit(LBool false))))

[<Test>]
let ``Application with unification error`` () =
    Assert.Throws<UnificationError>(fun () -> typeinfer_expr [] (App(negate, Lit(LInt 2))) |> ignore)
    |> ignore

[<Test>]
let ``I-TUP`` () =
  let tuple = Tuple ([negate; Var "y"; Lit(LInt 0); App (negate, Lit(LBool true))])
  let types = [TyArrow (TyBool, TyBool); int_arrow_bool; TyInt; TyBool]

  Assert.AreEqual ((TyTuple types, empty_sub), typeinfer_expr env_within_y tuple)