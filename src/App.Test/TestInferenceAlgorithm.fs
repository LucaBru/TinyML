module ``Test inference algorithm``

open NUnit.Framework
open TinyML.Typing
open TinyML.Ast

let empty_sub: subst = []

let int_arrow_bool = TyArrow(TyName "int", TyName "bool")

let negate =
  Lambda (
    "x",
    None,
    IfThenElse (
      Var "x", 
      Lit(LBool false),
      Some (Lit(LBool true))
    )
  )

[<SetUp>]
let ``set up`` () =
  reset_typevar_counter

[<Test>]
let ``I-VAR`` () =
    let env: scheme env = [ ("y", Forall(Set.empty, int_arrow_bool))]
    
    Assert.AreEqual ((int_arrow_bool, empty_sub), typeinfer_expr env (Var "y"))

[<Test>]
let ``I-ABS`` () =
    Assert.AreEqual((TyArrow(TyName "bool", TyName "bool"), [(0, TyName "bool")]), typeinfer_expr [] negate)

[<Test>]
let ``I_APP`` () =
  Assert.AreEqual ((TyName "bool", [(0, TyName "bool")]), typeinfer_expr [] (App(negate, Lit(LBool false))))

[<Test>]
let ``Application with unification error`` () =
  Assert.Throws<UnificationError>(fun () -> typeinfer_expr [] (App (negate, Lit(LInt 2))) |> ignore) |> ignore