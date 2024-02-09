module Tests

open System
open Xunit
open TinyML.Ast
open TinyML.Typing

let identity = Lambda("x", None, Var "x")

[<Fact>]
let ``VAR`` () =
    let arrow_type_scheme = Forall(Set.singleton 0, TyArrow(TyVar 0, TyVar 1))
    let env = [ ("x", arrow_type_scheme) ]

    set_typevar_count 2
    let inferred_type, _ = typeinfer_expr env (Var "x")
    Assert.StrictEqual<ty>(TyArrow(TyVar 2, TyVar 1), inferred_type)

[<Fact>]
let ``VAR of absent variable`` () =
    Assert.Throws<TypeError>(fun () -> typeinfer_expr [] (Var "x") :> obj)

[<Fact>]
let ``ABS`` () =
    let zero = Lambda("x", None, Lit(LInt 0))

    let expected = TyArrow(TyVar 0, TyInt)
    let inferred_type, _ = typeinfer_expr [] zero
    Assert.StrictEqual<ty>(expected, inferred_type)

[<Fact>]
let ``APP`` () =
    let inferred_type, _ = typeinfer_expr [] (App(identity, Lit(LInt 5)))

    Assert.StrictEqual<ty>(TyInt, inferred_type)

[<Fact>]
let ``LET-IN`` () =
    let let_in_expr = Let("f", None, identity, App(Var "f", (Lit(LInt 5))))

    let inferred_type, _ = typeinfer_expr [] let_in_expr

    Assert.StrictEqual<ty>(TyInt, inferred_type)

[<Fact>]
let ``TUPLE`` () =
    let tuple = Tuple [identity; Lit (LString "t")]

    let inferred_type, _ = typeinfer_expr [] tuple
    Assert.StrictEqual<ty>(TyTuple([TyArrow (TyVar 0, TyVar 0); TyString]), inferred_type)

[<Fact>]
let ``LET-REC-IN`` () =
    let rec_function = LetRec("f", None, Lambda ("x", None, IfThenElse (Var "x", Lit (LInt 0), Some (App (Var "f", Lit (LBool true))))), App (Var "f", Lit (LBool false)))

    let inferred_type, _ = typeinfer_expr [] rec_function

    Assert.StrictEqual<ty>(TyInt, inferred_type)

[<Fact>]
let ``Compose substitutions`` () =
    let subst1 = [ (0, TyInt); (2, TyInt) ]
    let subst2 = [ (3, TyVar 2) ]

    let expected: subst = (3, TyInt) :: subst1

    Assert.StrictEqual<subst>(expected, subst1 $ subst2)

[<Fact>]
let ``Compose substitutions which generate conflicts`` () =
    let subst1 = [ (3, TyBool); (1, TyInt) ]
    let subst2 = [ (3, TyVar 1) ]

    Assert.Throws<TypeError>(fun () -> subst1 $ subst2 :> obj)

[<Fact>]
let ``Compose substitutions which generate circularity`` () =
    let subst1 = [ (1, TyVar 3) ]
    let subst2 = [ (3, TyVar 1) ]

    Assert.Throws<TypeError>(fun () -> subst1 $ subst2 :> obj)
