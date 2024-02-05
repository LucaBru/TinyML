module ``Test auxiliary procedure of typing algorithm``

open NUnit.Framework
open TinyML.Ast
open TinyML.Typing

let int_arrow_2 = TyArrow(TyName "int", TyVar 2)

let tuple_type =
    TyTuple(
        [ TyArrow(TyName "int", TyVar 2)
          TyName "int"
          TyName "string"
          TyArrow(TyName "int", TyVar 1) ]
    )

let tuple_type_ftv =
    TyTuple(
        [ TyVar 0
          TyName "int"
          TyArrow(TyVar 1, TyVar 2)
          TyTuple(TyVar 3 :: TyVar 3 :: []) ]
    )

[<Test>]
let ``Is type var into an arrow type`` () =
    Assert.True(is_typevar_into_type 2 int_arrow_2)

[<Test>]
let ``Is type var into an tuple type`` () =
    Assert.True(is_typevar_into_type 1 tuple_type)

[<Test>]
let ``Compose composable substitutions`` () =
    let subst1 = [ (0, TyArrow(TyName "int", TyName "string")); (3, TyName "int") ]
    let subst2 = [ (3, TyName "int"); (4, TyName "int") ]

    Assert.AreEqual(List.distinct subst1 @ subst2, compose_subst subst1 subst2)

[<Test>]
let ``Compose substitutions with joint domains, exception expected`` () =
    let subst1 = [ (0, TyName "int") ]
    let subst2 = [ (0, TyName "string") ]

    Assert.Throws<CompositionError>(fun () -> compose_subst subst1 subst2 |> ignore)
    |> ignore

[<Test>]
let ``Compose substitutions with circularity, exception expected`` () =
    let subst1 = [ (0, TyVar 1) ]
    let subst2 = [ (1, TyName "int") ]

    Assert.Throws<CompositionError>(fun () -> compose_subst subst1 subst2 |> ignore)
    |> ignore

[<Test>]
let ``Unify unifiable types`` () =
    let t1 = TyArrow(TyName "int", TyName "int")
    let expected = [ (2, TyName "int") ]

    Assert.AreEqual(expected, unify t1 int_arrow_2)

[<Test>]
let ``Unify not unifiable types, exception expected`` () =
    let t1 = TyName "int"
    let t2 = TyArrow(TyName "bool", TyName "int")

    Assert.Throws<UnificationError>(fun () -> unify t1 t2 |> ignore) |> ignore

[<Test>]
let ``Apply substitution`` () =
    let tuple =
        TyTuple(
            [ TyVar 0
              TyName "int"
              TyArrow(TyVar 1, TyVar 0)
              TyTuple(TyVar 0 :: TyVar 1 :: []) ]
        )

    let subst = [ (0, TyName "int") ]

    let expected =
        TyTuple[TyName "int"
                TyName "int"
                TyArrow(TyVar 1, TyName "int")
                TyTuple(TyName "int" :: TyVar 1 :: [])]

    Assert.AreEqual(expected, apply_subst tuple subst)

[<Test>]
let ``Calculate type's free type variables`` () =
    Assert.AreEqual(Set.ofList [ 0; 1; 2; 3 ], freevars_ty tuple_type_ftv)

[<Test>]
let ``Calculate scheme's free type variables`` () =
    let sc = Forall(Set.ofList [ 0; 2 ], tuple_type_ftv)
    let expected = Set.ofList [ 1; 3 ]

    Assert.AreEqual(expected, freevars_scheme sc)

[<Test>]
let ``Calculate environment's free type variables`` () =
    let sc1 = Forall(Set.ofList [ 0 ], TyArrow(TyVar 0, TyVar 1))
    let sc2 = Forall(Set.ofList [ 0; 2 ], tuple_type_ftv)
    let env = [ ("x", sc1); ("y", sc2) ]

    let expected = [ 1; 3 ] |> Set.ofList
    Assert.AreEqual(expected, freevars_scheme_env env)
