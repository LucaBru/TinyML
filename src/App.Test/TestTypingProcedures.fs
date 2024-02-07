module ``Test auxiliary procedure of typing algorithm``

open NUnit.Framework
open TinyML.Ast
open TinyML.Typing

let int_arrow_2 = TyArrow(TyInt, TyVar 2)

let tuple_type =
    TyTuple([ TyArrow(TyInt, TyVar 2); TyInt; TyString; TyArrow(TyInt, TyVar 1) ])

let tuple_type_ftv =
    TyTuple([ TyVar 0; TyInt; TyArrow(TyVar 1, TyVar 2); TyTuple(TyVar 3 :: TyVar 3 :: []) ])

[<Test>]
let ``Is type var into an arrow type`` () =
    Assert.True(is_typevar_into_type 2 int_arrow_2)

[<Test>]
let ``Is type var into an tuple type`` () =
    Assert.True(is_typevar_into_type 1 tuple_type)

[<Test>]
let ``Compose composable substitutions`` () =
    let subst1 = [(0, TyInt); (1, TyTuple ([TyBool; TyChar]))]
    let subst2 = [(0, TyInt); (2, TyVar 3)]
    let subst3 = [(3, TyInt)]

    let composed_substitution = subst3 $ subst2 $ subst1

    composed_substitution |> List.iter (fun (type_var, t) -> printf $"{type_var} -> {pretty_ty t};")

    Assert.AreEqual ([],compose_subst )

[<Test>]
let ``Compose substitutions with joint domains, exception expected`` () =
    let subst1 = [ (0, TyInt) ]
    let subst2 = [ (0, TyString) ]

    Assert.Throws<CompositionError>(fun () -> compose_subst subst1 subst2 |> ignore)
    |> ignore

[<Test>]
let ``Compose substitutions with circularity, exception expected`` () =
    let subst1 = [ (0, TyVar 1) ]
    let subst2 = [ (1, TyVar 0) ]

    Assert.Throws<CompositionError>(fun () -> compose_subst subst1 subst2 |> ignore)
    |> ignore

[<Test>]
let ``Unify unifiable types`` () =
    let t1 = TyArrow(TyInt, TyInt)
    let expected = [ (2, TyInt) ]

    Assert.AreEqual(expected, unify t1 int_arrow_2)

[<Test>]
let ``Unify not unifiable types, exception expected`` () =
    let t1 = TyInt
    let t2 = TyArrow(TyBool, TyInt)

    Assert.Throws<UnificationError>(fun () -> unify t1 t2 |> ignore) |> ignore

[<Test>]
let ``Apply substitution`` () =
    let tuple =
        TyTuple([ TyVar 0; TyInt; TyArrow(TyVar 1, TyVar 0); TyTuple(TyVar 0 :: TyVar 1 :: []) ])

    let subst = [ (0, TyInt) ]

    let expected =
        TyTuple[TyInt
                TyInt
                TyArrow(TyVar 1, TyInt)
                TyTuple(TyInt :: TyVar 1 :: [])]

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
