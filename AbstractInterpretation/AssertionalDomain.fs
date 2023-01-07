module AssertionalDomain

open Syntax
open OperationalSemantics
open Domain

let AssertionalDomain = {
    new Domain<Set<Env>> with
        member this.Bot =
            Set.empty

        member this.Join (a : Set<Env>) (b : Set<Env>) : Set<Env> =
            Set.union a b

        member this.Leq (a : Set<Env>) (b : Set<Env>) : bool =
            Set.isSubset a b

        member this.Assign (varName : string) (aexpr : AExpr) (a : Set<Env>) : Set<Env> =
            let mapEnv (env : Env) : Env =
                env.Add(varName, evalAExpr env aexpr)
            Set.map mapEnv a

        member this.TestPos (bexpr : BExpr) (a : Set<Env>) : Set<Env> =
            Set.filter (fun env -> evalBExpr env bexpr) a

        member this.TestNeg (bexpr : BExpr) (a : Set<Env>) : Set<Env> =
            Set.filter (fun env -> not (evalBExpr env bexpr)) a
}