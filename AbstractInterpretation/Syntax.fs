module Syntax

open FSharpx.State

type Label = int

type AExpr =
    | Number of int
    | Minus of lhs:AExpr * rhs:AExpr
    | Id of string

type BExpr =
    | Lt of AExpr * AExpr
    | Nand of BExpr * BExpr

and Statement<'A> =
    | Assignment of variable:string * expr:AExpr * 'A
    | Skip of 'A
    | IfThen of cond:BExpr * thenClause:Statement<'A> * 'A
    | IfThenElse of cond:BExpr * thenClause:Statement<'A> * elseClause:Statement<'A> * 'A
    | While of cond:BExpr * body:Statement<'A> * 'A
    | Break of 'A
    | StatList of stats:List<Statement<'A>> * 'A

    with

    member this.attributes : 'A =
        match this with
        | Assignment(_, _, a)
        | Skip(a)
        | IfThen(_, _, a)
        | IfThenElse(_, _, _, a)
        | While(_, _, a)
        | Break(a)
        | StatList(_, a) ->
            a

type ControlFlowAttributes = {
    /// entrance to S
    at : Label
    /// exit point of S
    after : Label
    /// does the statement S contain a break that escapes out of S?
    escape : bool
    /// the destination label that a break out of S goes to
    breakTo : Label
    /// All labels of statements that can escape out of S
    breaksOf : Set<Label>
    /// All labels potential reachable while executing S, either inside or after S
    labs : Set<Label>
}

let getNextLabel() : State<int, int> =
    state {
        let! ret = getState
        do! putState (ret + 1)
        return ret
    }

let rec decorateControlFlow (s : Statement<unit>) (at : Label) (after : Label) (breakTo : Label) : State<Statement<ControlFlowAttributes>, int> = 
    match s with
    | Assignment(variable, aexpr, ()) ->
        state {
            let attributes = {
                at = at
                after = after
                escape = false
                breakTo = breakTo
                breaksOf = Set.empty
                labs = Set.singleton at
            }
            return Assignment(variable, aexpr, attributes)
        }
    | Skip(()) ->
        state {
            let attributes = {
                at = at
                after = after
                escape = false
                breakTo = breakTo
                breaksOf = Set.empty
                labs = Set.singleton at
            }
            return Skip(attributes)
        }
    | IfThen(cond, thenClause, ()) ->
        state {
            let condLabel = at
            let! thenLabel = getNextLabel()
            let! thenDecorated = decorateControlFlow thenClause thenLabel after breakTo
            let attributes = {
                at = condLabel
                after = after
                escape = thenDecorated.attributes.escape
                breakTo = breakTo
                breaksOf = thenDecorated.attributes.breaksOf
                labs = Set.add condLabel thenDecorated.attributes.labs
            }
            return IfThen(cond, thenDecorated, attributes)
        }
    | IfThenElse(cond, thenClause, elseClause, ()) ->
        state {
            let condLabel = at
            let! thenLabel = getNextLabel()
            let! thenDecorated = decorateControlFlow thenClause thenLabel after breakTo
            let! elseLabel = getNextLabel()
            let! elseDecorated = decorateControlFlow elseClause elseLabel after breakTo
            let attributes = {
                at = condLabel
                after = after
                escape = thenDecorated.attributes.escape || elseDecorated.attributes.escape
                breakTo = breakTo
                breaksOf = Set.union thenDecorated.attributes.breaksOf elseDecorated.attributes.breaksOf
                labs = Set.unionMany [Set.singleton condLabel ; thenDecorated.attributes.labs ; elseDecorated.attributes.labs ]
            }
            return IfThenElse(cond, thenDecorated, elseDecorated, attributes)
        }
    | While(cond, body, ()) ->
        state {
            let condLabel = at
            let! bodyLabel = getNextLabel()
            let! bodyDecorated = decorateControlFlow body bodyLabel condLabel after
            let attributes = {
                at = condLabel
                after = after
                escape = false
                breakTo = breakTo
                breaksOf = Set.empty
                labs = Set.add condLabel bodyDecorated.attributes.labs
            }
            return While(cond, bodyDecorated, attributes)
        }
    | Break(()) ->
        state {
            let attributes = {
                at = at
                after = after
                escape = true
                breakTo = breakTo
                breaksOf = Set.singleton at
                labs = Set.singleton at
            }
            return Break(attributes)
        }
    | StatList(stats, ()) ->
        assert (stats.Length > 0)
        let foldStat (acc : List<Statement<ControlFlowAttributes>>) 
                     ((stat, at, after) : Statement<unit> * Label * Label) 
                     : State<List<Statement<ControlFlowAttributes>>, int> =

            state {
                let! decorated = decorateControlFlow stat at after breakTo
                return decorated :: acc
            }

        state {
            let! restAtLabels = mapM getNextLabel (List.replicate (stats.Length - 1) ())
            let allAtLabels = at :: restAtLabels
            let allAfterLabels = List.append restAtLabels [after]
            let! statsDecorated = foldM foldStat [] (List.zip3 stats allAtLabels allAfterLabels)
            let attributes = {
                at = at
                after = after
                escape = List.exists (fun (stat : Statement<ControlFlowAttributes>) -> stat.attributes.escape) statsDecorated
                breakTo = breakTo
                breaksOf = Set.unionMany <| List.map (fun (stat : Statement<ControlFlowAttributes>) -> stat.attributes.breaksOf) statsDecorated
                labs = Set.unionMany <| List.map (fun (stat : Statement<ControlFlowAttributes>) -> stat.attributes.labs) statsDecorated
            }
            return StatList(statsDecorated, attributes)
        }