module Syntax

open FSharpx.State
open FSharpx

type Label = int

type AExpr =
    | Number of int
    | Minus of lhs:AExpr * rhs:AExpr
    | Id of string

    override this.ToString() =
        match this with
        | Number(n) ->
            n.ToString()
        | Minus(lhs, rhs) ->
            $"({lhs} - {rhs})"
        | Id(x) ->
            x

type BExpr =
    | Lt of AExpr * AExpr
    | Nand of BExpr * BExpr

    override this.ToString() =
        match this with
        | Lt(lhs, rhs) ->
            $"({lhs} < {rhs})"
        | Nand(lhs, rhs) ->
            $"({lhs} nand {rhs})"

and Statement<'A> =
    | Assignment of variable:string * expr:AExpr * 'A
    | Skip of 'A
    | IfThen of cond:BExpr * thenClause:Statement<'A> * 'A
    | IfThenElse of cond:BExpr * thenClause:Statement<'A> * elseClause:Statement<'A> * 'A
    | While of cond:BExpr * body:Statement<'A> * 'A
    | Break of 'A
    | StatList of stats:List<Statement<'A>> * 'A

    with

    member this.Attributes : 'A =
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
    with

    member this.Summary =
        $"<l{this.at}, l{this.after}, {this.escape}, l{this.breakTo}>"

let getNextLabel() : State<int, int> =
    state {
        let! ret = getState
        do! putState (ret + 1)
        return ret
    }

let rec private decorateControlFlowAux (s : Statement<unit>) (at : Label) (after : Label) (breakTo : Label) : State<Statement<ControlFlowAttributes>, int> = 
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
            let! thenDecorated = decorateControlFlowAux thenClause thenLabel after breakTo
            let attributes = {
                at = condLabel
                after = after
                escape = thenDecorated.Attributes.escape
                breakTo = breakTo
                breaksOf = thenDecorated.Attributes.breaksOf
                labs = Set.add condLabel thenDecorated.Attributes.labs
            }
            return IfThen(cond, thenDecorated, attributes)
        }
    | IfThenElse(cond, thenClause, elseClause, ()) ->
        state {
            let condLabel = at
            let! thenLabel = getNextLabel()
            let! thenDecorated = decorateControlFlowAux thenClause thenLabel after breakTo
            let! elseLabel = getNextLabel()
            let! elseDecorated = decorateControlFlowAux elseClause elseLabel after breakTo
            let attributes = {
                at = condLabel
                after = after
                escape = thenDecorated.Attributes.escape || elseDecorated.Attributes.escape
                breakTo = breakTo
                breaksOf = Set.union thenDecorated.Attributes.breaksOf elseDecorated.Attributes.breaksOf
                labs = Set.unionMany [Set.singleton condLabel ; thenDecorated.Attributes.labs ; elseDecorated.Attributes.labs ]
            }
            return IfThenElse(cond, thenDecorated, elseDecorated, attributes)
        }
    | While(cond, body, ()) ->
        state {
            let condLabel = at
            let! bodyLabel = getNextLabel()
            let! bodyDecorated = decorateControlFlowAux body bodyLabel condLabel after
            let attributes = {
                at = condLabel
                after = after
                escape = false
                breakTo = breakTo
                breaksOf = Set.empty
                labs = Set.add condLabel bodyDecorated.Attributes.labs
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
                let! decorated = decorateControlFlowAux stat at after breakTo
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
                escape = List.exists (fun (stat : Statement<ControlFlowAttributes>) -> stat.Attributes.escape) statsDecorated
                breakTo = breakTo
                breaksOf = Set.unionMany <| List.map (fun (stat : Statement<ControlFlowAttributes>) -> stat.Attributes.breaksOf) statsDecorated
                labs = Set.unionMany <| List.map (fun (stat : Statement<ControlFlowAttributes>) -> stat.Attributes.labs) statsDecorated
            }
            return StatList(List.rev statsDecorated, attributes)
        }

let decorateControlFlow (stat : Statement<unit>) : Statement<ControlFlowAttributes> =
    let computeResult : State<Statement<ControlFlowAttributes>, int> =
        state {
            let! at = getNextLabel()
            let! after = getNextLabel()
            let! result = decorateControlFlowAux stat at after after
            return result
        }
    State.eval computeResult 0

let statDiagram (stat : Statement<ControlFlowAttributes>) : string =
    let rec statDiagramAux (stat : Statement<ControlFlowAttributes>) (level : int) =
        let indent = String.replicate ((2*level) - stat.Attributes.Summary.Length) " "
        match stat with
        | Assignment(variable, expr, attr) ->
            $"{attr.Summary}{indent}l{attr.at}: {variable} = {expr};"
        | Skip(attr) ->
            $"{attr.Summary}{indent}l{attr.at}: skip;"
        | IfThen(cond, thenClause, attr) ->
            $"{attr.Summary}{indent}(if l{attr.at}: {cond}\n{statDiagramAux thenClause (level + 1)})"
        | IfThenElse(cond, thenClause, elseClause, attr) ->
            let thenDiagram = statDiagramAux thenClause (level + 1)
            let elseDiagram = statDiagramAux elseClause (level + 1)
            let elseIndent = (String.replicate attr.Summary.Length " ") + indent
            $"{attr.Summary}{indent}(if l{attr.at}: {cond}\n{thenDiagram}\n{elseIndent}else\n{elseDiagram}"
        | While(cond, body, attr) ->
            let bodyDiagram = statDiagramAux body (level + 1)
            $"{attr.Summary}{indent}(while l{attr.at}: {cond}\n{bodyDiagram})"
        | Break(attr) ->
            $"{attr.Summary}{indent}l{attr.at}: break;"
        | StatList(stats, attr) ->
            let statDiagrams = List.map (fun x -> statDiagramAux x (level + 1)) stats 
            let statDiagramsString = String.concat "\n" statDiagrams
            let lbrack = "{"
            let rbrack = "}"
            let rbrackIndent = (String.replicate (attr.Summary.Length) " ") + indent
            $"{attr.Summary}{indent}{lbrack}\n{statDiagramsString}\n{rbrackIndent}{rbrack}"
    statDiagramAux stat 12