module OperationalSemantics

open Syntax

type Env = Map<string, int>

type State = {
    env : Env 
    label : int
}

type ActionTemplate = 
    | SkipTemplate of after:Label
    | BreakTemplate of breakTo:Label
    | AssignTemplate of var:string * aexpr:AExpr * after:Label
    | CondTemplate of cond:BExpr * afterTrue:Label * afterFalse:Label

[<StructuredFormatDisplay("{DisplayText}")>]
type Action =
    | SkipAction
    | BreakAction
    | AssignAction of var:string * newVal:int
    | CondAction of cond:BExpr * isTrue:bool

    member this.DisplayText = this.ToString()

    override this.ToString() : string =
        match this with
        | SkipAction ->
            "Skip"
        | BreakAction ->
            "Break"
        | AssignAction(var, newVal) ->
            $"{var} = {newVal}"
        | CondAction(cond, isTrue) ->
            if isTrue then
                $"{cond}"
            else
                $"!{cond}"

let private getActionTemplate (s : Statement<ControlFlowAttributes>) (label : Label) : ActionTemplate =
    assert (s.Attributes.labs.Contains label)
    let rec getActionAux (s : Statement<ControlFlowAttributes>) : Set<ActionTemplate> =        
        match s with
        | Assignment(variable, expr, attr) ->
            if attr.at = label then Set.singleton (AssignTemplate(variable, expr, attr.after)) else Set.empty
        | Skip(attr) ->
            if attr.at = label then Set.singleton (SkipTemplate(attr.after)) else Set.empty
        | IfThen(cond, thenClause, attr) ->
            let condTemplates = 
                if attr.at = label then
                    Set.singleton (CondTemplate(cond, thenClause.Attributes.at, attr.after))
                else
                    Set.empty
            Set.union condTemplates (getActionAux thenClause)
        | IfThenElse(cond, thenClause, elseClause, attr) ->
            let condTemplates =
                if attr.at = label then
                    Set.singleton (CondTemplate(cond, thenClause.Attributes.at, elseClause.Attributes.at)) 
                else
                    Set.empty
            Set.unionMany [
                condTemplates
                getActionAux thenClause
                getActionAux elseClause
            ]
        | While(cond, body, attr) ->
            let condTemplates =
                if attr.at = label then
                    Set.singleton (CondTemplate(cond, body.Attributes.at, attr.after))
                else
                    Set.empty 
            Set.union condTemplates (getActionAux body)
        | Break(attr) ->
            if attr.at = label then Set.singleton (BreakTemplate(attr.breakTo)) else Set.empty
        | StatList(stats, attr) ->
            Set.unionMany (List.map getActionAux stats)
    let result = getActionAux s
    assert (result.Count = 1)
    result.MinimumElement

let rec evalAExpr (env : Env) (aexpr : AExpr) : int =
    match aexpr with
    | Number(n) ->
        n 
    | Minus(lhs, rhs) ->
        (evalAExpr env lhs) - (evalAExpr env rhs)
    | Id(x) ->
        if env.ContainsKey x then
            env[x]
        else
            0

let rec evalBExpr (env : Env) (bexpr : BExpr) : bool =
    match bexpr with
    | Lt(lAExpr, rAExpr) ->
        (evalAExpr env lAExpr) < (evalAExpr env rAExpr)
    | Nand(lBExpr, rBExpr) ->
        not ((evalBExpr env lBExpr) && (evalBExpr env rBExpr))

let step (s : Statement<ControlFlowAttributes>) (state : State) : Action * State =
    match getActionTemplate s state.label with 
    | SkipTemplate(after) ->
        SkipAction, { state with label = after }
    | BreakTemplate(breakTo) ->
        BreakAction, { state with label = breakTo }
    | AssignTemplate(var, aexpr, after) ->
        let newVal = evalAExpr state.env aexpr
        AssignAction(var, newVal), { env = state.env.Add(var, newVal) ; label = after }
    | CondTemplate(cond, afterTrue, afterFalse) ->
        match evalBExpr state.env cond with
        | true ->
            CondAction(cond, true), { state with label = afterTrue }
        | false ->
            CondAction(cond, false), { state with label = afterFalse }

/// Returns (initLabel, transitions), where initLabel is the starting label
/// and each transition is a pair of an action and a label the action transitions to 
let trace (s : Statement<ControlFlowAttributes>) : Label * List<Action * Label> =
    let mutable state = { env = Map.empty ; label = s.Attributes.at }
    let mutable result : List<Action * Label> = []
    while state.label <> s.Attributes.after do
        let action, state' = step s state
        result <- (action, state'.label) :: result
        state <- state'
    s.Attributes.at, List.rev result

let sprintTrace (s : Statement<ControlFlowAttributes>) : string = 
    let initLabel, transitions = trace s
    let sprintTransition ((action, label) : Action * Label) : string =
        $"--[{action}]-> l{label}"
    $"l{initLabel} " + String.concat " " (List.map sprintTransition transitions)