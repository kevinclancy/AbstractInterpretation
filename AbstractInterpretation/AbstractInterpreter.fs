module AbstractInterpreter

open Syntax
open Domain

/// Computes the least fixpoint of *f* above *a*
let rec lfp (a : 'D) (f : 'D -> 'D) (leq : 'D -> 'D  -> bool) =
    let fa = f a in
    if leq fa a then
        fa
    else
        lfp fa f leq

type InterpretationAttributes<'D> = {
    at : Label
    stateAt : 'D
    after : Label
    stateAfter : 'D
    escape : bool
    breakTo: Label
    /// The join of the states at all break labels
    stateAnyBreak : 'D
}

type While<'D> = BExpr * Statement<InterpretationAttributes<'D>> * InterpretationAttributes<'D>

let leq (D : Domain<'D>) (x : While<'D>) (y : While<'D>) : bool =
    let (_, _, {stateAt = stateAtX ; stateAfter = stateAfterX ; stateAnyBreak = stateAnyBreakX }) = x
    let (_, _, { stateAt = stateAtY ; stateAfter = stateAfterY ; stateAnyBreak = stateAnyBreakY}) = y
    (D.Leq stateAtX stateAtY) && (D.Leq stateAfterX stateAfterY) && (D.Leq stateAnyBreakX stateAnyBreakY)

let rec fWhile (D : Domain<'D>) (state0 : 'D) (w : While<'D>) : While<'D> =
    let (bexprW, bodyW, attrW) = w
    let stateAt = D.Join state0 attrW.stateAt
    let bodyW' = abstractInterpret D bodyW (D.TestPos bexprW stateAt)
    let stateAfter' = bodyW'.Attr.stateAfter
    let stateAnyBreak' = bodyW'.Attr.stateAnyBreak
    let attrW' = {
        attrW with
            stateAt = D.Join stateAt stateAfter'
            stateAfter = D.Join (D.TestNeg bexprW stateAt) stateAnyBreak'
            stateAnyBreak = D.Bot
    }
    (bexprW, bodyW', attrW')

and abstractInterpret (D : Domain<'D>)
                      (s : Statement<InterpretationAttributes<'D>>)
                      (state0 : 'D)
                      : Statement<InterpretationAttributes<'D>> =

    match s with
    | Skip(attr) ->
        Skip({ attr with stateAt = state0 ; stateAfter = state0 ; stateAnyBreak = D.Bot})
    | Assignment(var, aexpr, attr) ->
        let stateAfter' = D.Assign var aexpr state0
        Assignment(var, aexpr, { attr with stateAt = state0 ; stateAfter = stateAfter' ; stateAnyBreak = D.Bot})
    | IfThen(cond, thenClause, attr) ->
        let thenClause' = abstractInterpret D thenClause (D.TestPos cond state0)
        let attr' = {
            attr with
                stateAt = state0
                stateAfter = D.Join (thenClause'.Attr.stateAfter) (D.TestNeg cond state0)
                stateAnyBreak = thenClause'.Attr.stateAnyBreak
        }
        IfThen(cond, thenClause', attr')
    | IfThenElse(cond, thenClause, elseClause, attr) ->
        let thenClause' = abstractInterpret D thenClause (D.TestPos cond state0)
        let elseClause' = abstractInterpret D elseClause (D.TestNeg cond state0)
        let attr' = {
            attr with
                stateAt = state0
                stateAfter = D.Join (thenClause'.Attr.stateAfter) (elseClause'.Attr.stateAfter)
                stateAnyBreak = D.Join (thenClause'.Attr.stateAnyBreak) (elseClause'.Attr.stateAnyBreak)
        }
        IfThenElse(cond, thenClause', elseClause', attr')
    | Break(attr) ->
        Break({attr with stateAt = state0 ; stateAfter = D.Bot ; stateAnyBreak = state0})
    | While(cond, body, attr) ->
        let whileBot = (cond, body, {attr with stateAt = D.Bot ; stateAfter = D.Bot ; stateAnyBreak = D.Bot})
        let fpCond, fpBody, fpAttr = lfp whileBot (fWhile D state0) (leq D)
        let fpBody' = abstractInterpret D fpBody (D.TestPos fpCond fpAttr.stateAt)
        While(fpCond, fpBody', fpAttr)
    | StatList(stats, attr) ->
        let stats', stateAt', stateAfter', stateAnyBreak' = abstractInterpretStatList D stats state0
        let attr' = {
            attr with
                stateAt = stateAt'
                stateAfter = stateAfter'
                stateAnyBreak = stateAnyBreak'
        }
        StatList(stats', attr')

and abstractInterpretStatList (D : Domain<'D>)
                              (stats : List<Statement<InterpretationAttributes<'D>>>)
                              (state0 : 'D)
                              : List<Statement<InterpretationAttributes<'D>>> * 'D * 'D * 'D =

    match stats with
    | [] ->
        failwith "impossible - we only create statement lists with at least one statement"
    | [s] ->
        let s' = abstractInterpret D s state0
        [s'], s'.Attr.stateAt, s'.Attr.stateAfter, s'.Attr.stateAnyBreak
    | s :: restStats ->
        let s' = abstractInterpret D s state0
        let restStats', _, restStateAfter', restStateAnyBreak' =
            abstractInterpretStatList D restStats s'.Attr.stateAfter
        s' :: restStats', s'.Attr.stateAt, restStateAfter', (D.Join s'.Attr.stateAnyBreak restStateAnyBreak')



