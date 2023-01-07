module Domain

open Syntax

type Domain<'X> =
    abstract member Leq : 'X -> 'X -> bool
    abstract member Bot : 'X
    abstract member Join : 'X -> 'X -> 'X
    abstract member Assign : string -> AExpr -> 'X -> 'X
    abstract member TestPos : BExpr -> 'X -> 'X
    abstract member TestNeg : BExpr -> 'X -> 'X