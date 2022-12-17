// Implementation file for parser generated by fsyacc
module Parser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open FSharp.Text.Lexing
open FSharp.Text.Parsing.ParseHelpers
# 1 ".\Parser.fsy"

open System
open Syntax

let mutable nextLabel = 0

let getNextLabel() : int =
    let ret = nextLabel
    nextLabel <- nextLabel + 1
    ret

# 18 ".\Parser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | PLUS
  | MINUS
  | TIMES
  | SKIP
  | LT
  | NAND
  | EOF
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | IF
  | ELSE
  | WHILE
  | BREAK
  | EQUALS
  | SEMICOLON
  | ID of (string)
  | INT of (int)
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_TIMES
    | TOKEN_SKIP
    | TOKEN_LT
    | TOKEN_NAND
    | TOKEN_EOF
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_IF
    | TOKEN_ELSE
    | TOKEN_WHILE
    | TOKEN_BREAK
    | TOKEN_EQUALS
    | TOKEN_SEMICOLON
    | TOKEN_ID
    | TOKEN_INT
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startprog
    | NONTERM_bexpr
    | NONTERM_aexpr
    | NONTERM_stat
    | NONTERM_statList
    | NONTERM_prog

// This function maps tokens to integer indexes
let tagOfToken (t:token) = 
  match t with
  | PLUS  -> 0 
  | MINUS  -> 1 
  | TIMES  -> 2 
  | SKIP  -> 3 
  | LT  -> 4 
  | NAND  -> 5 
  | EOF  -> 6 
  | LPAREN  -> 7 
  | RPAREN  -> 8 
  | LBRACK  -> 9 
  | RBRACK  -> 10 
  | IF  -> 11 
  | ELSE  -> 12 
  | WHILE  -> 13 
  | BREAK  -> 14 
  | EQUALS  -> 15 
  | SEMICOLON  -> 16 
  | ID _ -> 17 
  | INT _ -> 18 

// This function maps integer indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_PLUS 
  | 1 -> TOKEN_MINUS 
  | 2 -> TOKEN_TIMES 
  | 3 -> TOKEN_SKIP 
  | 4 -> TOKEN_LT 
  | 5 -> TOKEN_NAND 
  | 6 -> TOKEN_EOF 
  | 7 -> TOKEN_LPAREN 
  | 8 -> TOKEN_RPAREN 
  | 9 -> TOKEN_LBRACK 
  | 10 -> TOKEN_RBRACK 
  | 11 -> TOKEN_IF 
  | 12 -> TOKEN_ELSE 
  | 13 -> TOKEN_WHILE 
  | 14 -> TOKEN_BREAK 
  | 15 -> TOKEN_EQUALS 
  | 16 -> TOKEN_SEMICOLON 
  | 17 -> TOKEN_ID 
  | 18 -> TOKEN_INT 
  | 21 -> TOKEN_end_of_input
  | 19 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startprog 
    | 1 -> NONTERM_bexpr 
    | 2 -> NONTERM_bexpr 
    | 3 -> NONTERM_bexpr 
    | 4 -> NONTERM_aexpr 
    | 5 -> NONTERM_aexpr 
    | 6 -> NONTERM_aexpr 
    | 7 -> NONTERM_aexpr 
    | 8 -> NONTERM_stat 
    | 9 -> NONTERM_stat 
    | 10 -> NONTERM_stat 
    | 11 -> NONTERM_stat 
    | 12 -> NONTERM_stat 
    | 13 -> NONTERM_stat 
    | 14 -> NONTERM_stat 
    | 15 -> NONTERM_statList 
    | 16 -> NONTERM_statList 
    | 17 -> NONTERM_prog 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 21 
let _fsyacc_tagOfErrorTerminal = 19

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | PLUS  -> "PLUS" 
  | MINUS  -> "MINUS" 
  | TIMES  -> "TIMES" 
  | SKIP  -> "SKIP" 
  | LT  -> "LT" 
  | NAND  -> "NAND" 
  | EOF  -> "EOF" 
  | LPAREN  -> "LPAREN" 
  | RPAREN  -> "RPAREN" 
  | LBRACK  -> "LBRACK" 
  | RBRACK  -> "RBRACK" 
  | IF  -> "IF" 
  | ELSE  -> "ELSE" 
  | WHILE  -> "WHILE" 
  | BREAK  -> "BREAK" 
  | EQUALS  -> "EQUALS" 
  | SEMICOLON  -> "SEMICOLON" 
  | ID _ -> "ID" 
  | INT _ -> "INT" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | PLUS  -> (null : System.Object) 
  | MINUS  -> (null : System.Object) 
  | TIMES  -> (null : System.Object) 
  | SKIP  -> (null : System.Object) 
  | LT  -> (null : System.Object) 
  | NAND  -> (null : System.Object) 
  | EOF  -> (null : System.Object) 
  | LPAREN  -> (null : System.Object) 
  | RPAREN  -> (null : System.Object) 
  | LBRACK  -> (null : System.Object) 
  | RBRACK  -> (null : System.Object) 
  | IF  -> (null : System.Object) 
  | ELSE  -> (null : System.Object) 
  | WHILE  -> (null : System.Object) 
  | BREAK  -> (null : System.Object) 
  | EQUALS  -> (null : System.Object) 
  | SEMICOLON  -> (null : System.Object) 
  | ID _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | INT _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
let _fsyacc_gotos = [| 0us;65535us;4us;65535us;10us;6us;11us;7us;27us;8us;33us;9us;8us;65535us;4us;5us;10us;2us;11us;3us;16us;13us;19us;14us;22us;15us;27us;2us;33us;2us;6us;65535us;0us;41us;28us;29us;30us;31us;34us;35us;38us;41us;41us;41us;3us;65535us;0us;43us;38us;39us;41us;42us;1us;65535us;0us;1us;|]
let _fsyacc_sparseGotoTableRowOffsets = [|0us;1us;6us;15us;22us;26us;|]
let _fsyacc_stateToProdIdxsTableElements = [| 1us;0us;1us;0us;2us;1us;4us;3us;1us;4us;7us;1us;1us;2us;1us;4us;2us;2us;2us;2us;2us;3us;3us;2us;10us;11us;2us;2us;12us;1us;2us;2us;3us;7us;1us;3us;2us;4us;4us;2us;4us;7us;2us;4us;8us;1us;4us;1us;5us;1us;6us;1us;7us;1us;7us;1us;8us;1us;8us;1us;8us;1us;9us;1us;9us;2us;10us;11us;2us;10us;11us;2us;10us;11us;2us;10us;11us;1us;11us;1us;11us;1us;12us;1us;12us;1us;12us;1us;12us;1us;13us;1us;13us;1us;14us;1us;14us;1us;14us;2us;15us;16us;1us;15us;1us;17us;1us;17us;|]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us;2us;4us;7us;11us;13us;16us;19us;22us;26us;29us;31us;34us;36us;39us;42us;45us;47us;49us;51us;53us;55us;57us;59us;61us;63us;65us;68us;71us;74us;77us;79us;81us;83us;85us;87us;89us;91us;93us;95us;97us;99us;102us;104us;106us;|]
let _fsyacc_action_rows = 45
let _fsyacc_actionTableElements = [|6us;32768us;3us;24us;9us;38us;11us;26us;13us;32us;14us;36us;17us;21us;0us;49152us;2us;32768us;1us;16us;4us;4us;3us;32768us;1us;16us;4us;4us;8us;20us;3us;32768us;7us;19us;17us;18us;18us;17us;1us;16385us;1us;16us;0us;16386us;2us;32768us;5us;10us;8us;12us;2us;32768us;5us;10us;8us;28us;2us;32768us;5us;10us;8us;34us;3us;32768us;7us;11us;17us;18us;18us;17us;3us;32768us;7us;11us;17us;18us;18us;17us;0us;16387us;0us;16388us;2us;32768us;1us;16us;8us;20us;2us;32768us;1us;16us;16us;23us;3us;32768us;7us;19us;17us;18us;18us;17us;0us;16389us;0us;16390us;3us;32768us;7us;19us;17us;18us;18us;17us;0us;16391us;1us;32768us;15us;22us;3us;32768us;7us;19us;17us;18us;18us;17us;0us;16392us;1us;32768us;16us;25us;0us;16393us;1us;32768us;7us;27us;3us;32768us;7us;11us;17us;18us;18us;17us;6us;32768us;3us;24us;9us;38us;11us;26us;13us;32us;14us;36us;17us;21us;1us;16394us;12us;30us;6us;32768us;3us;24us;9us;38us;11us;26us;13us;32us;14us;36us;17us;21us;0us;16395us;1us;32768us;7us;33us;3us;32768us;7us;11us;17us;18us;18us;17us;6us;32768us;3us;24us;9us;38us;11us;26us;13us;32us;14us;36us;17us;21us;0us;16396us;1us;32768us;16us;37us;0us;16397us;6us;32768us;3us;24us;9us;38us;11us;26us;13us;32us;14us;36us;17us;21us;1us;32768us;10us;40us;0us;16398us;6us;16400us;3us;24us;9us;38us;11us;26us;13us;32us;14us;36us;17us;21us;0us;16399us;1us;32768us;6us;44us;0us;16401us;|]
let _fsyacc_actionTableRowOffsets = [|0us;7us;8us;11us;15us;19us;21us;22us;25us;28us;31us;35us;39us;40us;41us;44us;47us;51us;52us;53us;57us;58us;60us;64us;65us;67us;68us;70us;74us;81us;83us;90us;91us;93us;97us;104us;105us;107us;108us;115us;117us;118us;125us;126us;128us;|]
let _fsyacc_reductionSymbolCounts = [|1us;3us;3us;3us;3us;1us;1us;3us;4us;2us;5us;7us;5us;2us;3us;2us;1us;2us;|]
let _fsyacc_productionToNonTerminalTable = [|0us;1us;1us;1us;2us;2us;2us;2us;3us;3us;3us;3us;3us;3us;3us;4us;4us;5us;|]
let _fsyacc_immediateActions = [|65535us;49152us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;16387us;65535us;65535us;65535us;65535us;16389us;16390us;65535us;16391us;65535us;65535us;16392us;65535us;16393us;65535us;65535us;65535us;65535us;65535us;16395us;65535us;65535us;65535us;16396us;65535us;16397us;65535us;65535us;16398us;65535us;16399us;65535us;16401us;|]
let _fsyacc_reductions = lazy [|
# 203 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> Statement<unit> in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : 'gentype__startprog));
# 212 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_aexpr in
            let _3 = parseState.GetInput(3) :?> 'gentype_aexpr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 30 ".\Parser.fsy"
                                              Lt(_1, _3) 
                   )
# 30 ".\Parser.fsy"
                 : 'gentype_bexpr));
# 224 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_bexpr in
            let _3 = parseState.GetInput(3) :?> 'gentype_bexpr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 31 ".\Parser.fsy"
                                                Nand(_1, _3) 
                   )
# 31 ".\Parser.fsy"
                 : 'gentype_bexpr));
# 236 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_bexpr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 32 ".\Parser.fsy"
                                                   _2 
                   )
# 32 ".\Parser.fsy"
                 : 'gentype_bexpr));
# 247 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_aexpr in
            let _3 = parseState.GetInput(3) :?> 'gentype_aexpr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 34 ".\Parser.fsy"
                                                 Minus(_1, _3) 
                   )
# 34 ".\Parser.fsy"
                 : 'gentype_aexpr));
# 259 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> int in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 35 ".\Parser.fsy"
                                   Number(_1) 
                   )
# 35 ".\Parser.fsy"
                 : 'gentype_aexpr));
# 270 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> string in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 36 ".\Parser.fsy"
                                  Id(_1) 
                   )
# 36 ".\Parser.fsy"
                 : 'gentype_aexpr));
# 281 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_aexpr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 37 ".\Parser.fsy"
                                                   _2 
                   )
# 37 ".\Parser.fsy"
                 : 'gentype_aexpr));
# 292 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> string in
            let _3 = parseState.GetInput(3) :?> 'gentype_aexpr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 39 ".\Parser.fsy"
                                                        Assignment(_1, _3, ()) 
                   )
# 39 ".\Parser.fsy"
                 : 'gentype_stat));
# 304 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 40 ".\Parser.fsy"
                                             Skip() 
                   )
# 40 ".\Parser.fsy"
                 : 'gentype_stat));
# 314 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _3 = parseState.GetInput(3) :?> 'gentype_bexpr in
            let _5 = parseState.GetInput(5) :?> 'gentype_stat in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 41 ".\Parser.fsy"
                                                          IfThen(_3, _5, ()) 
                   )
# 41 ".\Parser.fsy"
                 : 'gentype_stat));
# 326 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _3 = parseState.GetInput(3) :?> 'gentype_bexpr in
            let _5 = parseState.GetInput(5) :?> 'gentype_stat in
            let _7 = parseState.GetInput(7) :?> 'gentype_stat in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 42 ".\Parser.fsy"
                                                                    IfThenElse(_3, _5, _7, ()) 
                   )
# 42 ".\Parser.fsy"
                 : 'gentype_stat));
# 339 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _3 = parseState.GetInput(3) :?> 'gentype_bexpr in
            let _5 = parseState.GetInput(5) :?> 'gentype_stat in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 43 ".\Parser.fsy"
                                                             While(_3, _5, ()) 
                   )
# 43 ".\Parser.fsy"
                 : 'gentype_stat));
# 351 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 44 ".\Parser.fsy"
                                              Break() 
                   )
# 44 ".\Parser.fsy"
                 : 'gentype_stat));
# 361 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_statList in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 45 ".\Parser.fsy"
                                                     StatList(_2, ()) 
                   )
# 45 ".\Parser.fsy"
                 : 'gentype_stat));
# 372 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_stat in
            let _2 = parseState.GetInput(2) :?> 'gentype_statList in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 47 ".\Parser.fsy"
                                                _1 :: _2 
                   )
# 47 ".\Parser.fsy"
                 : 'gentype_statList));
# 384 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_stat in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 48 ".\Parser.fsy"
                                       [_1] 
                   )
# 48 ".\Parser.fsy"
                 : 'gentype_statList));
# 395 ".\Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_statList in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 50 ".\Parser.fsy"
                                           StatList(_1, ()) 
                   )
# 50 ".\Parser.fsy"
                 : Statement<unit>));
|]
# 407 ".\Parser.fs"
let tables : FSharp.Text.Parsing.Tables<_> = 
  { reductions = _fsyacc_reductions.Value;
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken; 
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt:FSharp.Text.Parsing.ParseErrorContext<_>) -> 
                              match parse_error_rich with 
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 22;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = tables.Interpret(lexer, lexbuf, startState)
let prog lexer lexbuf : Statement<unit> =
    engine lexer lexbuf 0 :?> _
