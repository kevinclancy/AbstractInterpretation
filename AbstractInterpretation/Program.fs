open System.IO
open FSharp.Text.Lexing
open Parser
open Lexer
open Syntax
open OperationalSemantics

let printProg (filename : string) =
    let reader = 
        try 
            new StreamReader(filename)
        with
        | :? FileNotFoundException ->
            printfn $"file not found"
            exit 1

    let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(reader.ReadToEnd())

    let stat = Parser.prog Lexer.token lexbuffer 

    let stat' = decorateControlFlow stat
    let diagram = statDiagram stat'
    let trace = sprintTrace stat'
    $"{diagram}\n\n{trace}"
    
[<EntryPoint>]
let main (argv : string[]) =
    if argv.Length = 0 then
        printfn $"provide the name of a text file as the command line argument"
        exit 1
    
    printf "%s" (printProg argv[0])

    1


