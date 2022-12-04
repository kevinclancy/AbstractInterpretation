open System.IO
open FSharp.Text.Lexing
open Parser
open Lexer

// open a text file

// parse the text file


// copy the above stuff from SchemaTypes

[<EntryPoint>]
let main (argv : string[]) =
    if argv.Length = 0 then
        printfn $"provide the name of a text file as the command line argument"
        exit 1
    
    let reader = 
        try 
            new StreamReader(argv[0])
        with
        | :? FileNotFoundException ->
            printfn $"file not found"
            exit 1

    let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(reader.ReadToEnd())

    let stat = Parser.stat Lexer.token lexbuffer 

    1


