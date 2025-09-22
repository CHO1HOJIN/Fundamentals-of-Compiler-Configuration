open FSharp.Text.Lexing
open AST

let usage () =
  let _ = printfn "<Usage>"
  let _ = printfn "[*] ./out/TypeCheck print-ast <source file>"
  let _ = printfn "[*] ./out/TypeCheck check-error <source file>"
  exit 1

let lex (file: string): LexBuffer<_> =
  try
    let streamReader = new System.IO.StreamReader(file)
    let lexbuf = LexBuffer<_>.FromTextReader streamReader
    lexbuf.EndPos <- { lexbuf.EndPos with pos_lnum = 1 }
    lexbuf
  with :? System.IO.IOException ->
    printfn "[*] Failed to open file '%s'" file
    exit 1

let parse (lexbuf: LexBuffer<_>) : Program =
  try Parser.prog Lexer.token lexbuf
  with _ ->
    printfn "[*] Parsing error at line %d" (lexbuf.EndPos.Line)
    exit 1

[<EntryPoint>]
let main argv =
  if Array.length argv <> 2 then usage ()
  let lexbuf = lex argv[1]
  let prog = parse lexbuf
  match argv[0] with
  | "print-ast" -> printfn "%s" (Program.toStr prog)
  | "check-error" -> List.iter (fun i -> printfn "%d" i) (TypeCheck.run prog)
  | s -> usage ()
  0
