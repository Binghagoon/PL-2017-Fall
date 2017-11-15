
let main () =
    let src = ref "" in
    let spec = [] in
    let usage = "Usage: run <options> <file>" in
    let _ = Arg.parse spec
                (fun
                   x ->
                     if Sys.file_exists x then src := x
                     else raise (Arg.Bad (x ^ ": No files given")))
                usage
    in

  if !src = "" then Arg.usage spec usage
  else
    let file_channel = open_in !src in
    let lexbuf = Lexing.from_channel file_channel in
    let pgm = Parser.program Lexer.start lexbuf in
      C.execute pgm

let _ = main ()
