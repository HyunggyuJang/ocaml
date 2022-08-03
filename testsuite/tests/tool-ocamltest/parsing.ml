(* TEST
   flags = "-I ${ocamlsrcdir}/ocamltest"
   * toplevel
*)

#load "ocamltest.cma";;
let block = Tsl_parser.tsl_block Tsl_lexer.token (Lexing.from_string {xx|
(* TEST
   flags = "-I ${ocamlsrcdir}/ocamltest"
   * expect
*)

#load "tsl_ast.cmo";;
#load "tsl_parser.cmo";;
#load "tsl_lexer.cmo";;
Tsl_parser.tsl_block Tsl_lexer.token (Lexing.from_string {|
(* TEST
   flags = "-I ${ocamlsrcdir}/ocamltest"
   * expect
*)
|});;
[%%expect {|
- : Tsl_ast.tsl_block =
[Tsl_ast.Environment_statement
  {Tsl_ast.node =
    Tsl_ast.Assignment (false, {Tsl_ast.node = "flags"; loc = <abstr>},
     {Tsl_ast.node = "-I ${ocamlsrcdir}/ocamltest"; loc = <abstr>});
   loc = <abstr>};
 Tsl_ast.Test (1, {Tsl_ast.node = "expect"; loc = <abstr>}, [])]
|}];;
|xx});;
Tsl_semantics.test_trees_of_tsl_block block;;
