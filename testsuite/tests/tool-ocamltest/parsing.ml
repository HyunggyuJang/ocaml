(* TEST
   ld_library_path += "${ocamlsrcdir}/ocamltest ${ocamlsrcdir}/otherlibs/unix"
   flags = "-I ${ocamlsrcdir}/ocamltest"
   * expect
*)

#load "ocamltest.cma";;
open Tsl_parser
open Tsl_lexer
open Tsl_semantics
open Tsl_ast
let block = tsl_block token (Lexing.from_string {xx|
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
test_trees_of_tsl_block block;;
[%%expect {|
val block : Tsl_ast.tsl_block =
  [Environment_statement
    {node =
      Assignment (false, {node = "flags"; loc = <abstr>},
       {node = "-I ${ocamlsrcdir}/ocamltest"; loc = <abstr>});
     loc = <abstr>};
   Test (1, {node = "expect"; loc = <abstr>}, [])]
- : Tsl_ast.environment_statement Tsl_ast.located list *
    Tsl_semantics.test_tree list
=
([{node =
    Assignment (false, {node = "flags"; loc = <abstr>},
     {node = "-I ${ocamlsrcdir}/ocamltest"; loc = <abstr>});
   loc = <abstr>}],
 [Node ([],
   {Tests.test_name = "expect"; test_run_by_default = false;
    test_actions = [<abstr>; <abstr>; <abstr>]},
   [], [])])
|}];;
