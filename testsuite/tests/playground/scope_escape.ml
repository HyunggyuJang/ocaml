(* TEST
   flags = "-I ${ocamlsrcdir}/typing \
    -I ${ocamlsrcdir}/parsing -I ${ocamlsrcdir}/toplevel -I ${ocamlsrcdir}/utils"
   * expect
*)

let e1 = Parse.implementation (Lexing.from_string "let x = ref []");;
[%%expect{|
val e1 : Parsetree.structure =
  [{Parsetree.pstr_desc =
     Parsetree.Pstr_value (Asttypes.Nonrecursive,
      [{Parsetree.pvb_pat =
         {Parsetree.ppat_desc =
           Parsetree.Ppat_var
            {Asttypes.txt = "x";
             loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 4};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 5};
               loc_ghost = false}};
          ppat_loc =
           {Location.loc_start =
             {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 4};
            loc_end =
             {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
            loc_ghost = false};
          ppat_loc_stack = []; ppat_attributes = []};
        pvb_expr =
         {Parsetree.pexp_desc =
           Parsetree.Pexp_apply
            ({Parsetree.pexp_desc =
               Parsetree.Pexp_ident
                {Asttypes.txt = Longident.Lident "ref";
                 loc =
                  {Location.loc_start =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 8};
                   loc_end =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 11};
                   loc_ghost = false}};
              pexp_loc =
               {Location.loc_start =
                 {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                  pos_cnum = 8};
                loc_end =
                 {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                  pos_cnum = 11};
                loc_ghost = false};
              pexp_loc_stack = []; pexp_attributes = []},
            [(Asttypes.Nolabel,
              {Parsetree.pexp_desc =
                Parsetree.Pexp_construct
                 ({Asttypes.txt = Longident.Lident "[]";
                   loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 12};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 14};
                     loc_ghost = false}},
                 None);
               pexp_loc =
                {Location.loc_start =
                  {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                   pos_cnum = 12};
                 loc_end =
                  {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                   pos_cnum = 14};
                 loc_ghost = false};
               pexp_loc_stack = []; pexp_attributes = []})]);
          pexp_loc =
           {Location.loc_start =
             {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 8};
            loc_end =
             {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
              pos_cnum = 14};
            loc_ghost = false};
          pexp_loc_stack = []; pexp_attributes = []};
        pvb_attributes = [];
        pvb_loc =
         {Location.loc_start =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
          loc_end =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 14};
          loc_ghost = false}}]);
    pstr_loc =
     {Location.loc_start =
       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
      loc_end =
       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 14};
      loc_ghost = false}}]
|}];;

let x_pat = match e1 with
    {pstr_desc = Pstr_value (_, {pvb_pat; _}::_); _}::_ ->
      pvb_pat
  | _ -> assert false;;
[%%expect{|
val x_pat : Parsetree.pattern =
  {Parsetree.ppat_desc =
    Parsetree.Ppat_var
     {Asttypes.txt = "x";
      loc =
       {Location.loc_start =
         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 4};
        loc_end =
         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
        loc_ghost = false}};
   ppat_loc =
    {Location.loc_start =
      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 4};
     loc_end =
      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
     loc_ghost = false};
   ppat_loc_stack = []; ppat_attributes = []}
|}];;

let lref = match e1 with
  {pstr_desc = Pstr_value (_, {pvb_expr = {pexp_desc = Pexp_apply ({pexp_desc = Pexp_ident sfun; _}, sarg); _}; _}::_); _}::_ ->
    sfun
| _ -> assert false;;
[%%expect{|
val lref : Longident.t Asttypes.loc =
  {Asttypes.txt = Longident.Lident "ref";
   loc =
    {Location.loc_start =
      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 8};
     loc_end =
      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 11};
     loc_ghost = false}}
|}];;

let ref_lookedup = Env.lookup_value ~loc:lref.loc lref.txt !Topcommon.toplevel_env;;
[%%expect{|
val ref_lookedup : Path.t * Types.value_description =
  (Path.Pdot (Path.Pident <abstr>, "ref"),
   {Types.val_type = <abstr>;
    val_kind =
     Types.Val_prim
      {Primitive.prim_name = "%makemutable"; prim_arity = 1;
       prim_alloc = true; prim_native_name = "";
       prim_native_repr_args = [Primitive.Same_as_ocaml_repr];
       prim_native_repr_res = Primitive.Same_as_ocaml_repr};
    val_loc =
     {Location.loc_start =
       {Lexing.pos_fname = "stdlib.mli"; pos_lnum = 1218; pos_bol = 46248;
        pos_cnum = 46248};
      loc_end =
       {Lexing.pos_fname = "stdlib.mli"; pos_lnum = 1218; pos_bol = 46248;
        pos_cnum = 46292};
      loc_ghost = false};
    val_attributes = [];
    val_uid = Types.Uid.Item {Types.Uid.comp_unit = "Stdlib"; id = 208}})
|}]

let ref_path_name = Path.name (fst ref_lookedup);;
[%%expect{|
val ref_path_name : string = "Stdlib.ref"
|}];;

Format.printf "%a" !Btype.print_raw (snd ref_lookedup).val_type;;
[%%expect{|
{id=1377;level=100000000;scope=0;desc=
 Tarrow("",{id=135;level=100000000;scope=0;desc=Tvar "a"},
  {id=1378;level=100000000;scope=0;desc=Tconstr(ref,[{id=135}],[])},Cok)}- : unit = ()
|}];;

let ref_instance = (Ctype.instance (snd ref_lookedup).val_type);;
[%%expect{|
val ref_instance : Types.type_expr = <abstr>
|}];;

Format.printf "%a" !Btype.print_raw ref_instance;;
[%%expect{|

{id=22712;level=0;scope=0;desc=
 Tarrow("",{id=22714;level=0;scope=0;desc=Tvar None},
  {id=22713;level=0;scope=0;desc=Tconstr(ref,[{id=22714}],[])},Cok)}- : unit = ()
|}, Principal{|

{id=22810;level=0;scope=0;desc=
 Tarrow("",{id=22812;level=0;scope=0;desc=Tvar None},
  {id=22811;level=0;scope=0;desc=Tconstr(ref,[{id=22812}],[])},Cok)}- : unit = ()
|}];;

let var = Ctype.newvar ();;
[%%expect{|
val var : Types.type_expr = <abstr>
|}];;

Typecore.unify_with_dump !Topcommon.toplevel_env (Ctype.instance (snd ref_lookedup).val_type) var;;
[%%expect{|
Before: {id=23706;level=0;scope=0;desc=
         Tarrow("",{id=23708;level=0;scope=0;desc=Tvar None},
          {id=23707;level=0;scope=0;desc=Tconstr(ref,[{id=23708}],[])},Cok)}
{id=22857;level=0;scope=0;desc=Tvar None}
In unify1_var: {id=22857;level=0;scope=0;desc=Tvar None}
{id=23706;level=0;scope=0;desc=
 Tarrow("",{id=23708;level=0;scope=0;desc=Tvar None},
  {id=23707;level=0;scope=0;desc=Tconstr(ref,[{id=23708}],[])},Cok)}
After: {id=23706;level=0;scope=0;desc=
        Tarrow("",{id=23708;level=0;scope=0;desc=Tvar None},
         {id=23707;level=0;scope=0;desc=Tconstr(ref,[{id=23708}],[])},Cok)}
{id=23706;level=0;scope=0;desc=
 Tarrow("",{id=23708;level=0;scope=0;desc=Tvar None},
  {id=23707;level=0;scope=0;desc=Tconstr(ref,[{id=23708}],[])},Cok)}
- : unit = ()
|}, Principal{|
Before: {id=23941;level=0;scope=0;desc=
         Tarrow("",{id=23943;level=0;scope=0;desc=Tvar None},
          {id=23942;level=0;scope=0;desc=Tconstr(ref,[{id=23943}],[])},Cok)}
{id=23050;level=0;scope=0;desc=Tvar None}
In unify1_var: {id=23050;level=0;scope=0;desc=Tvar None}
{id=23941;level=0;scope=0;desc=
 Tarrow("",{id=23943;level=0;scope=0;desc=Tvar None},
  {id=23942;level=0;scope=0;desc=Tconstr(ref,[{id=23943}],[])},Cok)}
After: {id=23941;level=0;scope=0;desc=
        Tarrow("",{id=23943;level=0;scope=0;desc=Tvar None},
         {id=23942;level=0;scope=0;desc=Tconstr(ref,[{id=23943}],[])},Cok)}
{id=23941;level=0;scope=0;desc=
 Tarrow("",{id=23943;level=0;scope=0;desc=Tvar None},
  {id=23942;level=0;scope=0;desc=Tconstr(ref,[{id=23943}],[])},Cok)}
- : unit = ()
|}]

let e2 = Parse.implementation (Lexing.from_string "module M = struct type t let _ = (x : t list ref) end");;
[%%expect{|
val e2 : Parsetree.structure =
  [{Parsetree.pstr_desc =
     Parsetree.Pstr_module
      {Parsetree.pmb_name =
        {Asttypes.txt = Some "M";
         loc =
          {Location.loc_start =
            {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 7};
           loc_end =
            {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 8};
           loc_ghost = false}};
       pmb_expr =
        {Parsetree.pmod_desc =
          Parsetree.Pmod_structure
           [{Parsetree.pstr_desc =
              Parsetree.Pstr_type (Asttypes.Recursive,
               [{Parsetree.ptype_name =
                  {Asttypes.txt = "t";
                   loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 23};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 24};
                     loc_ghost = false}};
                 ptype_params = []; ptype_cstrs = [];
                 ptype_kind = Parsetree.Ptype_abstract;
                 ptype_private = Asttypes.Public; ptype_manifest = None;
                 ptype_attributes = [];
                 ptype_loc =
                  {Location.loc_start =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 18};
                   loc_end =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 24};
                   loc_ghost = false}}]);
             pstr_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 18};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 24};
               loc_ghost = false}};
            {Parsetree.pstr_desc =
              Parsetree.Pstr_value (Asttypes.Nonrecursive,
               [{Parsetree.pvb_pat =
                  {Parsetree.ppat_desc = Parsetree.Ppat_any;
                   ppat_loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 29};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 30};
                     loc_ghost = false};
                   ppat_loc_stack = []; ppat_attributes = []};
                 pvb_expr =
                  {Parsetree.pexp_desc =
                    Parsetree.Pexp_constraint
                     ({Parsetree.pexp_desc =
                        Parsetree.Pexp_ident
                         {Asttypes.txt = Longident.Lident "x";
                          loc =
                           {Location.loc_start =
                             {Lexing.pos_fname = ""; pos_lnum = 1;
                              pos_bol = 0; pos_cnum = 34};
                            loc_end =
                             {Lexing.pos_fname = ""; pos_lnum = 1;
                              pos_bol = 0; pos_cnum = 35};
                            loc_ghost = false}};
                       pexp_loc =
                        {Location.loc_start =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 34};
                         loc_end =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 35};
                         loc_ghost = false};
                       pexp_loc_stack = []; pexp_attributes = []},
                     {Parsetree.ptyp_desc =
                       Parsetree.Ptyp_constr
                        ({Asttypes.txt = Longident.Lident "ref";
                          loc =
                           {Location.loc_start =
                             {Lexing.pos_fname = ""; pos_lnum = 1;
                              pos_bol = 0; pos_cnum = 45};
                            loc_end =
                             {Lexing.pos_fname = ""; pos_lnum = 1;
                              pos_bol = 0; pos_cnum = 48};
                            loc_ghost = false}},
                        [{Parsetree.ptyp_desc =
                           Parsetree.Ptyp_constr
                            ({Asttypes.txt = Longident.Lident "list";
                              loc =
                               {Location.loc_start =
                                 {Lexing.pos_fname = ""; pos_lnum = 1;
                                  pos_bol = 0; pos_cnum = 40};
                                loc_end =
                                 {Lexing.pos_fname = ""; pos_lnum = 1;
                                  pos_bol = 0; pos_cnum = 44};
                                loc_ghost = false}},
                            [{Parsetree.ptyp_desc =
                               Parsetree.Ptyp_constr
                                ({Asttypes.txt = Longident.Lident "t";
                                  loc =
                                   {Location.loc_start =
                                     {Lexing.pos_fname = ""; pos_lnum = 1;
                                      pos_bol = 0; pos_cnum = 38};
                                    loc_end =
                                     {Lexing.pos_fname = ""; pos_lnum = 1;
                                      pos_bol = 0; pos_cnum = 39};
                                    loc_ghost = false}},
                                []);
                              ptyp_loc =
                               {Location.loc_start =
                                 {Lexing.pos_fname = ""; pos_lnum = 1;
                                  pos_bol = 0; pos_cnum = 38};
                                loc_end =
                                 {Lexing.pos_fname = ""; pos_lnum = 1;
                                  pos_bol = 0; pos_cnum = 39};
                                loc_ghost = false};
                              ptyp_loc_stack = []; ptyp_attributes = []}]);
                          ptyp_loc =
                           {Location.loc_start =
                             {Lexing.pos_fname = ""; pos_lnum = 1;
                              pos_bol = 0; pos_cnum = 38};
                            loc_end =
                             {Lexing.pos_fname = ""; pos_lnum = 1;
                              pos_bol = 0; pos_cnum = 44};
                            loc_ghost = false};
                          ptyp_loc_stack = []; ptyp_attributes = []}]);
                      ptyp_loc =
                       {Location.loc_start =
                         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                          pos_cnum = 38};
                        loc_end =
                         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                          pos_cnum = 48};
                        loc_ghost = false};
                      ptyp_loc_stack = []; ptyp_attributes = []});
                   pexp_loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 33};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 49};
                     loc_ghost = false};
                   pexp_loc_stack = []; pexp_attributes = []};
                 pvb_attributes = [];
                 pvb_loc =
                  {Location.loc_start =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 25};
                   loc_end =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 49};
                   loc_ghost = false}}]);
             pstr_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 25};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 49};
               loc_ghost = false}}];
         pmod_loc =
          {Location.loc_start =
            {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 11};
           loc_end =
            {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 53};
           loc_ghost = false};
         pmod_attributes = []};
       pmb_attributes = [];
       pmb_loc =
        {Location.loc_start =
          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
         loc_end =
          {Lexing.pos_fname = ""; pos_lnum = ...; pos_bol = ...;
           pos_cnum = ...};
         loc_ghost = ...}};
    pstr_loc = ...};
   ...]
|}];;
let t1 = Typemod.type_structure_with_dump !Topcommon.toplevel_env e1;;
[%%expect{|
In type_let, new variables: [{id=30350;level=1;scope=0;desc=Tvar None}]
In type_let, pattern variables: [{id=30350}]
In type_let, pattern vars:  [{id=30350}]
In type_expect_: sexp: expression ([1,0+8]..[1,0+14])
  Pexp_apply
  expression ([1,0+8]..[1,0+11])
    Pexp_ident "ref" ([1,0+8]..[1,0+11])
  [
    <arg>
    Nolabel
      expression ([1,0+12]..[1,0+14])
        Pexp_construct "[]" ([1,0+12]..[1,0+14])
        None
  ]

expected: {id=30350;level=1;scope=0;desc=Tvar None}
In type_expect_: sexp: expression ([1,0+8]..[1,0+11])
  Pexp_ident "ref" ([1,0+8]..[1,0+11])

expected: {id=30351;level=2;scope=0;desc=Tvar None}
In unify1_var: {id=30351;level=2;scope=0;desc=Tvar None}
{id=30352;level=2;scope=0;desc=
 Tarrow("",{id=30354;level=2;scope=0;desc=Tvar None},
  {id=30353;level=2;scope=0;desc=Tconstr(ref,[{id=30354}],[])},Cok)}
In type_expect_: sexp: expression ([1,0+12]..[1,0+14])
  Pexp_construct "[]" ([1,0+12]..[1,0+14])
  None

expected: {id=30354;level=1;scope=0;desc=Tvar None}
In unify1_var: {id=30354;level=1;scope=0;desc=Tvar None}
{id=30356;level=2;scope=0;desc=
 Tconstr(list,[{id=30357;level=2;scope=0;desc=Tvar None}],[])}
In unify_eq: {id=30356;level=1;scope=0;desc=
              Tconstr(list,[{id=30357;level=1;scope=0;desc=Tvar None}],[])}
{id=30356;level=1;scope=0;desc=
 Tconstr(list,[{id=30357;level=1;scope=0;desc=Tvar None}],[])}
In unify1_var: {id=30350;level=1;scope=0;desc=Tvar None}
{id=30353;level=1;scope=0;desc=
 Tconstr(ref,
  [{id=30356;level=1;scope=0;desc=
    Tconstr(list,[{id=30357;level=1;scope=0;desc=Tvar None}],[])}],[])}
In type_let, exp_list:
[{id=30353;level=1;scope=0;desc=
  Tconstr(ref,
   [{id=30356;level=1;scope=0;desc=
     Tconstr(list,[{id=30357;level=1;scope=0;desc=Tvar None}],[])}],[])}]
val t1 :
  Typedtree.structure * Types.signature * Typemod.Signature_names.t *
  Shape.t * Env.t =
  ({Typedtree.str_items =
     [{Typedtree.str_desc =
        Typedtree.Tstr_value (Asttypes.Nonrecursive,
         [{Typedtree.vb_pat =
            {Typedtree.pat_desc =
              Typedtree.Tpat_var (<abstr>,
               {Asttypes.txt = "x";
                loc =
                 {Location.loc_start =
                   {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                    pos_cnum = 4};
                  loc_end =
                   {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                    pos_cnum = 5};
                  loc_ghost = false}});
             pat_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 4};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 5};
               loc_ghost = false};
             pat_extra = []; pat_type = <abstr>; pat_env = <abstr>;
             pat_attributes = []};
           vb_expr =
            {Typedtree.exp_desc =
              Typedtree.Texp_apply
               ({Typedtree.exp_desc =
                  Typedtree.Texp_ident
                   (Path.Pdot (Path.Pident <abstr>, "ref"),
                   {Asttypes.txt = Longident.Lident "ref";
                    loc =
                     {Location.loc_start =
                       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                        pos_cnum = 8};
                      loc_end =
                       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                        pos_cnum = 11};
                      loc_ghost = false}},
                   {Types.val_type = <abstr>;
                    val_kind =
                     Types.Val_prim
                      {Primitive.prim_name = "%makemutable"; prim_arity = 1;
                       prim_alloc = true; prim_native_name = "";
                       prim_native_repr_args = [Primitive.Same_as_ocaml_repr];
                       prim_native_repr_res = Primitive.Same_as_ocaml_repr};
                    val_loc =
                     {Location.loc_start =
                       {Lexing.pos_fname = "stdlib.mli"; pos_lnum = 1218;
                        pos_bol = 46248; pos_cnum = 46248};
                      loc_end =
                       {Lexing.pos_fname = "stdlib.mli"; pos_lnum = 1218;
                        pos_bol = 46248; pos_cnum = 46292};
                      loc_ghost = false};
                    val_attributes = [];
                    val_uid =
                     Types.Uid.Item
                      {Types.Uid.comp_unit = "Stdlib"; id = 208}});
                 exp_loc =
                  {Location.loc_start =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 8};
                   loc_end =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 11};
                   loc_ghost = false};
                 exp_extra = []; exp_type = <abstr>; exp_env = <abstr>;
                 exp_attributes = []},
               [(Asttypes.Nolabel,
                 Some
                  {Typedtree.exp_desc =
                    Typedtree.Texp_construct
                     ({Asttypes.txt = Longident.Lident "[]";
                       loc =
                        {Location.loc_start =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 12};
                         loc_end =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 14};
                         loc_ghost = false}},
                     {Types.cstr_name = "[]"; cstr_res = <abstr>;
                      cstr_existentials = []; cstr_args = []; cstr_arity = 0;
                      cstr_tag = Types.Cstr_constant 0; cstr_consts = 1;
                      cstr_nonconsts = 1; cstr_generalized = false;
                      cstr_private = Asttypes.Public;
                      cstr_loc =
                       {Location.loc_start =
                         {Lexing.pos_fname = "_none_"; pos_lnum = 0;
                          pos_bol = 0; pos_cnum = -1};
                        loc_end =
                         {Lexing.pos_fname = "_none_"; pos_lnum = 0;
                          pos_bol = 0; pos_cnum = -1};
                        loc_ghost = true};
                      cstr_attributes = []; cstr_inlined = None;
                      cstr_uid = Types.Uid.Predef "[]"},
                     []);
                   exp_loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 12};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 14};
                     loc_ghost = false};
                   exp_extra = []; exp_type = <abstr>; exp_env = <abstr>;
                   exp_attributes = []})]);
             exp_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 8};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 14};
               loc_ghost = false};
             exp_extra = []; exp_type = <abstr>; exp_env = <abstr>;
             exp_attributes = []};
           vb_attributes = [];
           vb_loc =
            {Location.loc_start =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 0};
             loc_end =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 14};
             loc_ghost = false}}]);
       str_loc =
        {Location.loc_start =
          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
         loc_end =
          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 14};
         loc_ghost = false};
       str_env = <abstr>}];
    str_type =
     [Types.Sig_value (<abstr>,
       {Types.val_type = <abstr>; val_kind = Types.Val_reg;
        val_loc =
         {Location.loc_start =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 4};
          loc_end =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
          loc_ghost = false};
        val_attributes = [];
        val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 20}},
       Types.Exported)];
    str_final_env = <abstr>},
   [Types.Sig_value (<abstr>,
     {Types.val_type = <abstr>; val_kind = Types.Val_reg;
      val_loc =
       {Location.loc_start =
         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 4};
        loc_end =
         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
        loc_ghost = false};
      val_attributes = [];
      val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 20}},
     Types.Exported)],
   <abstr>, {Shape.uid = None; desc = Shape.Struct <abstr>}, <abstr>)
|}, Principal{|
In type_let, new variables: [{id=30479;level=2;scope=0;desc=Tvar None}]
In type_let, pattern variables: [{id=30479}]
In type_let, pattern vars:  [{id=30479}]
In type_expect_: sexp: expression ([1,0+8]..[1,0+14])
  Pexp_apply
  expression ([1,0+8]..[1,0+11])
    Pexp_ident "ref" ([1,0+8]..[1,0+11])
  [
    <arg>
    Nolabel
      expression ([1,0+12]..[1,0+14])
        Pexp_construct "[]" ([1,0+12]..[1,0+14])
        None
  ]

expected: {id=30479;level=1;scope=0;desc=Tvar None}
In type_expect_: sexp: expression ([1,0+8]..[1,0+11])
  Pexp_ident "ref" ([1,0+8]..[1,0+11])

expected: {id=30480;level=3;scope=0;desc=Tvar None}
In unify1_var: {id=30480;level=3;scope=0;desc=Tvar None}
{id=30481;level=3;scope=0;desc=
 Tarrow("",{id=30483;level=3;scope=0;desc=Tvar None},
  {id=30482;level=3;scope=0;desc=Tconstr(ref,[{id=30483}],[])},Cok)}
In type_expect_: sexp: expression ([1,0+12]..[1,0+14])
  Pexp_construct "[]" ([1,0+12]..[1,0+14])
  None

expected: {id=30483;level=1;scope=0;desc=Tvar None}
In unify1_var: {id=30483;level=1;scope=0;desc=Tvar None}
{id=30491;level=3;scope=0;desc=
 Tconstr(list,[{id=30490;level=3;scope=0;desc=Tvar None}],[])}
In unify2_expand: {id=30492;level=2;scope=0;desc=
                   Tconstr(list,[{id=30490;level=1;scope=0;desc=Tvar None}],
                    [])}
{id=30491;level=1;scope=0;desc=
 Tconstr(list,[{id=30490;level=1;scope=0;desc=Tvar None}],[])}
In unify_eq: {id=30490;level=1;scope=0;desc=Tvar None}
{id=30490;level=1;scope=0;desc=Tvar None}
In unify1_var: {id=30479;level=1;scope=0;desc=Tvar None}
{id=30488;level=2;scope=0;desc=
 Tconstr(ref,
  [{id=30491;level=1;scope=0;desc=
    Tconstr(list,[{id=30490;level=1;scope=0;desc=Tvar None}],[])}],[])}
In type_let, exp_list:
[{id=30488;level=1;scope=0;desc=
  Tconstr(ref,
   [{id=30491;level=1;scope=0;desc=
     Tconstr(list,[{id=30490;level=1;scope=0;desc=Tvar None}],[])}],[])}]
val t1 :
  Typedtree.structure * Types.signature * Typemod.Signature_names.t *
  Shape.t * Env.t =
  ({Typedtree.str_items =
     [{Typedtree.str_desc =
        Typedtree.Tstr_value (Asttypes.Nonrecursive,
         [{Typedtree.vb_pat =
            {Typedtree.pat_desc =
              Typedtree.Tpat_var (<abstr>,
               {Asttypes.txt = "x";
                loc =
                 {Location.loc_start =
                   {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                    pos_cnum = 4};
                  loc_end =
                   {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                    pos_cnum = 5};
                  loc_ghost = false}});
             pat_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 4};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 5};
               loc_ghost = false};
             pat_extra = []; pat_type = <abstr>; pat_env = <abstr>;
             pat_attributes = []};
           vb_expr =
            {Typedtree.exp_desc =
              Typedtree.Texp_apply
               ({Typedtree.exp_desc =
                  Typedtree.Texp_ident
                   (Path.Pdot (Path.Pident <abstr>, "ref"),
                   {Asttypes.txt = Longident.Lident "ref";
                    loc =
                     {Location.loc_start =
                       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                        pos_cnum = 8};
                      loc_end =
                       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                        pos_cnum = 11};
                      loc_ghost = false}},
                   {Types.val_type = <abstr>;
                    val_kind =
                     Types.Val_prim
                      {Primitive.prim_name = "%makemutable"; prim_arity = 1;
                       prim_alloc = true; prim_native_name = "";
                       prim_native_repr_args = [Primitive.Same_as_ocaml_repr];
                       prim_native_repr_res = Primitive.Same_as_ocaml_repr};
                    val_loc =
                     {Location.loc_start =
                       {Lexing.pos_fname = "stdlib.mli"; pos_lnum = 1218;
                        pos_bol = 46248; pos_cnum = 46248};
                      loc_end =
                       {Lexing.pos_fname = "stdlib.mli"; pos_lnum = 1218;
                        pos_bol = 46248; pos_cnum = 46292};
                      loc_ghost = false};
                    val_attributes = [];
                    val_uid =
                     Types.Uid.Item
                      {Types.Uid.comp_unit = "Stdlib"; id = 208}});
                 exp_loc =
                  {Location.loc_start =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 8};
                   loc_end =
                    {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                     pos_cnum = 11};
                   loc_ghost = false};
                 exp_extra = []; exp_type = <abstr>; exp_env = <abstr>;
                 exp_attributes = []},
               [(Asttypes.Nolabel,
                 Some
                  {Typedtree.exp_desc =
                    Typedtree.Texp_construct
                     ({Asttypes.txt = Longident.Lident "[]";
                       loc =
                        {Location.loc_start =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 12};
                         loc_end =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 14};
                         loc_ghost = false}},
                     {Types.cstr_name = "[]"; cstr_res = <abstr>;
                      cstr_existentials = []; cstr_args = []; cstr_arity = 0;
                      cstr_tag = Types.Cstr_constant 0; cstr_consts = 1;
                      cstr_nonconsts = 1; cstr_generalized = false;
                      cstr_private = Asttypes.Public;
                      cstr_loc =
                       {Location.loc_start =
                         {Lexing.pos_fname = "_none_"; pos_lnum = 0;
                          pos_bol = 0; pos_cnum = -1};
                        loc_end =
                         {Lexing.pos_fname = "_none_"; pos_lnum = 0;
                          pos_bol = 0; pos_cnum = -1};
                        loc_ghost = true};
                      cstr_attributes = []; cstr_inlined = None;
                      cstr_uid = Types.Uid.Predef "[]"},
                     []);
                   exp_loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 12};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 14};
                     loc_ghost = false};
                   exp_extra = []; exp_type = <abstr>; exp_env = <abstr>;
                   exp_attributes = []})]);
             exp_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 8};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 14};
               loc_ghost = false};
             exp_extra = []; exp_type = <abstr>; exp_env = <abstr>;
             exp_attributes = []};
           vb_attributes = [];
           vb_loc =
            {Location.loc_start =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 0};
             loc_end =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 14};
             loc_ghost = false}}]);
       str_loc =
        {Location.loc_start =
          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
         loc_end =
          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 14};
         loc_ghost = false};
       str_env = <abstr>}];
    str_type =
     [Types.Sig_value (<abstr>,
       {Types.val_type = <abstr>; val_kind = Types.Val_reg;
        val_loc =
         {Location.loc_start =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 4};
          loc_end =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
          loc_ghost = false};
        val_attributes = [];
        val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 20}},
       Types.Exported)];
    str_final_env = <abstr>},
   [Types.Sig_value (<abstr>,
     {Types.val_type = <abstr>; val_kind = Types.Val_reg;
      val_loc =
       {Location.loc_start =
         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 4};
        loc_end =
         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
        loc_ghost = false};
      val_attributes = [];
      val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 20}},
     Types.Exported)],
   <abstr>, {Shape.uid = None; desc = Shape.Struct <abstr>}, <abstr>)
|}]
