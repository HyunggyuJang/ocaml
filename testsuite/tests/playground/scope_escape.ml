(* TEST
   flags = "-I ${ocamlsrcdir}/typing \
    -I ${ocamlsrcdir}/parsing -I ${ocamlsrcdir}/toplevel -dump-unification"
   * expect
*)

let e1 = Parse.implementation (Lexing.from_string "let x = ref []");;
[%%expect{|
{id=1528;level=2;scope=0;desc=
 Tarrow("",{id=1530;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},
  {id=1529;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])},Cok)}
{id=1435;level=2;scope=0;desc=Tvar None}
{id=3364;level=3;scope=0;desc=
 Tarrow("?with_positions",
  {id=3368;level=3;scope=0;desc=
   Tconstr(option,[{id=3369;level=3;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=3365;level=3;scope=0;desc=
   Tarrow("",{id=3367;level=3;scope=0;desc=Tconstr(string,[],[])},
    {id=1530;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},Cok)},Cok)}
{id=3363;level=3;scope=0;desc=Tvar None}
{id=3372;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=3367;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=3367;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=3367;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=1530;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=1530;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=1530;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=1530;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=1529;level=1;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=1434;level=1;scope=0;desc=Tvar None}
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
|}, Principal{|
{id=1528;level=3;scope=0;desc=
 Tarrow("",{id=1530;level=3;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},
  {id=1529;level=3;scope=0;desc=Tconstr(Parsetree.structure,[],[])},Cok)}
{id=1435;level=3;scope=0;desc=Tvar None}
{id=3373;level=4;scope=0;desc=
 Tarrow("?with_positions",
  {id=3377;level=4;scope=0;desc=
   Tconstr(option,[{id=3378;level=4;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=3374;level=4;scope=0;desc=
   Tarrow("",{id=3376;level=4;scope=0;desc=Tconstr(string,[],[])},
    {id=3375;level=4;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},Cok)},Cok)}
{id=3372;level=4;scope=0;desc=Tvar None}
{id=3399;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=3400;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=3400;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=3394;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=3393;level=3;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=3402;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=3402;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=2829;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=2828;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=1434;level=1;scope=0;desc=Tvar None}
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
{id=7990;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=7989;level=2;scope=0;desc=Tvar None}
{id=8036;level=2;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=7988;level=1;scope=0;desc=Tvar None}
{id=8037;level=2;scope=0;desc=Tconstr(bool,[],[])}
{id=8038;level=2;scope=0;desc=Tconstr(bool,[],[])}
{id=8036;level=1;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=8036;level=1;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=8036;level=1;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=8046;level=1;scope=0;desc=Tvar None}
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
|}, Principal{|
{id=7935;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=7934;level=2;scope=0;desc=Tvar None}
{id=7983;level=3;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=7933;level=1;scope=0;desc=Tvar None}
{id=7986;level=4;scope=0;desc=Tconstr(bool,[],[])}
{id=7985;level=4;scope=0;desc=Tconstr(bool,[],[])}
{id=7983;level=1;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=7983;level=1;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=7983;level=1;scope=0;desc=Tconstr(Parsetree.pattern,[],[])}
{id=7995;level=1;scope=0;desc=Tvar None}
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
{id=8708;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=8707;level=2;scope=0;desc=Tvar None}
{id=8785;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8786;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8706;level=1;scope=0;desc=Tvar None}
{id=8823;level=2;scope=0;desc=Tconstr(bool,[],[])}
{id=8824;level=2;scope=0;desc=Tconstr(bool,[],[])}
{id=8785;level=1;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8786;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8785;level=1;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8786;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8785;level=1;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8786;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8832;level=1;scope=0;desc=Tvar None}
val lref : Longident.t Asttypes.loc =
  {Asttypes.txt = Longident.Lident "ref";
   loc =
    {Location.loc_start =
      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 8};
     loc_end =
      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 11};
     loc_ghost = false}}
|}, Principal{|
{id=8641;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=8640;level=2;scope=0;desc=Tvar None}
{id=8720;level=3;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8721;level=3;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8639;level=1;scope=0;desc=Tvar None}
{id=8760;level=4;scope=0;desc=Tconstr(bool,[],[])}
{id=8759;level=4;scope=0;desc=Tconstr(bool,[],[])}
{id=8720;level=1;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8721;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8720;level=1;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8721;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8720;level=1;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=8721;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=8769;level=1;scope=0;desc=Tvar None}
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
{id=11656;level=2;scope=0;desc=
 Tarrow("?use",
  {id=11666;level=2;scope=0;desc=
   Tconstr(option,[{id=11667;level=2;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=11657;level=2;scope=0;desc=
   Tarrow("loc",{id=11665;level=2;scope=0;desc=Tconstr(Location.t,[],[])},
    {id=11658;level=2;scope=0;desc=
     Tarrow("",{id=11664;level=2;scope=0;desc=Tconstr(Longident.t,[],[])},
      {id=11659;level=2;scope=0;desc=
       Tarrow("",{id=11663;level=2;scope=0;desc=Tconstr(Env.t,[],[])},
        {id=11660;level=2;scope=0;desc=
         Ttuple
          [{id=11661;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
           {id=11662;level=2;scope=0;desc=
            Tconstr(Types.value_description,[],[])}]},Cok)},Cok)},Cok)},Cok)}
{id=9158;level=2;scope=0;desc=Tvar None}
{id=13307;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13308;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13306;level=2;scope=0;desc=Tvar None}
{id=13307;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13308;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13310;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,[{id=13311;level=2;scope=0;desc=Tvar None}],[])}
{id=11665;level=1;scope=0;desc=Tconstr(Location.t,[],[])}
{id=11665;level=1;scope=0;desc=Tconstr(Location.t,[],[])}
{id=11665;level=1;scope=0;desc=Tconstr(Location.t,[],[])}
{id=11665;level=1;scope=0;desc=Tconstr(Location.t,[],[])}
{id=13319;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13320;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13318;level=2;scope=0;desc=Tvar None}
{id=13319;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13320;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13322;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,[{id=13321;level=2;scope=0;desc=Tvar None}],[])}
{id=13320;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=11664;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=11664;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=11664;level=1;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=13330;level=3;scope=0;desc=
 Tarrow("",
  {id=13332;level=3;scope=0;desc=
   Tconstr(ref,[{id=13331;level=3;scope=0;desc=Tvar None}],[])},{id=13331},
  Cok)}
{id=13329;level=3;scope=0;desc=Tvar None}
{id=13762;level=3;scope=0;desc=
 Tconstr(ref,[{id=13763;level=3;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=13332;level=2;scope=0;desc=
 Tconstr(ref,[{id=13331;level=2;scope=0;desc=Tvar None}],[])}
{id=13332;level=2;scope=0;desc=
 Tconstr(ref,[{id=13763;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=13332;level=2;scope=0;desc=
 Tconstr(ref,[{id=13763;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=13763;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=11663;level=1;scope=0;desc=Tconstr(Env.t,[],[])}
{id=11663;level=1;scope=0;desc=Tconstr(Env.t,[],[])}
{id=11663;level=1;scope=0;desc=Tconstr(Env.t,[],[])}
{id=11660;level=1;scope=0;desc=
 Ttuple
  [{id=11661;level=1;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=11662;level=1;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=9157;level=1;scope=0;desc=Tvar None}
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
|}, Principal{|
{id=11602;level=3;scope=0;desc=
 Tarrow("?use",
  {id=11612;level=3;scope=0;desc=
   Tconstr(option,[{id=11613;level=3;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=11603;level=3;scope=0;desc=
   Tarrow("loc",{id=11611;level=3;scope=0;desc=Tconstr(Location.t,[],[])},
    {id=11604;level=3;scope=0;desc=
     Tarrow("",{id=11610;level=3;scope=0;desc=Tconstr(Longident.t,[],[])},
      {id=11605;level=3;scope=0;desc=
       Tarrow("",{id=11609;level=3;scope=0;desc=Tconstr(Env.t,[],[])},
        {id=11606;level=3;scope=0;desc=
         Ttuple
          [{id=11607;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
           {id=11608;level=3;scope=0;desc=
            Tconstr(Types.value_description,[],[])}]},Cok)},Cok)},Cok)},Cok)}
{id=9104;level=3;scope=0;desc=Tvar None}
{id=13279;level=3;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13280;level=3;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13278;level=3;scope=0;desc=Tvar None}
{id=13279;level=100000000;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13280;level=100000000;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13282;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,[{id=13283;level=2;scope=0;desc=Tvar None}],[])}
{id=13281;level=2;scope=0;desc=Tconstr(Location.t,[],[])}
{id=13290;level=2;scope=0;desc=Tconstr(Location.t,[],[])}
{id=13290;level=2;scope=0;desc=Tconstr(Location.t,[],[])}
{id=13271;level=2;scope=0;desc=Tconstr(Location.t,[],[])}
{id=13292;level=3;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13293;level=3;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13291;level=3;scope=0;desc=Tvar None}
{id=13292;level=100000000;scope=0;desc=
 Tconstr(Asttypes.loc,
  [{id=13293;level=100000000;scope=0;desc=Tconstr(Longident.t,[],[])}],[])}
{id=13295;level=2;scope=0;desc=
 Tconstr(Asttypes.loc,[{id=13294;level=2;scope=0;desc=Tvar None}],[])}
{id=13293;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=13302;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=13302;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=13270;level=2;scope=0;desc=Tconstr(Longident.t,[],[])}
{id=13304;level=4;scope=0;desc=
 Tarrow("",
  {id=13306;level=4;scope=0;desc=
   Tconstr(ref,[{id=13305;level=4;scope=0;desc=Tvar None}],[])},{id=13305},
  Cok)}
{id=13303;level=4;scope=0;desc=Tvar None}
{id=13740;level=3;scope=0;desc=
 Tconstr(ref,[{id=13741;level=3;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=13742;level=3;scope=0;desc=
 Tconstr(ref,[{id=13305;level=2;scope=0;desc=Tvar None}],[])}
{id=13742;level=3;scope=0;desc=
 Tconstr(ref,[{id=13741;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=13311;level=3;scope=0;desc=
 Tconstr(ref,[{id=13741;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=13741;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=13744;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=13744;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=13269;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=13266;level=2;scope=0;desc=
 Ttuple
  [{id=13267;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=13268;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=9103;level=1;scope=0;desc=Tvar None}
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
{id=18309;level=2;scope=0;desc=
 Tarrow("?paren",
  {id=18313;level=2;scope=0;desc=
   Tconstr(option,
    [{id=18314;level=2;scope=0;desc=
      Tarrow("",{id=18316;level=2;scope=0;desc=Tconstr(string,[],[])},
       {id=18315;level=2;scope=0;desc=Tconstr(bool,[],[])},Cok)}],[])},
  {id=18310;level=2;scope=0;desc=
   Tarrow("",{id=18312;level=2;scope=0;desc=Tconstr(Path.t,[],[])},
    {id=18311;level=2;scope=0;desc=Tconstr(string,[],[])},Cok)},Cok)}
{id=18308;level=2;scope=0;desc=Tvar None}
{id=18949;level=3;scope=0;desc=
 Tarrow("",
  {id=18951;level=3;scope=0;desc=
   Ttuple
    [{id=18950;level=3;scope=0;desc=Tvar None};
     {id=18952;level=3;scope=0;desc=Tvar None}]},{id=18950},Cok)}
{id=18948;level=3;scope=0;desc=Tvar None}
{id=18954;level=3;scope=0;desc=
 Ttuple
  [{id=18955;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=18956;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=18951;level=2;scope=0;desc=
 Ttuple
  [{id=18950;level=2;scope=0;desc=Tvar None};
   {id=18952;level=2;scope=0;desc=Tvar None}]}
{id=18951;level=2;scope=0;desc=
 Ttuple
  [{id=18955;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=18956;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=18951;level=2;scope=0;desc=
 Ttuple
  [{id=18955;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=18956;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=18955;level=2;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18312;level=1;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18312;level=1;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18312;level=1;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18311;level=1;scope=0;desc=Tconstr(string,[],[])}
{id=18307;level=1;scope=0;desc=Tvar None}
val ref_path_name : string = "Stdlib.ref"
|}, Principal{|
{id=18278;level=3;scope=0;desc=
 Tarrow("?paren",
  {id=18282;level=3;scope=0;desc=
   Tconstr(option,
    [{id=18283;level=3;scope=0;desc=
      Tarrow("",{id=18285;level=3;scope=0;desc=Tconstr(string,[],[])},
       {id=18284;level=3;scope=0;desc=Tconstr(bool,[],[])},Cok)}],[])},
  {id=18279;level=3;scope=0;desc=
   Tarrow("",{id=18281;level=3;scope=0;desc=Tconstr(Path.t,[],[])},
    {id=18280;level=3;scope=0;desc=Tconstr(string,[],[])},Cok)},Cok)}
{id=18277;level=3;scope=0;desc=Tvar None}
{id=18938;level=4;scope=0;desc=
 Tarrow("",
  {id=18940;level=4;scope=0;desc=
   Ttuple
    [{id=18939;level=4;scope=0;desc=Tvar None};
     {id=18941;level=4;scope=0;desc=Tvar None}]},{id=18939},Cok)}
{id=18937;level=4;scope=0;desc=Tvar None}
{id=18947;level=3;scope=0;desc=
 Ttuple
  [{id=18948;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=18949;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=18950;level=3;scope=0;desc=
 Ttuple
  [{id=18939;level=2;scope=0;desc=Tvar None};
   {id=18941;level=2;scope=0;desc=Tvar None}]}
{id=18950;level=3;scope=0;desc=
 Ttuple
  [{id=18948;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=18949;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=18946;level=3;scope=0;desc=
 Ttuple
  [{id=18948;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=18949;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=18948;level=2;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18952;level=2;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18952;level=2;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18928;level=2;scope=0;desc=Tconstr(Path.t,[],[])}
{id=18927;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=18276;level=1;scope=0;desc=Tvar None}
val ref_path_name : string = "Stdlib.ref"
|}];;

Format.printf "%a" !Btype.print_raw (snd ref_lookedup).val_type;;
[%%expect{|
{id=20667;level=2;scope=0;desc=
 Tarrow("",
  {id=20669;level=2;scope=0;desc=
   Tconstr(format,
    [{id=20668;level=2;scope=0;desc=Tvar None};
     {id=20670;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])};
     {id=20671;level=2;scope=0;desc=Tconstr(unit,[],[])}],[])},{id=20668},
  Cok)}
{id=18986;level=2;scope=0;desc=Tvar None}
{id=21985;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.format6,
  [{id=21986;level=2;scope=0;desc=Tvar None};
   {id=21987;level=2;scope=0;desc=Tvar None};
   {id=21988;level=2;scope=0;desc=Tvar None};
   {id=21989;level=2;scope=0;desc=Tvar None};
   {id=21990;level=2;scope=0;desc=Tvar None};
   {id=21991;level=2;scope=0;desc=Tvar None}],[])}
{id=20669;level=1;scope=0;desc=
 Tconstr(format,
  [{id=20675;level=1;scope=0;desc=
    Tarrow("",{id=20673;level=1;scope=0;desc=Tvar None},
     {id=20678;level=1;scope=0;desc=
      Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
       {id=20677;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])}],[format])}
{id=22885;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=22886;level=2;scope=0;desc=
    Tarrow("",
     {id=22890;level=2;scope=0;desc=
      Tarrow("",{id=22893;level=2;scope=0;desc=Tvar None},
       {id=22891;level=2;scope=0;desc=
        Tarrow("",{id=22889;level=2;scope=0;desc=Tvar None},
         {id=22892;level=2;scope=0;desc=Tvar None},Cok)},Cok)},
     {id=22887;level=2;scope=0;desc=
      Tarrow("",{id=22889},{id=22888;level=2;scope=0;desc=Tvar None},Cok)},
     Cok)};
   {id=22893};{id=22892};{id=22894;level=2;scope=0;desc=Tvar None};
   {id=22895;level=2;scope=0;desc=Tvar None};
   {id=22896;level=2;scope=0;desc=Tvar None}],[])}
{id=21992;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20675;level=1;scope=0;desc=
    Tarrow("",{id=20673;level=1;scope=0;desc=Tvar None},
     {id=20678;level=1;scope=0;desc=
      Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
       {id=20677;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])};{id=20671};{id=20671};
   {id=20671}],[])}
{id=22898;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=22899;level=2;scope=0;desc=Tvar None};
   {id=22900;level=2;scope=0;desc=Tvar None};
   {id=22901;level=2;scope=0;desc=Tvar None};
   {id=22902;level=2;scope=0;desc=Tvar None};{id=22902};{id=22899}],[])}
{id=22897;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20677;level=1;scope=0;desc=Tvar None};
   {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])};{id=20671};{id=20671};
   {id=20671}],[])}
{id=22897;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=20671};{id=20671};{id=20671};{id=20671}],[])}
{id=22897;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=20671};{id=20671};{id=20671};{id=20671}],[])}
{id=21992;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20675;level=1;scope=0;desc=
    Tarrow("",
     {id=22890;level=1;scope=0;desc=
      Tarrow("",
       {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22891;level=1;scope=0;desc=
        Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
         {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=20678;level=1;scope=0;desc=Tarrow("",{id=20676},{id=20671},Cok)},
     Cok)};
   {id=20670};{id=20671};{id=20671};{id=20671};{id=20671}],[])}
{id=21992;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20675;level=1;scope=0;desc=
    Tarrow("",
     {id=22890;level=1;scope=0;desc=
      Tarrow("",
       {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22891;level=1;scope=0;desc=
        Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
         {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=20678;level=1;scope=0;desc=Tarrow("",{id=20676},{id=20671},Cok)},
     Cok)};
   {id=20670};{id=20671};{id=20671};{id=20671};{id=20671}],[])}
{id=22903;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=21993;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=21993;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=21993;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=20669;level=1;scope=0;desc=
 Tconstr(format,
  [{id=20675;level=1;scope=0;desc=
    Tarrow("",
     {id=22890;level=1;scope=0;desc=
      Tarrow("",
       {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22891;level=1;scope=0;desc=
        Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
         {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=20678;level=1;scope=0;desc=Tarrow("",{id=20676},{id=20671},Cok)},
     Cok)};
   {id=20670};{id=20671}],[format])}
{id=20669;level=1;scope=0;desc=
 Tconstr(format,
  [{id=20675;level=1;scope=0;desc=
    Tarrow("",
     {id=22890;level=1;scope=0;desc=
      Tarrow("",
       {id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22891;level=1;scope=0;desc=
        Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
         {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=20678;level=1;scope=0;desc=Tarrow("",{id=20676},{id=20671},Cok)},
     Cok)};
   {id=20670};{id=20671}],[format])}
{id=22905;level=3;scope=0;desc=
 Tarrow("",
  {id=22907;level=3;scope=0;desc=
   Tconstr(ref,[{id=22906;level=3;scope=0;desc=Tvar None}],[])},{id=22906},
  Cok)}
{id=22904;level=3;scope=0;desc=Tvar None}
{id=23699;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=23700;level=3;scope=0;desc=
    Tarrow("",
     {id=23704;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=23701;level=3;scope=0;desc=
      Tarrow("",
       {id=23703;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=23702;level=3;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=22907;level=2;scope=0;desc=
 Tconstr(ref,[{id=22906;level=2;scope=0;desc=Tvar None}],[])}
{id=22907;level=2;scope=0;desc=
 Tconstr(ref,
  [{id=23700;level=2;scope=0;desc=
    Tarrow("",
     {id=23704;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=23701;level=2;scope=0;desc=
      Tarrow("",
       {id=23703;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=23702;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=22907;level=2;scope=0;desc=
 Tconstr(ref,
  [{id=23700;level=2;scope=0;desc=
    Tarrow("",
     {id=23704;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=23701;level=2;scope=0;desc=
      Tarrow("",
       {id=23703;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=23702;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=23700;level=2;scope=0;desc=
 Tarrow("",{id=23704;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=23701;level=2;scope=0;desc=
   Tarrow("",{id=23703;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=23702;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=22890;level=1;scope=0;desc=
 Tarrow("",{id=20670;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=22891;level=1;scope=0;desc=
   Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
    {id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=23708;level=3;scope=0;desc=
 Tarrow("",
  {id=23710;level=3;scope=0;desc=
   Ttuple
    [{id=23711;level=3;scope=0;desc=Tvar None};
     {id=23709;level=3;scope=0;desc=Tvar None}]},{id=23709},Cok)}
{id=23707;level=3;scope=0;desc=Tvar None}
{id=23713;level=3;scope=0;desc=
 Ttuple
  [{id=23714;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=23715;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=23710;level=2;scope=0;desc=
 Ttuple
  [{id=23711;level=2;scope=0;desc=Tvar None};
   {id=23709;level=2;scope=0;desc=Tvar None}]}
{id=23710;level=2;scope=0;desc=
 Ttuple
  [{id=23714;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=23715;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=23710;level=2;scope=0;desc=
 Ttuple
  [{id=23714;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=23715;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=23715;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=23706;level=2;scope=0;desc=Tvar None}
{id=23715;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=23718;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=23717;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=23703;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=20671;level=1;scope=0;desc=Tconstr(unit,[],[])}
{id=18985;level=1;scope=0;desc=Tvar None}
{id=1377;level=100000000;scope=0;desc=
 Tarrow("",{id=135;level=100000000;scope=0;desc=Tvar "a"},
  {id=1378;level=100000000;scope=0;desc=Tconstr(ref,[{id=135}],[])},Cok)}- : unit = ()
|}, Principal{|
{id=20662;level=3;scope=0;desc=
 Tarrow("",
  {id=20664;level=3;scope=0;desc=
   Tconstr(format,
    [{id=20663;level=3;scope=0;desc=Tvar None};
     {id=20665;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])};
     {id=20666;level=3;scope=0;desc=Tconstr(unit,[],[])}],[])},{id=20663},
  Cok)}
{id=18981;level=3;scope=0;desc=Tvar None}
{id=22000;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.format6,
  [{id=21989;level=3;scope=0;desc=Tvar None};
   {id=21990;level=3;scope=0;desc=Tvar None};
   {id=21991;level=3;scope=0;desc=Tvar None};
   {id=21992;level=3;scope=0;desc=Tvar None};
   {id=21993;level=3;scope=0;desc=Tvar None};
   {id=21994;level=3;scope=0;desc=Tvar None}],[])}
{id=21997;level=3;scope=0;desc=
 Tconstr(format,
  [{id=20678;level=1;scope=0;desc=
    Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
     {id=20681;level=1;scope=0;desc=
      Tarrow("",{id=20679;level=1;scope=0;desc=Tvar None},
       {id=20680;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=21998;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=21999;level=3;scope=0;desc=Tconstr(unit,[],[])}],[])}
{id=22932;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=22933;level=3;scope=0;desc=
    Tarrow("",
     {id=22935;level=3;scope=0;desc=
      Tarrow("",{id=22924;level=3;scope=0;desc=Tvar None},
       {id=22936;level=3;scope=0;desc=
        Tarrow("",{id=22920;level=3;scope=0;desc=Tvar None},
         {id=22923;level=3;scope=0;desc=Tvar None},Cok)},Cok)},
     {id=22934;level=3;scope=0;desc=
      Tarrow("",{id=22920},{id=22919;level=3;scope=0;desc=Tvar None},Cok)},
     Cok)};
   {id=22924};{id=22923};{id=22925;level=3;scope=0;desc=Tvar None};
   {id=22926;level=3;scope=0;desc=Tvar None};
   {id=22927;level=3;scope=0;desc=Tvar None}],[])}
{id=22929;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20678;level=1;scope=0;desc=
    Tarrow("",{id=20676;level=1;scope=0;desc=Tvar None},
     {id=20681;level=1;scope=0;desc=
      Tarrow("",{id=20679;level=1;scope=0;desc=Tvar None},
       {id=20680;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=22930;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=22931;level=3;scope=0;desc=Tconstr(unit,[],[])};{id=22931};{id=22931};
   {id=22931}],[])}
{id=22949;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=22944;level=3;scope=0;desc=Tvar None};
   {id=22945;level=3;scope=0;desc=Tvar None};
   {id=22946;level=3;scope=0;desc=Tvar None};
   {id=22947;level=3;scope=0;desc=Tvar None};{id=22947};{id=22944}],[])}
{id=22948;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20680;level=1;scope=0;desc=Tvar None};
   {id=22930;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=22931;level=1;scope=0;desc=Tconstr(unit,[],[])};{id=22931};{id=22931};
   {id=22931}],[])}
{id=22950;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=22931;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=22930;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=22931};{id=22931};{id=22931};{id=22931}],[])}
{id=22942;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=22931;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=22930;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=22931};{id=22931};{id=22931};{id=22931}],[])}
{id=22937;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=22938;level=2;scope=0;desc=
    Tarrow("",
     {id=22940;level=2;scope=0;desc=
      Tarrow("",
       {id=22930;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22941;level=2;scope=0;desc=
        Tarrow("",{id=20679;level=1;scope=0;desc=Tvar None},
         {id=22931;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=22939;level=2;scope=0;desc=Tarrow("",{id=20679},{id=22931},Cok)},
     Cok)};
   {id=22930};{id=22931};{id=22931};{id=22931};{id=22931}],[])}
{id=22914;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=20678;level=1;scope=0;desc=
    Tarrow("",
     {id=22935;level=1;scope=0;desc=
      Tarrow("",
       {id=22930;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22936;level=1;scope=0;desc=
        Tarrow("",{id=20679;level=1;scope=0;desc=Tvar None},
         {id=22931;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=20681;level=1;scope=0;desc=Tarrow("",{id=20679},{id=22931},Cok)},
     Cok)};
   {id=22912;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=22913;level=2;scope=0;desc=Tconstr(unit,[],[])};{id=22913};{id=22913};
   {id=22913}],[])}
{id=22951;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=22952;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=22952;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=22915;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=22911;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.format6,
  [{id=20678;level=1;scope=0;desc=
    Tarrow("",
     {id=22935;level=1;scope=0;desc=
      Tarrow("",
       {id=22912;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22936;level=1;scope=0;desc=
        Tarrow("",{id=20679;level=1;scope=0;desc=Tvar None},
         {id=22913;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=20681;level=1;scope=0;desc=Tarrow("",{id=20679},{id=22913},Cok)},
     Cok)};
   {id=22912};{id=22913};{id=22913};{id=22913};{id=22913}],[])}
{id=20673;level=2;scope=0;desc=
 Tconstr(format,
  [{id=20678;level=1;scope=0;desc=
    Tarrow("",
     {id=22935;level=1;scope=0;desc=
      Tarrow("",
       {id=22912;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=22936;level=1;scope=0;desc=
        Tarrow("",{id=20679;level=1;scope=0;desc=Tvar None},
         {id=22913;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=20681;level=1;scope=0;desc=Tarrow("",{id=20679},{id=22913},Cok)},
     Cok)};
   {id=20674;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=20675;level=2;scope=0;desc=Tconstr(unit,[],[])}],[])}
{id=22973;level=4;scope=0;desc=
 Tarrow("",
  {id=22975;level=4;scope=0;desc=
   Tconstr(ref,[{id=22974;level=4;scope=0;desc=Tvar None}],[])},{id=22974},
  Cok)}
{id=22972;level=4;scope=0;desc=Tvar None}
{id=23771;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=23772;level=3;scope=0;desc=
    Tarrow("",
     {id=23776;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=23773;level=3;scope=0;desc=
      Tarrow("",
       {id=23775;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=23774;level=3;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=23777;level=3;scope=0;desc=
 Tconstr(ref,[{id=22974;level=2;scope=0;desc=Tvar None}],[])}
{id=23777;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=23772;level=2;scope=0;desc=
    Tarrow("",
     {id=23776;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=23773;level=2;scope=0;desc=
      Tarrow("",
       {id=23775;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=23774;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=22980;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=23772;level=2;scope=0;desc=
    Tarrow("",
     {id=23776;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=23773;level=2;scope=0;desc=
      Tarrow("",
       {id=23775;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=23774;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=23772;level=2;scope=0;desc=
 Tarrow("",{id=23776;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=23773;level=2;scope=0;desc=
   Tarrow("",{id=23775;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=23774;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=22935;level=1;scope=0;desc=
 Tarrow("",{id=20674;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=22936;level=1;scope=0;desc=
   Tarrow("",{id=20679;level=1;scope=0;desc=Tvar None},
    {id=20675;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=23781;level=5;scope=0;desc=
 Tarrow("",
  {id=23783;level=5;scope=0;desc=
   Ttuple
    [{id=23784;level=5;scope=0;desc=Tvar None};
     {id=23782;level=5;scope=0;desc=Tvar None}]},{id=23782},Cok)}
{id=23780;level=5;scope=0;desc=Tvar None}
{id=23790;level=4;scope=0;desc=
 Ttuple
  [{id=23791;level=4;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=23792;level=4;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=23793;level=4;scope=0;desc=
 Ttuple
  [{id=23784;level=3;scope=0;desc=Tvar None};
   {id=23782;level=3;scope=0;desc=Tvar None}]}
{id=23793;level=4;scope=0;desc=
 Ttuple
  [{id=23791;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=23792;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=23789;level=4;scope=0;desc=
 Ttuple
  [{id=23791;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=23792;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=23792;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=23779;level=3;scope=0;desc=Tvar None}
{id=23792;level=100000000;scope=0;desc=
 Tconstr(Types.value_description,[],[])}
{id=23796;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=23795;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=23775;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=20675;level=1;scope=0;desc=Tconstr(unit,[],[])}
{id=18980;level=1;scope=0;desc=Tvar None}
{id=1377;level=100000000;scope=0;desc=
 Tarrow("",{id=135;level=100000000;scope=0;desc=Tvar "a"},
  {id=1378;level=100000000;scope=0;desc=Tconstr(ref,[{id=135}],[])},Cok)}- : unit = ()
|}];;

let ref_instance = (Ctype.instance (snd ref_lookedup).val_type);;
[%%expect{|
{id=25513;level=2;scope=0;desc=
 Tarrow("?partial",
  {id=25517;level=2;scope=0;desc=
   Tconstr(option,[{id=25518;level=2;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=25514;level=2;scope=0;desc=
   Tarrow("",{id=25516;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25515;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},Cok)},Cok)}
{id=23755;level=2;scope=0;desc=Tvar None}
{id=25523;level=3;scope=0;desc=
 Tarrow("",
  {id=25525;level=3;scope=0;desc=
   Ttuple
    [{id=25526;level=3;scope=0;desc=Tvar None};
     {id=25524;level=3;scope=0;desc=Tvar None}]},{id=25524},Cok)}
{id=25522;level=3;scope=0;desc=Tvar None}
{id=25528;level=3;scope=0;desc=
 Ttuple
  [{id=25529;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25530;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25525;level=2;scope=0;desc=
 Ttuple
  [{id=25526;level=2;scope=0;desc=Tvar None};
   {id=25524;level=2;scope=0;desc=Tvar None}]}
{id=25525;level=2;scope=0;desc=
 Ttuple
  [{id=25529;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25530;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25525;level=2;scope=0;desc=
 Ttuple
  [{id=25529;level=2;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25530;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25530;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25521;level=2;scope=0;desc=Tvar None}
{id=25530;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25533;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25532;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25516;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25516;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25516;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25515;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=23754;level=1;scope=0;desc=Tvar None}
val ref_instance : Types.type_expr = <abstr>
|}, Principal{|
{id=25591;level=3;scope=0;desc=
 Tarrow("?partial",
  {id=25595;level=3;scope=0;desc=
   Tconstr(option,[{id=25596;level=3;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=25592;level=3;scope=0;desc=
   Tarrow("",{id=25594;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25593;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},Cok)},Cok)}
{id=23833;level=3;scope=0;desc=Tvar None}
{id=25615;level=5;scope=0;desc=
 Tarrow("",
  {id=25617;level=5;scope=0;desc=
   Ttuple
    [{id=25618;level=5;scope=0;desc=Tvar None};
     {id=25616;level=5;scope=0;desc=Tvar None}]},{id=25616},Cok)}
{id=25614;level=5;scope=0;desc=Tvar None}
{id=25624;level=4;scope=0;desc=
 Ttuple
  [{id=25625;level=4;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25626;level=4;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25627;level=4;scope=0;desc=
 Ttuple
  [{id=25618;level=3;scope=0;desc=Tvar None};
   {id=25616;level=3;scope=0;desc=Tvar None}]}
{id=25627;level=4;scope=0;desc=
 Ttuple
  [{id=25625;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25626;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25623;level=4;scope=0;desc=
 Ttuple
  [{id=25625;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25626;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25626;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25613;level=3;scope=0;desc=Tvar None}
{id=25626;level=100000000;scope=0;desc=
 Tconstr(Types.value_description,[],[])}
{id=25630;level=2;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25629;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25631;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25631;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25608;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25607;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=23832;level=1;scope=0;desc=Tvar None}
val ref_instance : Types.type_expr = <abstr>
|}];;

Format.printf "%a" !Btype.print_raw ref_instance;;
[%%expect{|
{id=25567;level=2;scope=0;desc=
 Tarrow("",
  {id=25569;level=2;scope=0;desc=
   Tconstr(format,
    [{id=25568;level=2;scope=0;desc=Tvar None};
     {id=25570;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])};
     {id=25571;level=2;scope=0;desc=Tconstr(unit,[],[])}],[])},{id=25568},
  Cok)}
{id=25566;level=2;scope=0;desc=Tvar None}
{id=25598;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.format6,
  [{id=25599;level=2;scope=0;desc=Tvar None};
   {id=25600;level=2;scope=0;desc=Tvar None};
   {id=25601;level=2;scope=0;desc=Tvar None};
   {id=25602;level=2;scope=0;desc=Tvar None};
   {id=25603;level=2;scope=0;desc=Tvar None};
   {id=25604;level=2;scope=0;desc=Tvar None}],[])}
{id=25569;level=1;scope=0;desc=
 Tconstr(format,
  [{id=25575;level=1;scope=0;desc=
    Tarrow("",{id=25573;level=1;scope=0;desc=Tvar None},
     {id=25578;level=1;scope=0;desc=
      Tarrow("",{id=25576;level=1;scope=0;desc=Tvar None},
       {id=25577;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])}],[format])}
{id=25607;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25608;level=2;scope=0;desc=
    Tarrow("",
     {id=25612;level=2;scope=0;desc=
      Tarrow("",{id=25615;level=2;scope=0;desc=Tvar None},
       {id=25613;level=2;scope=0;desc=
        Tarrow("",{id=25611;level=2;scope=0;desc=Tvar None},
         {id=25614;level=2;scope=0;desc=Tvar None},Cok)},Cok)},
     {id=25609;level=2;scope=0;desc=
      Tarrow("",{id=25611},{id=25610;level=2;scope=0;desc=Tvar None},Cok)},
     Cok)};
   {id=25615};{id=25614};{id=25616;level=2;scope=0;desc=Tvar None};
   {id=25617;level=2;scope=0;desc=Tvar None};
   {id=25618;level=2;scope=0;desc=Tvar None}],[])}
{id=25605;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25575;level=1;scope=0;desc=
    Tarrow("",{id=25573;level=1;scope=0;desc=Tvar None},
     {id=25578;level=1;scope=0;desc=
      Tarrow("",{id=25576;level=1;scope=0;desc=Tvar None},
       {id=25577;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])};{id=25571};{id=25571};
   {id=25571}],[])}
{id=25620;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25621;level=2;scope=0;desc=Tvar None};
   {id=25622;level=2;scope=0;desc=Tvar None};
   {id=25623;level=2;scope=0;desc=Tvar None};
   {id=25624;level=2;scope=0;desc=Tvar None};{id=25624};{id=25621}],[])}
{id=25619;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25577;level=1;scope=0;desc=Tvar None};
   {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])};{id=25571};{id=25571};
   {id=25571}],[])}
{id=25619;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25571};{id=25571};{id=25571};{id=25571}],[])}
{id=25619;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25571};{id=25571};{id=25571};{id=25571}],[])}
{id=25605;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25575;level=1;scope=0;desc=
    Tarrow("",
     {id=25612;level=1;scope=0;desc=
      Tarrow("",
       {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25613;level=1;scope=0;desc=
        Tarrow("",{id=25576;level=1;scope=0;desc=Tvar None},
         {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25578;level=1;scope=0;desc=Tarrow("",{id=25576},{id=25571},Cok)},
     Cok)};
   {id=25570};{id=25571};{id=25571};{id=25571};{id=25571}],[])}
{id=25605;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25575;level=1;scope=0;desc=
    Tarrow("",
     {id=25612;level=1;scope=0;desc=
      Tarrow("",
       {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25613;level=1;scope=0;desc=
        Tarrow("",{id=25576;level=1;scope=0;desc=Tvar None},
         {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25578;level=1;scope=0;desc=Tarrow("",{id=25576},{id=25571},Cok)},
     Cok)};
   {id=25570};{id=25571};{id=25571};{id=25571};{id=25571}],[])}
{id=25625;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25606;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25606;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25606;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25569;level=1;scope=0;desc=
 Tconstr(format,
  [{id=25575;level=1;scope=0;desc=
    Tarrow("",
     {id=25612;level=1;scope=0;desc=
      Tarrow("",
       {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25613;level=1;scope=0;desc=
        Tarrow("",{id=25576;level=1;scope=0;desc=Tvar None},
         {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25578;level=1;scope=0;desc=Tarrow("",{id=25576},{id=25571},Cok)},
     Cok)};
   {id=25570};{id=25571}],[format])}
{id=25569;level=1;scope=0;desc=
 Tconstr(format,
  [{id=25575;level=1;scope=0;desc=
    Tarrow("",
     {id=25612;level=1;scope=0;desc=
      Tarrow("",
       {id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25613;level=1;scope=0;desc=
        Tarrow("",{id=25576;level=1;scope=0;desc=Tvar None},
         {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25578;level=1;scope=0;desc=Tarrow("",{id=25576},{id=25571},Cok)},
     Cok)};
   {id=25570};{id=25571}],[format])}
{id=25627;level=3;scope=0;desc=
 Tarrow("",
  {id=25629;level=3;scope=0;desc=
   Tconstr(ref,[{id=25628;level=3;scope=0;desc=Tvar None}],[])},{id=25628},
  Cok)}
{id=25626;level=3;scope=0;desc=Tvar None}
{id=25631;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=25632;level=3;scope=0;desc=
    Tarrow("",
     {id=25636;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=25633;level=3;scope=0;desc=
      Tarrow("",
       {id=25635;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=25634;level=3;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=25629;level=2;scope=0;desc=
 Tconstr(ref,[{id=25628;level=2;scope=0;desc=Tvar None}],[])}
{id=25629;level=2;scope=0;desc=
 Tconstr(ref,
  [{id=25632;level=2;scope=0;desc=
    Tarrow("",
     {id=25636;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=25633;level=2;scope=0;desc=
      Tarrow("",
       {id=25635;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=25634;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=25629;level=2;scope=0;desc=
 Tconstr(ref,
  [{id=25632;level=2;scope=0;desc=
    Tarrow("",
     {id=25636;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=25633;level=2;scope=0;desc=
      Tarrow("",
       {id=25635;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=25634;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=25632;level=2;scope=0;desc=
 Tarrow("",{id=25636;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=25633;level=2;scope=0;desc=
   Tarrow("",{id=25635;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25634;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=25612;level=1;scope=0;desc=
 Tarrow("",{id=25570;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=25613;level=1;scope=0;desc=
   Tarrow("",{id=25576;level=1;scope=0;desc=Tvar None},
    {id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=25638;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25635;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25571;level=1;scope=0;desc=Tconstr(unit,[],[])}
{id=25565;level=1;scope=0;desc=Tvar None}

{id=25543;level=0;scope=0;desc=
 Tarrow("",{id=25545;level=0;scope=0;desc=Tvar None},
  {id=25544;level=0;scope=0;desc=Tconstr(ref,[{id=25545}],[])},Cok)}- : unit = ()
|}, Principal{|
{id=25665;level=3;scope=0;desc=
 Tarrow("",
  {id=25667;level=3;scope=0;desc=
   Tconstr(format,
    [{id=25666;level=3;scope=0;desc=Tvar None};
     {id=25668;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])};
     {id=25669;level=3;scope=0;desc=Tconstr(unit,[],[])}],[])},{id=25666},
  Cok)}
{id=25664;level=3;scope=0;desc=Tvar None}
{id=25716;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.format6,
  [{id=25705;level=3;scope=0;desc=Tvar None};
   {id=25706;level=3;scope=0;desc=Tvar None};
   {id=25707;level=3;scope=0;desc=Tvar None};
   {id=25708;level=3;scope=0;desc=Tvar None};
   {id=25709;level=3;scope=0;desc=Tvar None};
   {id=25710;level=3;scope=0;desc=Tvar None}],[])}
{id=25713;level=3;scope=0;desc=
 Tconstr(format,
  [{id=25681;level=1;scope=0;desc=
    Tarrow("",{id=25679;level=1;scope=0;desc=Tvar None},
     {id=25684;level=1;scope=0;desc=
      Tarrow("",{id=25682;level=1;scope=0;desc=Tvar None},
       {id=25683;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=25714;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25715;level=3;scope=0;desc=Tconstr(unit,[],[])}],[])}
{id=25757;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25758;level=3;scope=0;desc=
    Tarrow("",
     {id=25760;level=3;scope=0;desc=
      Tarrow("",{id=25749;level=3;scope=0;desc=Tvar None},
       {id=25761;level=3;scope=0;desc=
        Tarrow("",{id=25745;level=3;scope=0;desc=Tvar None},
         {id=25748;level=3;scope=0;desc=Tvar None},Cok)},Cok)},
     {id=25759;level=3;scope=0;desc=
      Tarrow("",{id=25745},{id=25744;level=3;scope=0;desc=Tvar None},Cok)},
     Cok)};
   {id=25749};{id=25748};{id=25750;level=3;scope=0;desc=Tvar None};
   {id=25751;level=3;scope=0;desc=Tvar None};
   {id=25752;level=3;scope=0;desc=Tvar None}],[])}
{id=25754;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25681;level=1;scope=0;desc=
    Tarrow("",{id=25679;level=1;scope=0;desc=Tvar None},
     {id=25684;level=1;scope=0;desc=
      Tarrow("",{id=25682;level=1;scope=0;desc=Tvar None},
       {id=25683;level=1;scope=0;desc=Tvar None},Cunknown)},Cunknown)};
   {id=25755;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25756;level=3;scope=0;desc=Tconstr(unit,[],[])};{id=25756};{id=25756};
   {id=25756}],[])}
{id=25774;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25769;level=3;scope=0;desc=Tvar None};
   {id=25770;level=3;scope=0;desc=Tvar None};
   {id=25771;level=3;scope=0;desc=Tvar None};
   {id=25772;level=3;scope=0;desc=Tvar None};{id=25772};{id=25769}],[])}
{id=25773;level=3;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25683;level=1;scope=0;desc=Tvar None};
   {id=25755;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25756;level=1;scope=0;desc=Tconstr(unit,[],[])};{id=25756};{id=25756};
   {id=25756}],[])}
{id=25775;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25756;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=25755;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25756};{id=25756};{id=25756};{id=25756}],[])}
{id=25767;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25756;level=1;scope=0;desc=Tconstr(unit,[],[])};
   {id=25755;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25756};{id=25756};{id=25756};{id=25756}],[])}
{id=25762;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25763;level=2;scope=0;desc=
    Tarrow("",
     {id=25765;level=2;scope=0;desc=
      Tarrow("",
       {id=25755;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25766;level=2;scope=0;desc=
        Tarrow("",{id=25682;level=1;scope=0;desc=Tvar None},
         {id=25756;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25764;level=2;scope=0;desc=Tarrow("",{id=25682},{id=25756},Cok)},
     Cok)};
   {id=25755};{id=25756};{id=25756};{id=25756};{id=25756}],[])}
{id=25739;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.fmt,
  [{id=25681;level=1;scope=0;desc=
    Tarrow("",
     {id=25760;level=1;scope=0;desc=
      Tarrow("",
       {id=25755;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25761;level=1;scope=0;desc=
        Tarrow("",{id=25682;level=1;scope=0;desc=Tvar None},
         {id=25756;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25684;level=1;scope=0;desc=Tarrow("",{id=25682},{id=25756},Cok)},
     Cok)};
   {id=25737;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25738;level=2;scope=0;desc=Tconstr(unit,[],[])};{id=25738};{id=25738};
   {id=25738}],[])}
{id=25776;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25777;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25777;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25740;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25736;level=2;scope=0;desc=
 Tconstr(CamlinternalFormatBasics.format6,
  [{id=25681;level=1;scope=0;desc=
    Tarrow("",
     {id=25760;level=1;scope=0;desc=
      Tarrow("",
       {id=25737;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25761;level=1;scope=0;desc=
        Tarrow("",{id=25682;level=1;scope=0;desc=Tvar None},
         {id=25738;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25684;level=1;scope=0;desc=Tarrow("",{id=25682},{id=25738},Cok)},
     Cok)};
   {id=25737};{id=25738};{id=25738};{id=25738};{id=25738}],[])}
{id=25676;level=2;scope=0;desc=
 Tconstr(format,
  [{id=25681;level=1;scope=0;desc=
    Tarrow("",
     {id=25760;level=1;scope=0;desc=
      Tarrow("",
       {id=25737;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
       {id=25761;level=1;scope=0;desc=
        Tarrow("",{id=25682;level=1;scope=0;desc=Tvar None},
         {id=25738;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)},
     {id=25684;level=1;scope=0;desc=Tarrow("",{id=25682},{id=25738},Cok)},
     Cok)};
   {id=25677;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])};
   {id=25678;level=2;scope=0;desc=Tconstr(unit,[],[])}],[])}
{id=25798;level=4;scope=0;desc=
 Tarrow("",
  {id=25800;level=4;scope=0;desc=
   Tconstr(ref,[{id=25799;level=4;scope=0;desc=Tvar None}],[])},{id=25799},
  Cok)}
{id=25797;level=4;scope=0;desc=Tvar None}
{id=25806;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=25807;level=3;scope=0;desc=
    Tarrow("",
     {id=25811;level=3;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=25808;level=3;scope=0;desc=
      Tarrow("",
       {id=25810;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=25809;level=3;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=25812;level=3;scope=0;desc=
 Tconstr(ref,[{id=25799;level=2;scope=0;desc=Tvar None}],[])}
{id=25812;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=25807;level=2;scope=0;desc=
    Tarrow("",
     {id=25811;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=25808;level=2;scope=0;desc=
      Tarrow("",
       {id=25810;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=25809;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=25805;level=3;scope=0;desc=
 Tconstr(ref,
  [{id=25807;level=2;scope=0;desc=
    Tarrow("",
     {id=25811;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
     {id=25808;level=2;scope=0;desc=
      Tarrow("",
       {id=25810;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
       {id=25809;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}],[])}
{id=25807;level=2;scope=0;desc=
 Tarrow("",{id=25811;level=2;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=25808;level=2;scope=0;desc=
   Tarrow("",{id=25810;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25809;level=2;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=25760;level=1;scope=0;desc=
 Tarrow("",{id=25677;level=1;scope=0;desc=Tconstr(Format.formatter,[],[])},
  {id=25761;level=1;scope=0;desc=
   Tarrow("",{id=25682;level=1;scope=0;desc=Tvar None},
    {id=25678;level=1;scope=0;desc=Tconstr(unit,[],[])},Cok)},Cok)}
{id=25814;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25810;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25678;level=1;scope=0;desc=Tconstr(unit,[],[])}
{id=25663;level=1;scope=0;desc=Tvar None}

{id=25641;level=0;scope=0;desc=
 Tarrow("",{id=25643;level=0;scope=0;desc=Tvar None},
  {id=25642;level=0;scope=0;desc=Tconstr(ref,[{id=25643}],[])},Cok)}- : unit = ()
|}];;

let var = Ctype.newvar ();;
[%%expect{|
{id=25673;level=2;scope=0;desc=
 Tarrow("?name",
  {id=25677;level=2;scope=0;desc=
   Tconstr(option,[{id=25678;level=2;scope=0;desc=Tconstr(string,[],[])}],[])},
  {id=25674;level=2;scope=0;desc=
   Tarrow("",{id=25676;level=2;scope=0;desc=Tconstr(unit,[],[])},
    {id=25675;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},Cok)},Cok)}
{id=25672;level=2;scope=0;desc=Tvar None}
{id=25681;level=2;scope=0;desc=Tconstr(unit,[],[])}
{id=25676;level=1;scope=0;desc=Tconstr(unit,[],[])}
{id=25676;level=1;scope=0;desc=Tconstr(unit,[],[])}
{id=25676;level=1;scope=0;desc=Tconstr(unit,[],[])}
{id=25675;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25671;level=1;scope=0;desc=Tvar None}
val var : Types.type_expr = <abstr>
|}, Principal{|
{id=25849;level=3;scope=0;desc=
 Tarrow("?name",
  {id=25853;level=3;scope=0;desc=
   Tconstr(option,[{id=25854;level=3;scope=0;desc=Tconstr(string,[],[])}],[])},
  {id=25850;level=3;scope=0;desc=
   Tarrow("",{id=25852;level=3;scope=0;desc=Tconstr(unit,[],[])},
    {id=25851;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},Cok)},Cok)}
{id=25848;level=3;scope=0;desc=Tvar None}
{id=25873;level=3;scope=0;desc=Tconstr(unit,[],[])}
{id=25872;level=3;scope=0;desc=Tconstr(unit,[],[])}
{id=25874;level=2;scope=0;desc=Tconstr(unit,[],[])}
{id=25866;level=2;scope=0;desc=Tconstr(unit,[],[])}
{id=25865;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25847;level=1;scope=0;desc=Tvar None}
val var : Types.type_expr = <abstr>
|}];;

Ctype.unify_eq (Ctype.instance (snd ref_lookedup).val_type) var;;
[%%expect{|
{id=25710;level=2;scope=0;desc=
 Tarrow("",{id=25714;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
  {id=25711;level=2;scope=0;desc=
   Tarrow("",{id=25713;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25712;level=2;scope=0;desc=Tconstr(bool,[],[])},Cok)},Cok)}
{id=25709;level=2;scope=0;desc=Tvar None}
{id=25718;level=3;scope=0;desc=
 Tarrow("?partial",
  {id=25722;level=3;scope=0;desc=
   Tconstr(option,[{id=25723;level=3;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=25719;level=3;scope=0;desc=
   Tarrow("",{id=25721;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25720;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},Cok)},Cok)}
{id=25717;level=3;scope=0;desc=Tvar None}
{id=25728;level=4;scope=0;desc=
 Tarrow("",
  {id=25730;level=4;scope=0;desc=
   Ttuple
    [{id=25731;level=4;scope=0;desc=Tvar None};
     {id=25729;level=4;scope=0;desc=Tvar None}]},{id=25729},Cok)}
{id=25727;level=4;scope=0;desc=Tvar None}
{id=25733;level=4;scope=0;desc=
 Ttuple
  [{id=25734;level=4;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25735;level=4;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25730;level=3;scope=0;desc=
 Ttuple
  [{id=25731;level=3;scope=0;desc=Tvar None};
   {id=25729;level=3;scope=0;desc=Tvar None}]}
{id=25730;level=3;scope=0;desc=
 Ttuple
  [{id=25734;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25735;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25730;level=3;scope=0;desc=
 Ttuple
  [{id=25734;level=3;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25735;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25735;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25726;level=3;scope=0;desc=Tvar None}
{id=25735;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25738;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25737;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25721;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25721;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25721;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25720;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25714;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25714;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25714;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25740;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25713;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25713;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25713;level=1;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25712;level=1;scope=0;desc=Tconstr(bool,[],[])}
{id=25708;level=1;scope=0;desc=Tvar None}
- : bool = false
|}, Principal{|
{id=25903;level=3;scope=0;desc=
 Tarrow("",{id=25907;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
  {id=25904;level=3;scope=0;desc=
   Tarrow("",{id=25906;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25905;level=3;scope=0;desc=Tconstr(bool,[],[])},Cok)},Cok)}
{id=25902;level=3;scope=0;desc=Tvar None}
{id=25921;level=4;scope=0;desc=
 Tarrow("?partial",
  {id=25925;level=4;scope=0;desc=
   Tconstr(option,[{id=25926;level=4;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=25922;level=4;scope=0;desc=
   Tarrow("",{id=25924;level=4;scope=0;desc=Tconstr(Types.type_expr,[],[])},
    {id=25923;level=4;scope=0;desc=Tconstr(Types.type_expr,[],[])},Cok)},Cok)}
{id=25920;level=4;scope=0;desc=Tvar None}
{id=25945;level=6;scope=0;desc=
 Tarrow("",
  {id=25947;level=6;scope=0;desc=
   Ttuple
    [{id=25948;level=6;scope=0;desc=Tvar None};
     {id=25946;level=6;scope=0;desc=Tvar None}]},{id=25946},Cok)}
{id=25944;level=6;scope=0;desc=Tvar None}
{id=25954;level=5;scope=0;desc=
 Ttuple
  [{id=25955;level=5;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25956;level=5;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25957;level=5;scope=0;desc=
 Ttuple
  [{id=25948;level=4;scope=0;desc=Tvar None};
   {id=25946;level=4;scope=0;desc=Tvar None}]}
{id=25957;level=5;scope=0;desc=
 Ttuple
  [{id=25955;level=4;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25956;level=4;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25953;level=5;scope=0;desc=
 Ttuple
  [{id=25955;level=4;scope=0;desc=Tconstr(Path.t,[],[])};
   {id=25956;level=4;scope=0;desc=Tconstr(Types.value_description,[],[])}]}
{id=25956;level=4;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25943;level=4;scope=0;desc=Tvar None}
{id=25956;level=100000000;scope=0;desc=
 Tconstr(Types.value_description,[],[])}
{id=25960;level=3;scope=0;desc=Tconstr(Types.value_description,[],[])}
{id=25959;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25961;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25961;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25938;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25937;level=3;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25963;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25963;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25919;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25964;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25965;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25965;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25918;level=2;scope=0;desc=Tconstr(Types.type_expr,[],[])}
{id=25917;level=2;scope=0;desc=Tconstr(bool,[],[])}
{id=25901;level=1;scope=0;desc=Tvar None}
- : bool = false
|}]

let e2 = Parse.implementation (Lexing.from_string "module M = struct type t let _ = (x : t list ref) end");;
[%%expect{|
{id=25769;level=2;scope=0;desc=
 Tarrow("",{id=25771;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},
  {id=25770;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])},Cok)}
{id=25768;level=2;scope=0;desc=Tvar None}
{id=25779;level=3;scope=0;desc=
 Tarrow("?with_positions",
  {id=25783;level=3;scope=0;desc=
   Tconstr(option,[{id=25784;level=3;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=25780;level=3;scope=0;desc=
   Tarrow("",{id=25782;level=3;scope=0;desc=Tconstr(string,[],[])},
    {id=25771;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},Cok)},Cok)}
{id=25778;level=3;scope=0;desc=Tvar None}
{id=25787;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=25782;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25782;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25782;level=2;scope=0;desc=Tconstr(string,[],[])}
{id=25771;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=25771;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=25771;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=25771;level=1;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=25770;level=1;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=25767;level=1;scope=0;desc=Tvar None}
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
|}, Principal{|
{id=25994;level=3;scope=0;desc=
 Tarrow("",{id=25996;level=3;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},
  {id=25995;level=3;scope=0;desc=Tconstr(Parsetree.structure,[],[])},Cok)}
{id=25993;level=3;scope=0;desc=Tvar None}
{id=26013;level=4;scope=0;desc=
 Tarrow("?with_positions",
  {id=26017;level=4;scope=0;desc=
   Tconstr(option,[{id=26018;level=4;scope=0;desc=Tconstr(bool,[],[])}],[])},
  {id=26014;level=4;scope=0;desc=
   Tarrow("",{id=26016;level=4;scope=0;desc=Tconstr(string,[],[])},
    {id=26015;level=4;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])},Cok)},Cok)}
{id=26012;level=4;scope=0;desc=Tvar None}
{id=26039;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=26040;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=26040;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=26034;level=3;scope=0;desc=Tconstr(string,[],[])}
{id=26033;level=3;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=26042;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=26042;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=26009;level=2;scope=0;desc=Tconstr(Lexing.lexbuf,[],[])}
{id=26008;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=25992;level=1;scope=0;desc=Tvar None}
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
let t1 = Typemod.type_structure !Topcommon.toplevel_env e1;;
[%%expect{|
{id=32318;level=2;scope=0;desc=
 Tarrow("",{id=32327;level=2;scope=0;desc=Tconstr(Env.t,[],[])},
  {id=32319;level=2;scope=0;desc=
   Tarrow("",
    {id=32326;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])},
    {id=32320;level=2;scope=0;desc=
     Ttuple
      [{id=32321;level=2;scope=0;desc=Tconstr(Typedtree.structure,[],[])};
       {id=32322;level=2;scope=0;desc=Tconstr(Types.signature,[],[])};
       {id=32323;level=2;scope=0;desc=
        Tconstr(Typemod.Signature_names.t,[],[])};
       {id=32324;level=2;scope=0;desc=Tconstr(Shape.t,[],[])};
       {id=32325;level=2;scope=0;desc=Tconstr(Env.t,[],[])}]},Cok)},Cok)}
{id=31999;level=2;scope=0;desc=Tvar None}
{id=33974;level=3;scope=0;desc=
 Tarrow("",
  {id=33976;level=3;scope=0;desc=
   Tconstr(ref,[{id=33975;level=3;scope=0;desc=Tvar None}],[])},{id=33975},
  Cok)}
{id=33973;level=3;scope=0;desc=Tvar None}
{id=33978;level=3;scope=0;desc=
 Tconstr(ref,[{id=33979;level=3;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=33976;level=2;scope=0;desc=
 Tconstr(ref,[{id=33975;level=2;scope=0;desc=Tvar None}],[])}
{id=33976;level=2;scope=0;desc=
 Tconstr(ref,[{id=33979;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=33976;level=2;scope=0;desc=
 Tconstr(ref,[{id=33979;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=33979;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=32327;level=1;scope=0;desc=Tconstr(Env.t,[],[])}
{id=32327;level=1;scope=0;desc=Tconstr(Env.t,[],[])}
{id=32327;level=1;scope=0;desc=Tconstr(Env.t,[],[])}
{id=32326;level=1;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=32326;level=1;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=32326;level=1;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=32326;level=1;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=32320;level=1;scope=0;desc=
 Ttuple
  [{id=32321;level=1;scope=0;desc=Tconstr(Typedtree.structure,[],[])};
   {id=32322;level=1;scope=0;desc=Tconstr(Types.signature,[],[])};
   {id=32323;level=1;scope=0;desc=Tconstr(Typemod.Signature_names.t,[],[])};
   {id=32324;level=1;scope=0;desc=Tconstr(Shape.t,[],[])};
   {id=32325;level=1;scope=0;desc=Tconstr(Env.t,[],[])}]}
{id=31998;level=1;scope=0;desc=Tvar None}
{id=34014;level=2;scope=0;desc=
 Tarrow("",{id=34016;level=2;scope=0;desc=Tvar None},
  {id=34015;level=2;scope=0;desc=Tconstr(ref,[{id=34016}],[])},Cok)}
{id=34013;level=2;scope=0;desc=Tvar None}
{id=34018;level=2;scope=0;desc=
 Tconstr(list,[{id=34019;level=2;scope=0;desc=Tvar None}],[])}
{id=34016;level=1;scope=0;desc=Tvar None}
{id=34018;level=1;scope=0;desc=
 Tconstr(list,[{id=34019;level=1;scope=0;desc=Tvar None}],[])}
{id=34018;level=1;scope=0;desc=
 Tconstr(list,[{id=34019;level=1;scope=0;desc=Tvar None}],[])}
{id=34015;level=1;scope=0;desc=
 Tconstr(ref,
  [{id=34018;level=1;scope=0;desc=
    Tconstr(list,[{id=34019;level=1;scope=0;desc=Tvar None}],[])}],[])}
{id=34012;level=1;scope=0;desc=Tvar None}
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
        val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 19}},
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
      val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 19}},
     Types.Exported)],
   <abstr>, {Shape.uid = None; desc = Shape.Struct <abstr>}, <abstr>)
|}, Principal{|
{id=32410;level=3;scope=0;desc=
 Tarrow("",{id=32419;level=3;scope=0;desc=Tconstr(Env.t,[],[])},
  {id=32411;level=3;scope=0;desc=
   Tarrow("",
    {id=32418;level=3;scope=0;desc=Tconstr(Parsetree.structure,[],[])},
    {id=32412;level=3;scope=0;desc=
     Ttuple
      [{id=32413;level=3;scope=0;desc=Tconstr(Typedtree.structure,[],[])};
       {id=32414;level=3;scope=0;desc=Tconstr(Types.signature,[],[])};
       {id=32415;level=3;scope=0;desc=
        Tconstr(Typemod.Signature_names.t,[],[])};
       {id=32416;level=3;scope=0;desc=Tconstr(Shape.t,[],[])};
       {id=32417;level=3;scope=0;desc=Tconstr(Env.t,[],[])}]},Cok)},Cok)}
{id=32091;level=3;scope=0;desc=Tvar None}
{id=34086;level=4;scope=0;desc=
 Tarrow("",
  {id=34088;level=4;scope=0;desc=
   Tconstr(ref,[{id=34087;level=4;scope=0;desc=Tvar None}],[])},{id=34087},
  Cok)}
{id=34085;level=4;scope=0;desc=Tvar None}
{id=34094;level=3;scope=0;desc=
 Tconstr(ref,[{id=34095;level=3;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=34096;level=3;scope=0;desc=
 Tconstr(ref,[{id=34087;level=2;scope=0;desc=Tvar None}],[])}
{id=34096;level=3;scope=0;desc=
 Tconstr(ref,[{id=34095;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=34093;level=3;scope=0;desc=
 Tconstr(ref,[{id=34095;level=2;scope=0;desc=Tconstr(Env.t,[],[])}],[])}
{id=34095;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=34098;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=34098;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=34084;level=2;scope=0;desc=Tconstr(Env.t,[],[])}
{id=34102;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=34103;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=34103;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=34083;level=2;scope=0;desc=Tconstr(Parsetree.structure,[],[])}
{id=34077;level=2;scope=0;desc=
 Ttuple
  [{id=34078;level=2;scope=0;desc=Tconstr(Typedtree.structure,[],[])};
   {id=34079;level=2;scope=0;desc=Tconstr(Types.signature,[],[])};
   {id=34080;level=2;scope=0;desc=Tconstr(Typemod.Signature_names.t,[],[])};
   {id=34081;level=2;scope=0;desc=Tconstr(Shape.t,[],[])};
   {id=34082;level=2;scope=0;desc=Tconstr(Env.t,[],[])}]}
{id=32090;level=1;scope=0;desc=Tvar None}
{id=34133;level=3;scope=0;desc=
 Tarrow("",{id=34135;level=3;scope=0;desc=Tvar None},
  {id=34134;level=3;scope=0;desc=Tconstr(ref,[{id=34135}],[])},Cok)}
{id=34132;level=3;scope=0;desc=Tvar None}
{id=34143;level=3;scope=0;desc=
 Tconstr(list,[{id=34142;level=3;scope=0;desc=Tvar None}],[])}
{id=34135;level=1;scope=0;desc=Tvar None}
{id=34144;level=2;scope=0;desc=
 Tconstr(list,[{id=34142;level=1;scope=0;desc=Tvar None}],[])}
{id=34143;level=1;scope=0;desc=
 Tconstr(list,[{id=34142;level=1;scope=0;desc=Tvar None}],[])}
{id=34140;level=2;scope=0;desc=
 Tconstr(ref,
  [{id=34143;level=1;scope=0;desc=
    Tconstr(list,[{id=34142;level=1;scope=0;desc=Tvar None}],[])}],[])}
{id=34131;level=1;scope=0;desc=Tvar None}
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
        val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 19}},
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
      val_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 19}},
     Types.Exported)],
   <abstr>, {Shape.uid = None; desc = Shape.Struct <abstr>}, <abstr>)
|}]
