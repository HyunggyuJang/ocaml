(* TEST
   flags = "-I ${ocamlsrcdir}/typing \
    -I ${ocamlsrcdir}/parsing -I ${ocamlsrcdir}/toplevel"
   * expect
*)
type u = <x:int>
type t = private <u; ..>

let s = {|type t = private <u; ..>|};;
let pe = Parse.implementation (Lexing.from_string s);;
let te = Typemod.type_structure !Topcommon.toplevel_env pe;;
[%%expect{|
type u = < x : int >
type t = private < x : int; .. >
val s : string = "type t = private <u; ..>"
val pe : Parsetree.structure =
  [{Parsetree.pstr_desc =
     Parsetree.Pstr_type (Asttypes.Recursive,
      [{Parsetree.ptype_name =
         {Asttypes.txt = "t";
          loc =
           {Location.loc_start =
             {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 5};
            loc_end =
             {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 6};
            loc_ghost = false}};
        ptype_params = []; ptype_cstrs = [];
        ptype_kind = Parsetree.Ptype_abstract;
        ptype_private = Asttypes.Private;
        ptype_manifest =
         Some
          {Parsetree.ptyp_desc =
            Parsetree.Ptyp_object
             ([{Parsetree.pof_desc =
                 Parsetree.Oinherit
                  {Parsetree.ptyp_desc =
                    Parsetree.Ptyp_constr
                     ({Asttypes.txt = Longident.Lident "u";
                       loc =
                        {Location.loc_start =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 18};
                         loc_end =
                          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                           pos_cnum = 19};
                         loc_ghost = false}},
                     []);
                   ptyp_loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 18};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 19};
                     loc_ghost = false};
                   ptyp_loc_stack = []; ptyp_attributes = []};
                pof_loc =
                 {Location.loc_start =
                   {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                    pos_cnum = 18};
                  loc_end =
                   {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                    pos_cnum = 19};
                  loc_ghost = false};
                pof_attributes = []}],
             Asttypes.Open);
           ptyp_loc =
            {Location.loc_start =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 17};
             loc_end =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 24};
             loc_ghost = false};
           ptyp_loc_stack = []; ptyp_attributes = []};
        ptype_attributes = [];
        ptype_loc =
         {Location.loc_start =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
          loc_end =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 24};
          loc_ghost = false}}]);
    pstr_loc =
     {Location.loc_start =
       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
      loc_end =
       {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 24};
      loc_ghost = false}}]
val te :
  Typedtree.structure * Types.signature * Typemod.Signature_names.t *
  Shape.t * Env.t =
  ({Typedtree.str_items =
     [{Typedtree.str_desc =
        Typedtree.Tstr_type (Asttypes.Recursive,
         [{Typedtree.typ_id = <abstr>;
           typ_name =
            {Asttypes.txt = "t#row";
             loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 5};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 6};
               loc_ghost = true}};
           typ_params = [];
           typ_type =
            {Types.type_params = []; type_arity = 0;
             type_kind = Types.Type_abstract;
             type_private = Asttypes.Private; type_manifest = None;
             type_variance = []; type_separability = [];
             type_is_newtype = false; type_expansion_scope = 0;
             type_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 0};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 24};
               loc_ghost = true};
             type_attributes = []; type_immediate = Type_immediacy.Unknown;
             type_unboxed_default = false;
             type_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 8}};
           typ_cstrs = []; typ_kind = Typedtree.Ttype_abstract;
           typ_private = Asttypes.Private; typ_manifest = None;
           typ_loc =
            {Location.loc_start =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 0};
             loc_end =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 24};
             loc_ghost = true};
           typ_attributes = []};
          {Typedtree.typ_id = <abstr>;
           typ_name =
            {Asttypes.txt = "t";
             loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 5};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 6};
               loc_ghost = false}};
           typ_params = [];
           typ_type =
            {Types.type_params = []; type_arity = 0;
             type_kind = Types.Type_abstract;
             type_private = Asttypes.Private; type_manifest = Some <abstr>;
             type_variance = []; type_separability = [];
             type_is_newtype = false; type_expansion_scope = 0;
             type_loc =
              {Location.loc_start =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 0};
               loc_end =
                {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                 pos_cnum = 24};
               loc_ghost = false};
             type_attributes = []; type_immediate = Type_immediacy.Unknown;
             type_unboxed_default = false;
             type_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 9}};
           typ_cstrs = []; typ_kind = Typedtree.Ttype_abstract;
           typ_private = Asttypes.Private;
           typ_manifest =
            Some
             {Typedtree.ctyp_desc =
               Typedtree.Ttyp_object
                ([{Typedtree.of_desc =
                    Typedtree.OTinherit
                     {Typedtree.ctyp_desc =
                       Typedtree.Ttyp_constr (Path.Pident <abstr>,
                        {Asttypes.txt = Longident.Lident "u";
                         loc =
                          {Location.loc_start =
                            {Lexing.pos_fname = ""; pos_lnum = 1;
                             pos_bol = 0; pos_cnum = 18};
                           loc_end =
                            {Lexing.pos_fname = ""; pos_lnum = 1;
                             pos_bol = 0; pos_cnum = 19};
                           loc_ghost = false}},
                        []);
                      ctyp_type = <abstr>; ctyp_env = <abstr>;
                      ctyp_loc =
                       {Location.loc_start =
                         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                          pos_cnum = 18};
                        loc_end =
                         {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                          pos_cnum = 19};
                        loc_ghost = false};
                      ctyp_attributes = []};
                   of_loc =
                    {Location.loc_start =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 18};
                     loc_end =
                      {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                       pos_cnum = 19};
                     loc_ghost = false};
                   of_attributes = []}],
                Asttypes.Open);
              ctyp_type = <abstr>; ctyp_env = <abstr>;
              ctyp_loc =
               {Location.loc_start =
                 {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                  pos_cnum = 17};
                loc_end =
                 {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
                  pos_cnum = 24};
                loc_ghost = false};
              ctyp_attributes = []};
           typ_loc =
            {Location.loc_start =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 0};
             loc_end =
              {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0;
               pos_cnum = 24};
             loc_ghost = false};
           typ_attributes = []}]);
       str_loc =
        {Location.loc_start =
          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
         loc_end =
          {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 24};
         loc_ghost = false};
       str_env = <abstr>}];
    str_type =
     [Types.Sig_type (<abstr>,
       {Types.type_params = []; type_arity = 0;
        type_kind = Types.Type_abstract; type_private = Asttypes.Private;
        type_manifest = None; type_variance = []; type_separability = [];
        type_is_newtype = false; type_expansion_scope = 0;
        type_loc =
         {Location.loc_start =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
          loc_end =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 24};
          loc_ghost = true};
        type_attributes = []; type_immediate = Type_immediacy.Unknown;
        type_unboxed_default = false;
        type_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 8}},
       Types.Trec_not, Types.Exported);
      Types.Sig_type (<abstr>,
       {Types.type_params = []; type_arity = 0;
        type_kind = Types.Type_abstract; type_private = Asttypes.Private;
        type_manifest = Some <abstr>; type_variance = [];
        type_separability = []; type_is_newtype = false;
        type_expansion_scope = 0;
        type_loc =
         {Location.loc_start =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
          loc_end =
           {Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 24};
          loc_ghost = false};
        type_attributes = []; type_immediate = Type_immediacy.Unknown;
        type_unboxed_default = false;
        type_uid = Types.Uid.Item {Types.Uid.comp_unit = ""; id = 9}},
       Types.Trec_first, Types.Exported)];
    str_final_env = <abstr>},
   [Types.Sig_type (<abstr>,
     {Types.type_params = ...; type_arity = ...; type_kind = ...;
      type_private = ...; type_manifest = ...; type_variance = ...;
      type_separability = ...; type_is_newtype = ...;
      type_expansion_scope = ...; type_loc = ...; type_attributes = ...;
      type_immediate = ...; type_unboxed_default = ...; type_uid = ...},
     ...);
    ...],
   ...)
|}]

let f (x:t) (y:u) = x = y;;
[%%expect{|
Line 1, characters 24-25:
1 | let f (x:t) (y:u) = x = y;;
                            ^
Error: This expression has type u but an expression was expected of type t
       The second object type has an abstract row, it cannot be closed
|}]


let g (x:u) (y:t) = x = y;;
[%%expect{|
Line 1, characters 24-25:
1 | let g (x:u) (y:t) = x = y;;
                            ^
Error: This expression has type t but an expression was expected of type u
       The first object type has an abstract row, it cannot be closed
|}]
