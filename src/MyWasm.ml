open Language

(* A set of strings *)
module S = Set.Make (String)
module W = Wasm

let phrase elem = W.Source.(elem @@ no_region)
let decode_s = W.Utf8.decode
let get_i32 i = W.Value.I32 i
let get_const i = W.Ast.Const (phrase @@ get_i32 @@ Int32.of_int i)
let get_binary b = W.Ast.Binary (get_i32 b)
let get_compare b = W.Ast.Compare (get_i32 b)

let rec compile_list ast =
  match ast with
  | Expr.Call (name, l) -> (
      match name with
      | Expr.Var name' ->
          List.flatten (List.map compile_list l)
          @ [ phrase @@ W.Ast.Call (phrase 0l) ]
      | a ->
          Printf.printf "unsupported call value %s\n" (GT.show Expr.t a);
          [])
  | Expr.Binop (op, lhs, rhs) -> (
      compile_list lhs @ compile_list rhs
      @
      match op with
      | "+" -> [ phrase @@ get_binary W.Ast.I32Op.Add ]
      | "-" -> [ phrase @@ get_binary W.Ast.I32Op.Sub ]
      | "*" -> [ phrase @@ get_binary W.Ast.I32Op.Mul ]
      | "/" -> [ phrase @@ get_binary W.Ast.I32Op.DivS ]
      | "%" -> [ phrase @@ get_binary W.Ast.I32Op.RemS ]
      | "==" -> [ phrase @@ get_compare W.Ast.I32Op.Eq ]
      | "!=" -> [ phrase @@ get_compare W.Ast.I32Op.Ne ]
      | "<=" -> [ phrase @@ get_compare W.Ast.I32Op.LeS ]
      | "<" -> [ phrase @@ get_compare W.Ast.I32Op.LtS ]
      | ">=" -> [ phrase @@ get_compare W.Ast.I32Op.GeS ]
      | ">" -> [ phrase @@ get_compare W.Ast.I32Op.GtS ]
      | "&&" ->
          [
            phrase
            @@ W.Ast.If
                 ( W.Ast.VarBlockType (phrase 2l),
                   [
                     phrase @@ get_const 0; phrase @@ get_compare W.Ast.I32Op.Ne;
                   ],
                   [ phrase W.Ast.Drop; phrase @@ get_const 0 ] );
          ]
      | "!!" ->
          [
            phrase @@ get_binary W.Ast.I32Op.Or;
            phrase @@ get_const 0;
            phrase @@ get_compare W.Ast.I32Op.Ne;
          ]
      | _ ->
          Printf.printf "unsupported binop %s\n" op;
          [])
  | Expr.Const i -> [ phrase @@ get_const i ]
  | Expr.Seq (s1, s2) -> compile_list s1 @ compile_list s2
  | Expr.Ignore s -> compile_list s @ [ phrase W.Ast.Drop ]
  | a ->
      Printf.printf "unsupported structure %s\n" (GT.show Expr.t a);
      []

let compile ast =
  match ast with
  | Expr.Scope (_, i) ->
      let types =
        [
          (phrase
          @@ W.Types.(RecT [ SubT (Final, [], DefFuncT (FuncT ([], []))) ]));
          (phrase
          @@ W.Types.(
               RecT [ SubT (Final, [], DefFuncT (FuncT ([ NumT I32T ], []))) ])
          );
          (phrase
          @@ W.Types.(
               RecT
                 [
                   SubT
                     (Final, [], DefFuncT (FuncT ([ NumT I32T ], [ NumT I32T ])));
                 ]));
        ]
      in
      let imports =
        [
          phrase
            W.Ast.
              {
                module_name = decode_s "lama";
                item_name = decode_s "Lwrite";
                idesc = phrase @@ W.Ast.FuncImport (phrase 1l);
              };
        ]
      in
      let funcs =
        [
          phrase W.Ast.{ ftype = phrase 0l; locals = []; body = compile_list i };
        ]
      in
      let exports =
        [
          phrase
            W.Ast.
              {
                name = decode_s "main";
                edesc = phrase @@ FuncExport (phrase 1l);
              };
        ]
      in
      phrase W.Ast.{ empty_module with imports; funcs; types; exports }
  | _ -> report_error "expected root scope"

let genast cmd ((imports, _), p) = compile p

let build cmd prog =
  let module' = genast cmd prog in
  let oc = open_out (cmd#basename ^ ".wast") in
  W.Print.module_ oc 80 module';
  close_out oc;
  cmd#dump_file "wasm" (W.Encode.encode module')
