open Language
module Wa = Wasm.Ast
module Wt = Wasm.Types
module M = Map.Make (String)

let phrase elem = Wasm.Source.(elem @@ no_region)
let decode_s = Wasm.Utf8.decode
let get_i32 i = Wasm.Value.I32 i
let get_const i = Wa.Const (phrase @@ get_i32 @@ Int32.of_int i)
let get_binary b = Wa.Binary (get_i32 b)
let get_compare b = Wa.Compare (get_i32 b)
let get_idx i = phrase @@ Int32.of_int i

let rec compile_list env ast =
  match ast with
  | Expr.Call (name, args) -> (
      match name with
      | Expr.Var name' ->
          let index = env#get_func_by_name name' in
          let env, code =
            List.fold_left
              (fun (env, acc) instr ->
                let env, code = compile_list env instr in
                (env, acc @ code))
              (env, []) args
          in
          (env, code @ [ phrase @@ Wa.Call (get_idx index) ])
      | _ ->
          report_error
          @@ Printf.sprintf "unsupported call value %s\n" (GT.show Expr.t name))
  | Expr.Binop (op, lhs, rhs) ->
      let env, lhscode = compile_list env lhs in
      let env, rhscode = compile_list env rhs in
      let env, opcode =
        match op with
        | "+" -> (env, [ phrase @@ get_binary Wa.I32Op.Add ])
        | "-" -> (env, [ phrase @@ get_binary Wa.I32Op.Sub ])
        | "*" -> (env, [ phrase @@ get_binary Wa.I32Op.Mul ])
        | "/" -> (env, [ phrase @@ get_binary Wa.I32Op.DivS ])
        | "%" -> (env, [ phrase @@ get_binary Wa.I32Op.RemS ])
        | "==" -> (env, [ phrase @@ get_compare Wa.I32Op.Eq ])
        | "!=" -> (env, [ phrase @@ get_compare Wa.I32Op.Ne ])
        | "<=" -> (env, [ phrase @@ get_compare Wa.I32Op.LeS ])
        | "<" -> (env, [ phrase @@ get_compare Wa.I32Op.LtS ])
        | ">=" -> (env, [ phrase @@ get_compare Wa.I32Op.GeS ])
        | ">" -> (env, [ phrase @@ get_compare Wa.I32Op.GtS ])
        | "&&" ->
            let index, env =
              env#type_upsert
                Wt.(
                  RecT
                    [
                      SubT
                        ( Final,
                          [],
                          DefFuncT (FuncT ([ NumT I32T ], [ NumT I32T ])) );
                    ])
            in
            ( env,
              [
                phrase
                @@ Wa.If
                     ( Wa.VarBlockType (get_idx index),
                       [
                         phrase @@ get_const 0;
                         phrase @@ get_compare Wa.I32Op.Ne;
                       ],
                       [ phrase Wa.Drop; phrase @@ get_const 0 ] );
              ] )
        | "!!" ->
            ( env,
              [
                phrase @@ get_binary Wa.I32Op.Or;
                phrase @@ get_const 0;
                phrase @@ get_compare Wa.I32Op.Ne;
              ] )
        | _ -> report_error @@ Printf.sprintf "unsupported binop %s\n" op
      in
      (env, lhscode @ rhscode @ opcode)
  | Expr.Const i -> (env, [ phrase @@ get_const i ])
  | Expr.Seq (s1, s2) ->
      let env, code1 = compile_list env s1 in
      let env, code2 = compile_list env s2 in
      (env, code1 @ code2)
  | Expr.Ignore s ->
      let env, code = compile_list env s in
      (env, code @ [ phrase Wa.Drop ])
  | Expr.Var name ->
      let index = env#get_global name in
      (env, [ phrase @@ Wa.GlobalGet (get_idx index) ])
  | Expr.Assign (Expr.Ref name, instr) ->
      let index = env#get_global name in
      let env, code = compile_list env instr in
      (env, code @ [ phrase @@ Wa.GlobalSet (get_idx index) ; phrase @@ Wa.GlobalGet (get_idx index) ])
  | Expr.If (c, s1, s2) ->
      let env, c_code = compile_list env c in
      let env, s1_code = compile_list env s1 in
      let env, s2_code = compile_list env s2 in
      ( env,
        c_code
        @ [
            phrase @@ Wa.If (ValBlockType (Some (NumT I32T)), s1_code, s2_code);
          ] )
  | Expr.Scope ([], instr) -> compile_list env instr
  | _ ->
      report_error
      @@ Printf.sprintf "unsupported structure %s\n" (GT.show Expr.t ast)

class env =
  object (self)
    val types =
      object (self)
        val index = 0
        val types_rev = []

        method upsert t =
          match List.assoc_opt t types_rev with
          | None ->
              (index, {<index = index + 1; types_rev = (t, index) :: types_rev>})
          | Some i -> (i, self)

        method get_types = List.rev @@ List.map fst types_rev
      end

    val imports_rev = []
    val func_index = 0
    val funcs_rev = []
    val func_by_name = M.empty
    val exports = []
    val globals_index = 0
    val globals_rev = []
    val globals_by_name = M.empty

    method type_upsert t =
      let index, types = types#upsert t in
      (index, {<types>})

    method add_function_import name t =
      let rec_type = Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) in
      let type_index, types = types#upsert rec_type in
      let new_import =
        Wa.
          {
            module_name = decode_s "lama";
            item_name = decode_s name;
            idesc = phrase @@ Wa.FuncImport (get_idx type_index);
          }
      in
      {<types
       ; imports_rev = new_import :: imports_rev
       ; func_index = func_index + 1
       ; func_by_name = func_by_name |> M.add name func_index>}

    method add_function name t body =
      let rec_type = Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) in
      let type_index, types = types#upsert rec_type in
      {<types
       ; funcs_rev = Wa.{ ftype = get_idx type_index; locals = []; body }
                     :: funcs_rev
       ; func_index = func_index + 1
       ; func_by_name = func_by_name |> M.add name func_index>}

    method export_function name =
      let index = M.find name func_by_name in
      {<exports = Wa.
                    {
                      name = decode_s name;
                      edesc = phrase @@ FuncExport (get_idx index);
                    }
                  :: exports>}

    method get_func_by_name name =
      try M.find name func_by_name
      with Not_found ->
        report_error
        @@ Printf.sprintf "unable to find function with name \"%s\"" name

    method add_global name =
      if M.mem name globals_by_name then
        report_error
        @@ Printf.sprintf "name \"%s\" is already defined in the scope" name
      else
        {<globals_index = globals_index + 1
         ; globals_rev = Wa.
                           {
                             gtype = Wt.(GlobalT (Var, NumT I32T));
                             ginit = phrase @@ [ phrase @@ get_const 0 ];
                           }
                         :: globals_rev
         ; globals_by_name = globals_by_name |> M.add name globals_index>}

    method get_global name =
      try M.find name globals_by_name
      with Not_found ->
        report_error
        @@ Printf.sprintf "unable to find global with name \"%s\"" name

    method get_module =
      phrase
        Wa.
          {
            empty_module with
            imports = List.rev @@ List.map phrase imports_rev;
            funcs = List.rev @@ List.map phrase funcs_rev;
            types = List.map phrase types#get_types;
            exports = List.map phrase exports;
            globals = List.rev @@ List.map phrase globals_rev;
          }
  end

let compile ast =
  let env = new env in
  match ast with
  | Expr.Scope (decls, instr) ->
      let env =
        env#add_function_import "write" (FuncT ([ NumT I32T ], [ NumT I32T ]))
      in
      let env = env#add_function_import "read" (FuncT ([], [ NumT I32T ])) in
      let globals =
        List.filter_map
          (fun (name, (_, d)) ->
            match d with `Variable init -> Some (name, init) | _ -> None)
          decls
      in
      let env =
        List.fold_left (fun env (name, _) -> env#add_global name) env @@ globals
      in
      let env, init =
        List.fold_left
          (fun (env, acc) (name, instr) ->
            let env, code = compile_list env instr in
            ( env,
              acc @ code
              @ [ phrase @@ Wa.GlobalSet (get_idx @@ env#get_global name) ] ))
          (env, [])
          (List.filter_map
             (fun (name, init) ->
               match init with Some i -> Some (name, i) | _ -> None)
             globals)
      in
      let env, code = compile_list env (Expr.Ignore instr) in
      let env = env#add_function "main" (FuncT ([], [])) (init @ code) in
      let env = env#export_function "main" in
      env#get_module
  | _ -> report_error "expected root scope"

let genast _ ((imports, _), p) = compile p

let build cmd prog =
  let module' = genast cmd prog in
  let oc = open_out (cmd#basename ^ ".wast") in
  Wasm.Print.module_ oc 80 module';
  close_out oc;
  cmd#dump_file "wasm" (Wasm.Encode.encode module')
