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
let get_test_op b = Wa.Test (get_i32 b)
let get_idx i = phrase @@ Int32.of_int i

let any_type = Wt.(RefT (NoNull, AnyHT))
let unbox = [ phrase @@ Wa.RefCast (NoNull, I31HT); phrase @@ Wa.I31Get SX ]
let box = [ phrase @@ Wa.RefI31 ]

type w_func =
  | ImportFunc of string * int (* name, type_idx *)
  | Func of int * int * Wa.instr list (* type_idx, locals_count, body *)

type w_value = Global of int | Local of int | Callable of int
type w_export = ExportFunc of string * int (* name, func_idx *)

let find_index v l =
  let rec inner v i = function
    | [] -> None
    | x :: xs -> if x = v then Some i else inner v (i + 1) xs
  in
  inner v 0 l

let rec is_last cond = function
  | [] -> false
  | x :: [] -> cond x
  | _ :: xs -> is_last cond xs

let upsert t types =
  match find_index t types with
  | Some i -> (i, types)
  | None -> (List.length types, types @ [ t ])

let rec get_last = function
  | [] -> raise (Failure "not expected empty list in get_last")
  | x :: [] -> x
  | _ :: xs -> get_last xs

let rec replace idx value = function
  | [] -> raise (Failure "length exceeded in replace")
  | x :: xs -> if idx = 0 then value :: xs else x :: replace (idx - 1) value xs

class lexical_scopes =
  object (self)
    val scopes : w_value M.t list = [ M.empty ]

    method add name v =
      if M.mem name (List.hd scopes) then
        report_error @@ Printf.sprintf "name \"%s\" is already defined" name
      else {<scopes = M.add name v (List.hd scopes) :: List.tl scopes>}

    method get name =
      let rec inner name = function
        | [] -> None
        | x :: xs -> (
            match M.find_opt name x with
            | None -> inner name xs
            | found -> found)
      in
      inner name scopes

    method enter_function = {<scopes = [ get_last scopes ]>}
    method enter_scope = {<scopes = M.empty :: scopes>}
    method exit_scope = {<scopes = List.tl scopes>}
  end

class env =
  object (self)
    val types = []
    val functions = []
    val globals = 0
    val locals = 0
    val exports = []
    val scopes = new lexical_scopes
    val stack_depth = 0

    method upsert_type t =
      let type_idx, types = upsert t types in
      (type_idx, {<types>})

    method add_function_import name t =
      if is_last (function ImportFunc (_, _) -> false | _ -> true) functions
      then report_error "all imports should be added before other functions"
      else
        let type_idx, types =
          upsert Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) types
        in
        let func_idx = List.length functions in
        ( func_idx,
          {<types
           ; functions = functions @ [ ImportFunc (name, type_idx) ]
           ; scopes = scopes#add name (Callable func_idx)>} )

    method allocate_functions names =
      let _, scopes =
        List.fold_left
          (fun (idx, scopes) name -> (idx + 1, scopes#add name (Callable idx)))
          (List.length functions, scopes)
          names
      in
      let functions = functions @ List.map (fun _ -> Func (0, 0, [])) names in
      {<scopes; functions>}

    method place_function name t locals_count body =
      let type_idx, types =
        upsert Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) types
      in
      let func_idx =
        match self#get name with
        | Some (Callable x) -> x
        | _ ->
            report_error
            @@ Printf.sprintf "function \"%s\" not allocated before placement"
                 name
      in
      {<types
       ; functions = replace func_idx
                       (Func (type_idx, locals_count, body))
                       functions>}

    method add_function name t locals_count body =
      let type_idx, types =
        upsert Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) types
      in
      let func_idx = List.length functions in
      ( func_idx,
        {<types
         ; functions = functions @ [ Func (type_idx, locals_count, body) ]
         ; scopes = scopes#add name (Callable func_idx)>} )

    method export_function name =
      match scopes#get name with
      | Some (Callable func_idx) ->
          {<exports = ExportFunc (name, func_idx) :: exports>}
      | _ ->
          report_error
          @@ Printf.sprintf "cannot export \"%s\" because it's not a function"
               name

    method add_global name =
      ( globals,
        {<globals = globals + 1; scopes = scopes#add name (Global globals)>} )

    method add_local name =
      (locals, {<locals = locals + 1; scopes = scopes#add name (Local locals)>})

    method get_scopes_ = scopes
    method get name = scopes#get name

    method enter_function =
      {<scopes = scopes#enter_function; locals = 0; stack_depth = 0>}

    method exit_function (old_env : env) =
      {<scopes = old_env#get_scopes_
       ; locals = old_env#get_locals_count
       ; stack_depth = old_env#get_stack_depth_>}

    method enter_scope = {<scopes = scopes#enter_scope>}
    method exit_scope = {<scopes = scopes#exit_scope>}
    method get_locals_count = locals
    method put_on_stack = {<stack_depth = stack_depth + 1>}
    method eat_from_stack = {<stack_depth = stack_depth - 1>}
    method eat_n_from_stack n = {<stack_depth = stack_depth - n>}
    method get_stack_depth_ = stack_depth

    method compare_stack_depth (other_env : env) =
      stack_depth - other_env#get_stack_depth_

    method reset_stack_depth (other_env : env) =
      {<stack_depth = other_env#get_stack_depth_>}

    method assemble_module =
      let types = List.map phrase types in
      let imports =
        List.filter_map
          (function
            | ImportFunc (name, type_idx) ->
                Some
                  (phrase
                  @@ Wa.
                       {
                         module_name = decode_s "lama";
                         item_name = decode_s name;
                         idesc = phrase @@ Wa.FuncImport (get_idx type_idx);
                       })
            | _ -> None)
          functions
      in
      let funcs =
        List.filter_map
          (function
            | Func (type_idx, locals_count, body) ->
                Some
                  (phrase
                  @@ Wa.
                       {
                         ftype = get_idx type_idx;
                         locals =
                           List.init locals_count (fun _ ->
                               phrase @@ { ltype = any_type });
                         body;
                       })
            | _ -> None)
          functions
      in
      let globals =
        List.init globals (fun _ ->
            phrase
            @@ Wa.
                 {
                   gtype = GlobalT (Var, any_type);
                   ginit = phrase @@ [ phrase @@ get_const 0 ] @ box;
                 })
      in
      let exports =
        List.map
          (function
            | ExportFunc (name, func_idx) ->
                phrase
                @@ Wa.
                     {
                       name = decode_s name;
                       edesc = phrase @@ FuncExport (get_idx func_idx);
                     })
          exports
      in
      phrase Wa.{ empty_module with imports; funcs; types; globals; exports }
  end

let rec compile_list (env : env) ast =
  match ast with
  | Expr.Call (name, args) -> (
      match name with
      | Expr.Var name' -> (
          match env#get name' with
          | Some (Callable func_idx) ->
              let env, code =
                List.fold_left
                  (fun (env, acc) instr ->
                    let env, code = compile_list env instr in
                    (env, acc @ code))
                  (env, []) args
              in
              let env = env#eat_n_from_stack @@ List.length args in
              let env = env#put_on_stack in
              (env, code @ [ phrase @@ Wa.Call (get_idx func_idx) ])
          | _ ->
              report_error
              @@ Printf.sprintf "function with name \"%s\" not found" name')
      | _ ->
          report_error
          @@ Printf.sprintf "unsupported call value %s\n" (GT.show Expr.t name))
  | Expr.Binop (op, lhs, rhs) ->
      let env, lhscode = compile_list env lhs in
      let env, rhscode = compile_list env rhs in
      let env = env#eat_from_stack in
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
            let type_idx, env =
              env#upsert_type
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
                     ( Wa.VarBlockType (get_idx type_idx),
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
      (env, lhscode @ unbox @ rhscode @ unbox @ opcode @ box)
  | Expr.Const i -> (env#put_on_stack, [ phrase @@ get_const i ] @ box)
  | Expr.Skip -> (env, [])
  | Expr.Seq (s1, s2) ->
      let env, code1 = compile_list env s1 in
      let env, code2 = compile_list env s2 in
      (env, code1 @ code2)
  | Expr.Ignore s ->
      let env, code = compile_list env s in
      (env#eat_from_stack, code @ [ phrase Wa.Drop ])
  | Expr.Var name -> (
      match env#get name with
      | Some (Global index) ->
          (env#put_on_stack, [ phrase @@ Wa.GlobalGet (get_idx index) ])
      | Some (Local index) ->
          (env#put_on_stack, [ phrase @@ Wa.LocalGet (get_idx index) ])
      | _ ->
          report_error
          @@ Printf.sprintf "trying to get, var with name \"%s\" not found" name
      )
  | Expr.Assign (Expr.Ref name, instr) -> (
      let env, code = compile_list env instr in
      match env#get name with
      | Some (Global index) ->
          ( env,
            code
            @ [
                phrase @@ Wa.GlobalSet (get_idx index);
                phrase @@ Wa.GlobalGet (get_idx index);
              ] )
      | Some (Local index) ->
          (env, code @ [ phrase @@ Wa.LocalTee (get_idx index) ])
      | _ ->
          report_error
          @@ Printf.sprintf "trying to set, var with name \"%s\" not found" name
      )
  | Expr.If (c, s1, s2) ->
      let env', c_code = compile_list env c in
      let env = env'#reset_stack_depth env in
      let env', s1_code = compile_list env s1 in
      let env = env'#reset_stack_depth env in
      let env', s2_code = compile_list env' s2 in
      let t =
        if env'#compare_stack_depth env = 0 then Wa.ValBlockType None
        else Wa.ValBlockType (Some (any_type))
      in
      (env', c_code @ unbox @ [ phrase @@ Wa.If (t, s1_code, s2_code) ])
  | Expr.While (cond, body) ->
      let env', c_code = compile_list env cond in
      let env = env'#reset_stack_depth env in
      let env, body_code = compile_list env body in
      ( env,
        [
          phrase
          @@ Wa.Block
               ( ValBlockType None,
                 [
                   phrase
                   @@ Wa.Loop
                        ( ValBlockType None,
                          c_code
                          @ unbox
                          @ [
                              phrase @@ get_test_op Wa.I32Op.Eqz;
                              phrase @@ Wa.BrIf (get_idx 1);
                            ]
                          @ body_code
                          @ [ phrase @@ Wa.Br (get_idx 0) ] );
                 ] );
        ] )
  | Expr.DoWhile (body, cond) ->
      let env, body_code = compile_list env body in
      let env', c_code = compile_list env cond in
      let env = env'#reset_stack_depth env in
      ( env,
        [
          phrase
          @@ Wa.Loop
               ( ValBlockType None,
                 body_code @ c_code @ unbox @ [ phrase @@ Wa.BrIf (get_idx 0) ] );
        ] )
  | Expr.Scope (decls, instr) ->
      let env = env#enter_scope in
      let env, code =
        compile_scope decls instr
          (fun env name -> snd (env#add_local name))
          (fun env name ->
            match env#get name with
            | Some (Local index) -> phrase @@ Wa.LocalSet (get_idx @@ index)
            | _ -> report_error "local was not added properly")
          env
      in
      (env#exit_scope, code)
  | _ ->
      report_error
      @@ Printf.sprintf "unsupported structure %s\n" (GT.show Expr.t ast)

and compile_scope decls instr add_local init_local env =
  let locals =
    List.filter_map
      (fun (name, decl) ->
        match decl with
        | `Local, `Variable init -> Some (name, init)
        | _, `Variable _ -> report_error "only local variables supported"
        | _ -> None)
      decls
  in
  let env =
    List.fold_left (fun env (name, _) -> add_local env name) env locals
  in

  let functions =
    List.filter_map
      (fun (name, decl) ->
        match decl with
        | `Local, `Fun (args, body) -> Some (name, (args, body))
        | _, `Fun _ -> report_error "only local functions supported"
        | _ -> None)
      decls
  in
  let env = env#allocate_functions @@ List.map fst functions in
  let env =
    List.fold_left
      (fun env (name, (args, body)) ->
        match body with
        | Expr.Scope (decls, instr) ->
            let decls =
              List.map (fun arg -> (arg, (`Local, `Variable None))) args @ decls
            in
            let env_after_function, code =
              compile_list env#enter_function (Expr.Scope (decls, instr))
            in
            let locals_count =
              env_after_function#get_locals_count - List.length args
            in
            let env = env_after_function#exit_function env in
            let t =
              Wt.(FuncT (List.map (fun _ -> any_type) args, [ any_type ]))
            in
            env#place_function name t locals_count code
        | _ -> report_error "expected scope as function root")
      env functions
  in

  let env, locals_init_code =
    List.fold_left
      (fun (env, acc) (name, instr) ->
        let env, code = compile_list env instr in
        (env#eat_from_stack, acc @ code @ [ init_local env name ]))
      (env, [])
      (List.filter_map
         (fun (name, init) ->
           match init with Some i -> Some (name, i) | _ -> None)
         locals)
  in

  let env, code = compile_list env instr in
  (env, locals_init_code @ code)

let compile ast =
  let env = new env in
  match ast with
  | Expr.Scope (decls, instr) ->
      let _, env =
        env#add_function_import "write" (FuncT ([ any_type ], [ any_type ]))
      in
      let _, env = env#add_function_import "read" (FuncT ([], [ any_type ])) in

      let env, code =
        compile_scope decls (Expr.Ignore instr)
          (fun env name -> snd (env#add_global name))
          (fun env name ->
            match env#get name with
            | Some (Global index) -> phrase @@ Wa.GlobalSet (get_idx @@ index)
            | _ -> report_error "global was not added properly")
          env
      in
      let _, env =
        env#add_function "main" (FuncT ([], [])) env#get_locals_count code
      in
      let env = env#export_function "main" in
      env#assemble_module
  | _ -> report_error "expected root scope"

let genast _ ((imports, _), p) = compile p

let build cmd prog =
  let module' = genast cmd prog in
  let oc = open_out (cmd#basename ^ ".wast") in
  Wasm.Print.module_ oc 80 module';
  close_out oc;
  cmd#dump_file "wasm" (Wasm.Encode.encode module')
