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
let any_ref_type = Wt.(NoNull, AnyHT)
let any_type = Wt.(RefT (NoNull, AnyHT))
let ref_type_of n = Wt.(NoNull, VarHT (StatX (Int32.of_int n)))

let string_type =
  Wt.(
    RecT
      [
        SubT (Final, [], DefArrayT (ArrayT (FieldT (Var, PackStorageT Pack8))));
      ])

let array_type =
  Wt.(
    RecT
      [
        SubT (Final, [], DefArrayT (ArrayT (FieldT (Var, ValStorageT any_type))));
      ])

let sexp_type array_type_idx =
  Wt.(
    RecT
      [
        SubT
          ( Final,
            [],
            DefStructT
              (StructT
                 [
                   FieldT (Cons, ValStorageT (NumT I32T));
                   FieldT (Cons, ValStorageT (RefT (ref_type_of array_type_idx)));
                 ]) );
      ])

let unbox = [ phrase @@ Wa.RefCast (NoNull, I31HT); phrase @@ Wa.I31Get SX ]
let box = [ phrase @@ Wa.RefI31 ]

let hash tag =
  let chars =
    "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'"
  in
  let h = Stdlib.ref 0 in
  for i = 0 to min (String.length tag - 1) 4 do
    h := (!h lsl 6) lor String.index chars tag.[i]
  done;
  !h

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
  object
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
    val datas = []
    val globals = 0
    val locals = 0
    val exports = []
    val scopes = new lexical_scopes
    val secret_scope = M.empty
    val temp_locals = []
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

    method add_secret_function name t locals_count body =
      match M.find_opt name secret_scope with
      | None ->
          let type_idx, types =
            upsert Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) types
          in
          let func_idx = List.length functions in
          ( func_idx,
            {<types
             ; functions = functions @ [ Func (type_idx, locals_count, body) ]
             ; secret_scope = M.add name func_idx secret_scope>} )
      | Some func_idx -> (func_idx, self)

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

    method get_temp_locals amount =
      let locals_to_add = max (amount - List.length temp_locals) 0 in
      let temp_locals =
        temp_locals @ List.init locals_to_add (fun i -> locals + i)
      in
      (temp_locals, {<temp_locals; locals = locals + locals_to_add>})

    method upsert_data str =
      let data_idx, datas = upsert str datas in
      (data_idx, {<datas>})

    method get_scopes_ = scopes
    method get name = scopes#get name

    method enter_function =
      {<scopes = scopes#enter_function
       ; locals = 0
       ; temp_locals = []
       ; stack_depth = 0>}

    method exit_function (old_env : env) =
      {<scopes = old_env#get_scopes_
       ; locals = old_env#get_locals_count
       ; temp_locals = fst (old_env#get_temp_locals 0)
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
      let datas =
        List.map
          (fun s -> phrase @@ Wa.{ dinit = s; dmode = phrase @@ Passive })
          datas
      in
      phrase
        Wa.{ empty_module with imports; funcs; types; globals; exports; datas }
  end

let ensure_elem_exists env =
  let block_type_idx, env =
    env#upsert_type
      Wt.(
        RecT [ SubT (Final, [], DefFuncT (FuncT ([ any_type ], [ any_type ]))) ])
  in
  let string_type_idx, env = env#upsert_type string_type in
  let array_type_idx, env = env#upsert_type array_type in
  let sexp_type_idx, env = env#upsert_type (sexp_type array_type_idx) in
  let elem_func_idx, env =
    env#add_secret_function "elem"
      (* args: array, index *)
      (* result: value *)
      (Wt.FuncT ([ any_type; NumT I32T ], [ any_type ]))
      0
      [
        phrase @@ Wa.LocalGet (get_idx 0);
        phrase
        @@ Wa.Block
             ( VarBlockType (get_idx block_type_idx),
               [
                 phrase
                 @@ Wa.BrOnCastFail
                      (get_idx 0, any_ref_type, ref_type_of sexp_type_idx);
                 phrase @@ Wa.StructGet (get_idx sexp_type_idx, get_idx 1, None);
                 phrase @@ Wa.LocalGet (get_idx 1);
                 phrase @@ Wa.ArrayGet (get_idx array_type_idx, None);
                 phrase @@ Wa.Return;
               ] );
        phrase
        @@ Wa.Block
             ( VarBlockType (get_idx block_type_idx),
               [
                 phrase
                 @@ Wa.BrOnCastFail
                      (get_idx 0, any_ref_type, ref_type_of string_type_idx);
                 phrase @@ Wa.LocalGet (get_idx 1);
                 phrase @@ Wa.ArrayGet (get_idx string_type_idx, Some SX);
               ]
               @ box
               @ [ phrase @@ Wa.Return ] );
        phrase @@ Wa.RefCast (ref_type_of array_type_idx);
        phrase @@ Wa.LocalGet (get_idx 1);
        phrase @@ Wa.ArrayGet (get_idx array_type_idx, None);
      ]
  in
  (elem_func_idx, env)

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
  | Expr.Assign (Expr.ElemRef (arr, index), instr) ->
      let block_type_idx, env =
        env#upsert_type
          Wt.(
            RecT
              [
                SubT (Final, [], DefFuncT (FuncT ([ any_type ], [ any_type ])));
              ])
      in
      let string_type_idx, env = env#upsert_type string_type in
      let array_type_idx, env = env#upsert_type array_type in
      let sexp_type_idx, env = env#upsert_type (sexp_type array_type_idx) in
      let assign_func_idx, env =
        env#add_secret_function "assign"
          (* args: array, index, value *)
          (* result: value *)
          (Wt.FuncT ([ any_type; NumT I32T; any_type ], [ any_type ]))
          0
          [
            phrase @@ Wa.LocalGet (get_idx 0);
            phrase
            @@ Wa.Block
                 ( VarBlockType (get_idx block_type_idx),
                   [
                     phrase
                     @@ Wa.BrOnCastFail
                          (get_idx 0, any_ref_type, ref_type_of sexp_type_idx);
                     phrase
                     @@ Wa.StructGet (get_idx sexp_type_idx, get_idx 1, None);
                     phrase @@ Wa.LocalGet (get_idx 1);
                     phrase @@ Wa.LocalGet (get_idx 2);
                     phrase @@ Wa.ArraySet (get_idx array_type_idx);
                     phrase @@ Wa.LocalGet (get_idx 2);
                     phrase @@ Wa.Return;
                   ] );
            phrase
            @@ Wa.Block
                 ( VarBlockType (get_idx block_type_idx),
                   [
                     phrase
                     @@ Wa.BrOnCastFail
                          (get_idx 0, any_ref_type, ref_type_of string_type_idx);
                     phrase @@ Wa.LocalGet (get_idx 1);
                     phrase @@ Wa.LocalGet (get_idx 2);
                   ]
                   @ unbox
                   @ [
                       phrase @@ Wa.ArraySet (get_idx string_type_idx);
                       phrase @@ Wa.LocalGet (get_idx 2);
                       phrase @@ Wa.Return;
                     ] );
            phrase @@ Wa.RefCast (ref_type_of array_type_idx);
            phrase @@ Wa.LocalGet (get_idx 1);
            phrase @@ Wa.LocalGet (get_idx 2);
            phrase @@ Wa.ArraySet (get_idx array_type_idx);
            phrase @@ Wa.LocalGet (get_idx 2);
          ]
      in
      let env, arr_code = compile_list env arr in
      let env, index_code = compile_list env index in
      let env, code = compile_list env instr in
      let env = env#eat_n_from_stack 2 in
      ( env,
        arr_code @ index_code @ unbox @ code
        @ [ phrase @@ Wa.Call (get_idx assign_func_idx) ] )
  | Expr.If (c, s1, s2) ->
      let env', c_code = compile_list env c in
      let env = env'#reset_stack_depth env in
      let env', s1_code = compile_list env s1 in
      let env = env'#reset_stack_depth env in
      let env', s2_code = compile_list env' s2 in
      let t =
        if env'#compare_stack_depth env = 0 then Wa.ValBlockType None
        else Wa.ValBlockType (Some any_type)
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
                          c_code @ unbox
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
                 body_code @ c_code @ unbox @ [ phrase @@ Wa.BrIf (get_idx 0) ]
               );
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
  | Expr.String str ->
      let type_idx, env = env#upsert_type string_type in
      let data_idx, env = env#upsert_data str in
      let env = env#put_on_stack in
      let size = String.length str in
      let instr = Wa.ArrayNewData (get_idx type_idx, get_idx data_idx) in
      (env, [ phrase @@ get_const 0; phrase @@ get_const size; phrase @@ instr ])
  | Expr.Elem (arr, index) ->
      let elem_func_idx, env = ensure_elem_exists env in
      let env, arr_code = compile_list env arr in
      let env, index_code = compile_list env index in
      let env = env#eat_from_stack in
      ( env,
        arr_code @ index_code @ unbox
        @ [ phrase @@ Wa.Call (get_idx elem_func_idx) ] )
  | Expr.Array elems ->
      let array_type_idx, env = env#upsert_type array_type in
      let env, code =
        List.fold_left
          (fun (env, acc) elem ->
            let env, code = compile_list env elem in
            (env, acc @ code))
          (env, []) elems
      in
      let elems_length = List.length elems in
      let env = env#eat_n_from_stack elems_length in
      let env = env#put_on_stack in
      ( env,
        code
        @ [
            phrase
            @@ Wa.ArrayNewFixed
                 (get_idx array_type_idx, Int32.of_int elems_length);
          ] )
  | Expr.Sexp (tag, vals) ->
      let hash_value = hash tag in
      let array_type_idx, env = env#upsert_type array_type in
      let sexp_type_idx, env = env#upsert_type (sexp_type array_type_idx) in
      let env = env#put_on_stack in
      let env, vals_code =
        List.fold_left
          (fun (env, acc) elem ->
            let env, code = compile_list env elem in
            (env, acc @ code))
          (env, []) vals
      in
      let vals_length = List.length vals in
      let env = env#eat_n_from_stack (vals_length + 1) in
      let env = env#put_on_stack in
      ( env,
        [ phrase @@ get_const hash_value ]
        @ vals_code
        @ [
            phrase
            @@ Wa.ArrayNewFixed
                 (get_idx array_type_idx, Int32.of_int vals_length);
            phrase @@ Wa.StructNew (get_idx sexp_type_idx, Explicit);
          ] )
  | Expr.Case (value, patterns, _, attr) ->
      let env, value_code = compile_list env value in
      let temp_locals, env = env#get_temp_locals 1 in
      let value_temp = List.hd temp_locals in
      let env = env#eat_from_stack in
      let elem_func_idx, env = ensure_elem_exists env in
      let rec compile_pattern env pattern path =
        let elem_code =
          [ phrase @@ Wa.LocalGet (get_idx value_temp) ]
          @ (List.map
               (fun i ->
                 [
                   phrase @@ get_const i;
                   phrase @@ Wa.Call (get_idx elem_func_idx);
                 ])
               path
            |> List.flatten)
        in
        match pattern with
        | Pattern.Sexp (tag, elems) ->
            let array_type_idx, env = env#upsert_type array_type in
            let sexp_type_idx, env =
              env#upsert_type (sexp_type array_type_idx)
            in
            let check_code =
              elem_code
              @ [
                  phrase @@ Wa.RefTest (ref_type_of sexp_type_idx);
                  phrase @@ get_test_op Eqz;
                  phrase @@ Wa.BrIf (get_idx 0);
                ]
              @ elem_code
              @ [
                  phrase @@ Wa.RefCast (ref_type_of sexp_type_idx);
                  phrase @@ Wa.StructGet (get_idx sexp_type_idx, get_idx 0, None);
                  phrase @@ get_const (hash tag);
                  phrase @@ get_compare Ne;
                  phrase @@ Wa.BrIf (get_idx 0);
                ]
              @ elem_code
              @ [
                  phrase @@ Wa.RefCast (ref_type_of sexp_type_idx);
                  phrase @@ Wa.StructGet (get_idx sexp_type_idx, get_idx 1, None);
                  phrase @@ Wa.ArrayLen;
                  phrase @@ get_const (List.length elems);
                  phrase @@ get_compare Ne;
                  phrase @@ Wa.BrIf (get_idx 0);
                ]
            in
            let bindings = [] in
            let env, check_code, bindings =
              elems
              |> List.mapi (fun i elem -> (i, elem))
              |> List.fold_left
                   (fun (env, check_code, bindings) (i, elem) ->
                     let env, check_code', bindings' =
                       compile_pattern env elem (path @ [ i ])
                     in
                     (env, check_code @ check_code', bindings @ bindings'))
                   (env, check_code, bindings)
            in
            (env, check_code, bindings)
        | Pattern.Const n ->
            let check_code =
              elem_code
              @ [
                  phrase @@ Wa.RefTest (NoNull, I31HT);
                  phrase @@ get_test_op Eqz;
                  phrase @@ Wa.BrIf (get_idx 0);
                ]
              @ elem_code @ unbox
              @ [
                  phrase @@ get_const n;
                  phrase @@ get_compare Ne;
                  phrase @@ Wa.BrIf (get_idx 0);
                ]
            in
            (env, check_code, [])
        | Pattern.Named (name, inner) ->
            let bindings = [ (name, elem_code) ] in
            let env, check_code, bindings' = compile_pattern env inner path in
            (env, check_code, bindings @ bindings')
        | Pattern.Wildcard -> (env, [], [])
        | _ ->
            report_error
            @@ Printf.sprintf "unsupported pattern %s\n"
                 (GT.show Pattern.t pattern)
      in
      let env, blocks =
        patterns
        |> List.fold_left
             (fun (env, blocks) (p, e) ->
               let env = env#enter_scope in
               let env, check_code, bindings = compile_pattern env p [] in
               let env, bindings_code =
                 List.fold_left
                   (fun (env, result) (name, code) ->
                     let idx, env = env#add_local name in
                     ( env,
                       result @ code @ [ phrase @@ Wa.LocalSet (get_idx idx) ]
                     ))
                   (env, []) bindings
               in
               let env, block_code = compile_list env e in
               let block =
                 phrase
                 @@ Wa.Block
                      ( ValBlockType None,
                        check_code @ bindings_code @ block_code
                        @ [ phrase @@ Wa.Br (get_idx 1) ] )
               in
               (env#exit_scope, blocks @ [ block ]))
             (env, [])
      in
      ( env,
        value_code
        @ [
            phrase @@ Wa.LocalSet (get_idx value_temp);
            phrase
            @@ Wa.Block
                 ( ValBlockType
                     (match attr with Void -> None | _ -> Some any_type),
                   blocks @ [ phrase @@ Wa.Unreachable ] );
          ] )
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

let add_runtime env =
  let block_type_idx, env =
    env#upsert_type
      Wt.(
        RecT [ SubT (Final, [], DefFuncT (FuncT ([ any_type ], [ any_type ]))) ])
  in
  let array_type_idx, env = env#upsert_type array_type in
  let sexp_type_idx, env = env#upsert_type (sexp_type array_type_idx) in
  let _, env =
    env#add_function "length"
      (Wt.FuncT ([ any_type ], [ any_type ]))
      0
      [
        phrase @@ Wa.LocalGet (get_idx 0);
        phrase
        @@ Wa.Block
             ( VarBlockType (get_idx block_type_idx),
               [
                 phrase
                 @@ Wa.BrOnCastFail
                      (get_idx 0, any_ref_type, ref_type_of sexp_type_idx);
                 phrase @@ Wa.StructGet (get_idx sexp_type_idx, get_idx 1, None);
                 phrase @@ Wa.ArrayLen;
                 phrase @@ Wa.RefI31;
                 phrase @@ Wa.Return;
               ] );
        phrase @@ Wa.RefCast (NoNull, ArrayHT);
        phrase @@ Wa.ArrayLen;
        phrase @@ Wa.RefI31;
      ]
  in
  env

let compile ast =
  let env = new env in
  match ast with
  | Expr.Scope (decls, instr) ->
      let _, env =
        env#add_function_import "write" (FuncT ([ any_type ], [ any_type ]))
      in
      let _, env = env#add_function_import "read" (FuncT ([], [ any_type ])) in

      let env = add_runtime env in

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

let genast _ ((_, _), p) = compile p

let build cmd prog =
  let module' = genast cmd prog in
  let oc = open_out (cmd#basename ^ ".wast") in
  Wasm.Print.module_ oc 80 module';
  close_out oc;
  Wasm.Valid.check_module module';
  cmd#dump_file "wasm" (Wasm.Encode.encode module')
