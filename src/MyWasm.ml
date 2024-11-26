open GT
open Language
module Wa = Wasm.Ast
module Wt = Wasm.Types
module M = Map.Make (String)
module Mi = Map.Make (Int)
module Si = Set.Make (Int)

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

let stack_ref_type =
  Wt.RecT
    [
      SubT
        ( Final,
          [],
          DefStructT
            (StructT
               [
                 FieldT (Cons, ValStorageT any_type);
                 FieldT (Cons, ValStorageT (NumT I32T));
               ]) );
    ]

let closure_type array_type_idx =
  Wt.RecT
    [
      SubT
        ( Final,
          [],
          DefStructT
            (StructT
               [
                 FieldT (Cons, ValStorageT (RefT (NoNull, FuncHT)));
                 FieldT (Cons, ValStorageT (RefT (ref_type_of array_type_idx)));
               ]) );
    ]

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

type w_value =
  | Global of int
  | Local of int * int
  | Closure of int * int
  | Callable of int
[@@deriving gt ~options:{ show }]

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

let rec get_last_2 = function
  | [] -> raise (Failure "not expected empty list in get_last_2")
  | _ :: [] -> raise (Failure "not expected list of 1 element in get_last_2")
  | [ x; y ] -> [ x; y ]
  | _ :: xs -> get_last_2 xs

let rec replace idx value = function
  | [] -> raise (Failure "length exceeded in replace")
  | x :: xs -> if idx = 0 then value :: xs else x :: replace (idx - 1) value xs

type value_locs_show = (int * (int * w_value) list) list
[@@deriving gt ~options:{ show }]

type call_map_show = (int * int list) list [@@deriving gt ~options:{ show }]

(* result is append only, not dependent on compilation state *)
module Result = struct
  type t = {
    types : Wt.rec_type list;
    functions : w_func list;
    value_locs : w_value Mi.t Mi.t;
    call_map : Si.t Mi.t;
    datas : string list;
    globals : int;
    exports : w_export list;
    helpers : int M.t;
    all_locals : int;
    declared_func_refs : Si.t;
  }

  let empty =
    {
      types = [];
      functions = [];
      value_locs = Mi.empty;
      call_map = Mi.empty;
      datas = [];
      globals = 0;
      exports = [];
      helpers = M.empty;
      all_locals = 0;
      declared_func_refs = Si.empty;
    }

  let upsert_type t result =
    let type_idx, types = upsert t result.types in
    (type_idx, { result with types })

  let add_function_import name t result =
    if
      is_last
        (function ImportFunc (_, _) -> false | _ -> true)
        result.functions
    then report_error "all imports should be added before other functions"
    else
      let type_idx, types =
        upsert Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) result.types
      in
      let func_idx = List.length result.functions in
      let functions = result.functions @ [ ImportFunc (name, type_idx) ] in
      (func_idx, { result with types; functions })

  let allocate_functions n result =
    let start_idx = List.length result.functions in
    let functions = result.functions @ List.init n (fun _ -> Func (0, 0, [])) in
    (start_idx, { result with functions })

  let add_or_place_function idx t locals_count body value_locs call_map result =
    let type_idx, types =
      upsert Wt.(RecT [ SubT (Final, [], DefFuncT t) ]) result.types
    in
    let func = Func (type_idx, locals_count, body) in
    let func_idx =
      idx |> Option.value ~default:(List.length result.functions)
    in
    let functions =
      match idx with
      | Some func_idx -> replace func_idx func result.functions
      | None -> result.functions @ [ func ]
    in
    let value_locs = Mi.add func_idx value_locs result.value_locs in
    let call_map = Mi.add func_idx call_map result.call_map in
    (func_idx, { result with types; functions; value_locs; call_map })

  let upsert_helper name t locals_count body result =
    match M.find_opt name result.helpers with
    | None ->
        let func_idx, result =
          add_or_place_function None t locals_count body Mi.empty Si.empty
            result
        in
        let helpers = M.add name func_idx result.helpers in
        (func_idx, { result with helpers })
    | Some func_idx -> (func_idx, result)

  let export_function name idx result =
    let exports = ExportFunc (name, idx) :: result.exports in
    { result with exports }

  let add_global result =
    (result.globals, { result with globals = result.globals + 1 })

  let upsert_data str result =
    let data_idx, datas = upsert str result.datas in
    (data_idx, { result with datas })

  let add_local result =
    (result.all_locals, { result with all_locals = result.all_locals + 1 })

  let register_call func_idx result =
    let declared_func_refs = Si.add func_idx result.declared_func_refs in
    { result with declared_func_refs }

  let expand_closures result =
    let should_stop = Stdlib.ref false in
    let value_locs = Stdlib.ref result.value_locs in
    let filter_closures locs =
      Mi.filter
        (fun _ loc -> match loc with Closure (_, _) -> true | _ -> false)
        locs
    in
    let count_closures locs = Mi.cardinal (filter_closures locs) in
    let expand from_idx to_idx =
      let from_locs =
        Mi.find_opt from_idx !value_locs |> Option.value ~default:Mi.empty
      in
      let from_closures = filter_closures from_locs in
      let to_locs = Mi.find to_idx !value_locs in
      let to_locs, modified =
        Mi.fold
          (fun local_idx _ (to_locs, modified) ->
            if Mi.mem local_idx to_locs then (to_locs, modified)
            else
              let closure = Closure (count_closures to_locs, local_idx) in
              let to_locs = Mi.add local_idx closure to_locs in
              (to_locs, true))
          from_closures (to_locs, false)
      in
      value_locs := Mi.add to_idx to_locs !value_locs;
      modified
    in
    while not !should_stop do
      let modified = Stdlib.ref false in
      Mi.iter
        (fun to_idx callees ->
          Si.iter
            (fun from_idx -> modified := expand from_idx to_idx || !modified)
            callees)
        result.call_map;
      should_stop := not !modified
    done;
    { result with value_locs = !value_locs }

  let second_pass result =
    let array_type_idx, result = upsert_type array_type result in
    let closure_type_idx, result =
      upsert_type (closure_type array_type_idx) result
    in
    let create_closure in_idx idx =
      let callee_locs =
        result.value_locs |> Mi.find_opt idx |> Option.value ~default:Mi.empty
      in
      let caller_locs = result.value_locs |> Mi.find in_idx in
      let to_collect =
        Mi.fold (fun _ loc acc -> loc :: acc) callee_locs []
        |> List.filter (fun loc ->
               match loc with Closure (_, _) -> true | _ -> false)
        |> List.sort (fun a b ->
               match (a, b) with
               | Closure (a, _), Closure (b, _) -> a - b
               | _ ->
                   report_error
                     "this is impossible because the list is filtered")
      in
      let collect_locs =
        to_collect
        |> List.map (fun loc ->
               match loc with
               | Closure (_, local_idx) -> Mi.find local_idx caller_locs
               | _ -> report_error "still impossible")
      in
      let collect_code =
        List.fold_left
          (fun acc loc ->
            let code =
              match loc with
              | Local (index, _) -> [ phrase @@ Wa.LocalGet (get_idx index) ]
              | Closure (index, _) ->
                  [
                    phrase @@ Wa.LocalGet (get_idx 0);
                    phrase @@ get_const index;
                    phrase @@ Wa.ArrayGet (get_idx array_type_idx, None);
                  ]
              | _ -> report_error "mission impossible"
            in
            acc @ code)
          [] collect_locs
      in
      [ phrase @@ Wa.RefFunc (get_idx idx) ]
      @ collect_code
      @ [
          phrase
          @@ Wa.ArrayNewFixed
               (get_idx array_type_idx, Int32.of_int (List.length collect_locs));
          phrase @@ Wa.StructNew (get_idx closure_type_idx, Explicit);
        ]
    in
    let rec map_instr idx instr =
      match Wasm.Source.(it instr) with
      | Wa.Block (t, body) -> [ phrase @@ Wa.Block (t, map_body idx body) ]
      | Wa.Loop (t, body) -> [ phrase @@ Wa.Loop (t, map_body idx body) ]
      | Wa.If (t, body1, body2) ->
          [ phrase @@ Wa.If (t, map_body idx body1, map_body idx body2) ]
      | Wa.ElemDrop func_idx ->
          create_closure idx (Int32.to_int Wasm.Source.(it func_idx))
      | other -> [ phrase @@ other ]
    and map_body idx body =
      body |> List.map (fun instr -> map_instr idx instr) |> List.flatten
    in
    let functions =
      result.functions
      |> List.mapi (fun idx f ->
             match f with
             | Func (type_idx, locals_count, body) ->
                 Func (type_idx, locals_count, map_body idx body)
             | other -> other)
    in
    { result with functions }

  let show_value_locs result =
    let value_locs_showable =
      Mi.to_seq result.value_locs
      |> List.of_seq
      |> List.map (fun (i, m) -> (i, Mi.to_seq m |> List.of_seq))
    in
    show value_locs_show value_locs_showable

  let show_call_map result =
    let call_map_showable =
      Mi.to_seq result.call_map |> List.of_seq
      |> List.map (fun (i, s) -> (i, Si.to_seq s |> List.of_seq))
    in
    show call_map_show call_map_showable

  let assemble_module result =
    let types = List.map phrase result.types in
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
        result.functions
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
        result.functions
    in
    let globals =
      List.init result.globals (fun _ ->
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
        result.exports
    in
    let datas =
      List.map
        (fun s -> phrase @@ Wa.{ dinit = s; dmode = phrase @@ Passive })
        result.datas
    in
    let elems =
      Si.fold
        (fun idx acc ->
          (phrase
          @@ Wa.
               {
                 etype = (Null, FuncHT);
                 einit = [ phrase @@ [ phrase @@ Wa.RefFunc (get_idx idx) ] ];
                 emode = phrase Declarative;
               })
          :: acc)
        result.declared_func_refs []
    in
    phrase
      Wa.
        {
          empty_module with
          imports;
          funcs;
          types;
          globals;
          exports;
          datas;
          elems;
        }
end

type scopes_show = (string * w_value) list list
[@@deriving gt ~options:{ show }]

(* env is specific to some part of compilation, can rollback to earlier env *)
module Env = struct
  type t = {
    result : Result.t;
    scopes : w_value M.t list;
    value_locs : w_value Mi.t;
    call_map : Si.t;
    locals : int;
    closures : int;
    is_collecting_refs : bool;
    refs : w_value list;
  }

  let empty =
    {
      result = Result.empty;
      scopes = [];
      value_locs = Mi.empty;
      call_map = Si.empty;
      locals = 0;
      closures = 0;
      is_collecting_refs = false;
      refs = [];
    }

  let upsert_type t env =
    let type_idx, result = Result.upsert_type t env.result in
    (type_idx, { env with result })

  let bind name v scopes =
    if M.mem name (List.hd scopes) then
      report_error @@ Printf.sprintf "name \"%s\" is already defined" name
    else M.add name v (List.hd scopes) :: List.tl scopes

  let get name env =
    let rec inner name = function
      | [] -> (None, [], env.closures, env.value_locs)
      | x :: xs -> (
          match M.find_opt name x with
          | None ->
              let result, xs, closures, value_locs = inner name xs in
              (result, x :: xs, closures, value_locs)
          | Some found -> (
              match found with
              | Closure (-1, local_idx) ->
                  let closure = Closure (env.closures, local_idx) in
                  let value_locs = Mi.add local_idx closure env.value_locs in
                  ( Some closure,
                    M.add name closure x :: xs,
                    env.closures + 1,
                    value_locs )
              | other -> (Some other, x :: xs, env.closures, env.value_locs)))
    in
    let result, scopes, closures, value_locs = inner name env.scopes in
    (result, { env with scopes; closures; value_locs })

  let add_function_import name t env =
    let func_idx, result = Result.add_function_import name t env.result in
    let scopes = bind name (Callable func_idx) env.scopes in
    { env with result; scopes }

  let allocate_functions names env =
    let start_idx, result =
      Result.allocate_functions (List.length names) env.result
    in
    let _, scopes =
      List.fold_left
        (fun (idx, scopes) name -> (idx + 1, bind name (Callable idx) scopes))
        (start_idx, env.scopes) names
    in
    { env with result; scopes }

  let place_function name t locals_count body value_locs call_map env =
    let loc, env = get name env in
    let func_idx =
      match loc with
      | Some (Callable x) -> x
      | _ ->
          report_error
          @@ Printf.sprintf "function \"%s\" not allocated before placement"
               name
    in
    let _, result =
      Result.add_or_place_function (Some func_idx) t locals_count body
        value_locs call_map env.result
    in
    (func_idx, { env with result })

  let add_function name t locals_count body value_locs call_map env =
    let func_idx, result =
      env.result
      |> Result.add_or_place_function None t locals_count body value_locs
           call_map
    in
    let scopes =
      match name with
      | Some name -> env.scopes |> bind name (Callable func_idx)
      | _ -> env.scopes
    in
    (func_idx, { env with result; scopes })

  let upsert_helper name t locals_count body env =
    let func_idx, result =
      Result.upsert_helper name t locals_count body env.result
    in
    (func_idx, { env with result })

  let export_function name idx env =
    let result = Result.export_function name idx env.result in
    { env with result }

  let add_global name env =
    let idx, result = Result.add_global env.result in
    let scopes = env.scopes |> bind name (Global idx) in
    (idx, { env with result; scopes })

  let add_local name env =
    let local_idx, result = Result.add_local env.result in
    let value_locs =
      Mi.add local_idx (Local (env.locals, local_idx)) env.value_locs
    in
    let scopes = env.scopes |> bind name (Local (env.locals, local_idx)) in
    ( env.locals,
      { env with locals = env.locals + 1; scopes; result; value_locs } )

  let add_unnamed_local env = (env.locals, { env with locals = env.locals + 1 })

  let upsert_data str env =
    let data_idx, result = Result.upsert_data str env.result in
    (data_idx, { env with result })

  let enter_function env =
    let rec inner = function
      | [] -> []
      | x :: xs ->
          M.map
            (function
              | Local (_, local_idx) -> Closure (-1, local_idx) | other -> other)
            x
          :: inner xs
    in
    let scopes = M.empty :: inner env.scopes in
    { empty with result = env.result; scopes }

  let exit_function prev_env env = { prev_env with result = env.result }

  let enter_scope env =
    let scopes = M.empty :: env.scopes in
    { env with scopes }

  let exit_scope env =
    let scopes = List.tl env.scopes in
    { env with scopes }

  let get_locals_count env = env.locals
  let start_collecting_refs env = { env with is_collecting_refs = true }

  let stop_collecting_refs env =
    (env.refs, { env with is_collecting_refs = false; refs = [] })

  let add_ref ref env =
    if not env.is_collecting_refs then
      report_error "tried to take ref outside of assignment operator"
    else
      let refs = env.refs @ [ ref ] in
      (List.length env.refs, { env with refs })

  let register_call func_idx env =
    let result = Result.register_call func_idx env.result in
    let call_map = Si.add func_idx env.call_map in
    { env with call_map; result }

  let get_call_map env = env.call_map
  let get_value_locs env = env.value_locs

  let is_global_func name env =
    let global_scopes = get_last_2 env.scopes in
    let rec inner name = function
      | [] -> None
      | x :: xs -> (
          match M.find_opt name x with None -> inner name xs | found -> found)
    in
    match inner name global_scopes with Some (Callable _) -> true | _ -> false

  let expand_closures env =
    let result = Result.expand_closures env.result in
    { env with result }

  let second_pass env =
    let result = Result.second_pass env.result in
    { env with result }

  let show_scopes env =
    let scopes_showable =
      env.scopes |> List.map (fun m -> M.to_seq m |> List.of_seq)
    in
    show scopes_show scopes_showable

  let assemble_module env = Result.assemble_module env.result
end

let add_helper_elem env =
  let block_type_idx, env =
    env
    |> Env.upsert_type
         Wt.(
           RecT
             [ SubT (Final, [], DefFuncT (FuncT ([ any_type ], [ any_type ]))) ])
  in
  let string_type_idx, env = env |> Env.upsert_type string_type in
  let array_type_idx, env = env |> Env.upsert_type array_type in
  let sexp_type_idx, env = env |> Env.upsert_type (sexp_type array_type_idx) in
  env
  |> Env.upsert_helper "elem"
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

let add_helper_assign env =
  let block_type_idx, env =
    env
    |> Env.upsert_type
         Wt.(
           RecT
             [ SubT (Final, [], DefFuncT (FuncT ([ any_type ], [ any_type ]))) ])
  in
  let string_type_idx, env = env |> Env.upsert_type string_type in
  let array_type_idx, env = env |> Env.upsert_type array_type in
  let sexp_type_idx, env = env |> Env.upsert_type (sexp_type array_type_idx) in
  env
  |> Env.upsert_helper "assign"
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
                  phrase @@ Wa.StructGet (get_idx sexp_type_idx, get_idx 1, None);
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

let rec compile_list env ast =
  match ast with
  | Expr.Call (Expr.Var name, args) when Env.is_global_func name env -> (
      let loc, env = env |> Env.get name in
      match loc with
      | Some (Callable func_idx) ->
          let array_type_idx, env = env |> Env.upsert_type array_type in
          let args_code, env =
            List.fold_left
              (fun (acc, env) arg ->
                let env, code = compile_list env arg in
                (acc @ code, env))
              ([], env) args
          in
          ( env,
            [
              phrase @@ Wa.ArrayNewFixed (get_idx array_type_idx, Int32.of_int 0);
            ]
            @ args_code
            @ [ phrase @@ Wa.Call (get_idx func_idx) ] )
      | _ -> report_error "simplified function call failed")
  | Expr.Call (name, args) ->
      let env, name_code = compile_list env name in
      let name_temp, env = env |> Env.add_unnamed_local in
      let array_type_idx, env = env |> Env.upsert_type array_type in
      let closure_type_idx, env =
        env |> Env.upsert_type (closure_type array_type_idx)
      in
      let args_code, env =
        List.fold_left
          (fun (acc, env) arg ->
            let env, code = compile_list env arg in
            (acc @ code, env))
          ([], env) args
      in
      let func_type =
        Wt.(
          FuncT
            ( RefT (ref_type_of array_type_idx)
              :: List.init (List.length args) (fun _ -> any_type),
              [ any_type ] ))
      in
      let func_type_idx, env =
        env
        |> Env.upsert_type Wt.(RecT [ SubT (Final, [], DefFuncT func_type) ])
      in
      ( env,
        name_code
        @ [
            phrase @@ Wa.LocalTee (get_idx name_temp);
            phrase @@ Wa.RefCast (ref_type_of closure_type_idx);
            phrase @@ Wa.StructGet (get_idx closure_type_idx, get_idx 1, None);
          ]
        @ args_code
        @ [
            phrase @@ Wa.LocalGet (get_idx name_temp);
            phrase @@ Wa.RefCast (ref_type_of closure_type_idx);
            phrase @@ Wa.StructGet (get_idx closure_type_idx, get_idx 0, None);
            phrase @@ Wa.RefCast (ref_type_of func_type_idx);
            phrase @@ Wa.CallRef (get_idx func_type_idx);
          ] )
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
            let type_idx, env =
              env
              |> Env.upsert_type
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
  | Expr.Const i -> (env, [ phrase @@ get_const i ] @ box)
  | Expr.Skip -> (env, [])
  | Expr.Seq (s1, s2) ->
      let env, code1 = compile_list env s1 in
      let env, code2 = compile_list env s2 in
      (env, code1 @ code2)
  | Expr.Ignore s ->
      let env, code = compile_list env s in
      (env, code @ [ phrase Wa.Drop ])
  | Expr.Var name -> (
      let array_type_idx, env = env |> Env.upsert_type array_type in
      let loc, env = env |> Env.get name in
      match loc with
      | Some (Global index) -> (env, [ phrase @@ Wa.GlobalGet (get_idx index) ])
      | Some (Local (index, _)) ->
          (env, [ phrase @@ Wa.LocalGet (get_idx index) ])
      | Some (Closure (index, _)) ->
          ( env,
            [
              phrase @@ Wa.LocalGet (get_idx 0);
              phrase @@ get_const index;
              phrase @@ Wa.ArrayGet (get_idx array_type_idx, None);
            ] )
      | Some (Callable func_idx) ->
          let env = env |> Env.register_call func_idx in
          (* placeholder for creating a closure in 2nd pass *)
          (env, [ phrase @@ Wa.ElemDrop (get_idx func_idx) ])
      | _ ->
          report_error
          @@ Printf.sprintf "trying to get, var with name \"%s\" not found" name
      )
  | Expr.Assign (Expr.Ref name, instr) -> (
      let assign_func_idx, env = add_helper_assign env in
      let env, code = compile_list env instr in
      let loc, env = env |> Env.get name in
      match loc with
      | Some (Global index) ->
          ( env,
            code
            @ [
                phrase @@ Wa.GlobalSet (get_idx index);
                phrase @@ Wa.GlobalGet (get_idx index);
              ] )
      | Some (Local (index, _)) ->
          (env, code @ [ phrase @@ Wa.LocalTee (get_idx index) ])
      | Some (Closure (index, _)) ->
          ( env,
            [ phrase @@ Wa.LocalGet (get_idx 0); phrase @@ get_const index ]
            @ code
            @ [ phrase @@ Wa.Call (get_idx assign_func_idx) ] )
      | _ ->
          report_error
          @@ Printf.sprintf "trying to set, var with name \"%s\" not found" name
      )
  | Expr.Assign (Expr.ElemRef (arr, index), instr) ->
      let assign_func_idx, env = add_helper_assign env in
      let env, arr_code = compile_list env arr in
      let env, index_code = compile_list env index in
      let env, code = compile_list env instr in
      ( env,
        arr_code @ index_code @ unbox @ code
        @ [ phrase @@ Wa.Call (get_idx assign_func_idx) ] )
  | Expr.Assign (ref, value) ->
      let env = env |> Env.start_collecting_refs in
      let env, ref_code = compile_list env ref in
      let refs, env = env |> Env.stop_collecting_refs in
      let env, value_code = compile_list env value in
      let assign_func_idx, env = add_helper_assign env in
      let array_type_idx, env = env |> Env.upsert_type array_type in
      let type_idx, env = env |> Env.upsert_type stack_ref_type in
      let block_type_idx, env =
        env
        |> Env.upsert_type
             Wt.(RecT [ SubT (Final, [], DefFuncT (FuncT ([ any_type ], []))) ])
      in
      let ref_temp, env = env |> Env.add_unnamed_local in
      let value_temp, env = env |> Env.add_unnamed_local in
      let refs_code =
        refs
        |> List.mapi (fun i r ->
               [ phrase @@ Wa.LocalGet (get_idx ref_temp) ]
               @ unbox
               @ [
                   phrase @@ get_const i;
                   phrase @@ get_compare Wa.I32Op.Eq;
                   phrase
                   @@ Wa.If
                        ( ValBlockType None,
                          (match r with
                          | Global idx ->
                              [
                                phrase @@ Wa.LocalGet (get_idx value_temp);
                                phrase @@ Wa.GlobalSet (get_idx idx);
                              ]
                          | Local (idx, _) ->
                              [
                                phrase @@ Wa.LocalGet (get_idx value_temp);
                                phrase @@ Wa.LocalSet (get_idx idx);
                              ]
                          | Closure (idx, _) ->
                              [
                                phrase @@ Wa.LocalGet (get_idx 0);
                                phrase @@ get_const idx;
                                phrase @@ Wa.LocalGet (get_idx value_temp);
                                phrase @@ Wa.ArraySet (get_idx array_type_idx);
                              ]
                          | _ ->
                              report_error
                                "cannot assign to ref which is not global or \
                                 local or closure")
                          @ [ phrase @@ Wa.Br (get_idx 1) ],
                          [] );
                 ])
        |> List.flatten
      in
      ( env,
        ref_code
        @ [ phrase @@ Wa.LocalSet (get_idx ref_temp) ]
        @ value_code
        @ [
            phrase @@ Wa.LocalSet (get_idx value_temp);
            phrase @@ Wa.LocalGet (get_idx ref_temp);
            phrase @@ Wa.RefCast (ref_type_of type_idx);
            phrase @@ Wa.StructGet (get_idx type_idx, get_idx 0, None);
            phrase @@ Wa.LocalGet (get_idx ref_temp);
            phrase @@ Wa.RefCast (ref_type_of type_idx);
            phrase @@ Wa.StructGet (get_idx type_idx, get_idx 1, None);
            phrase @@ get_const ~-0xbeef;
            phrase @@ get_compare Wa.I32Op.Eq;
            phrase
            @@ Wa.If
                 ( VarBlockType (get_idx block_type_idx),
                   [ phrase @@ Wa.LocalSet (get_idx ref_temp) ] @ refs_code,
                   [
                     phrase @@ Wa.LocalGet (get_idx ref_temp);
                     phrase @@ Wa.RefCast (ref_type_of type_idx);
                     phrase @@ Wa.StructGet (get_idx type_idx, get_idx 1, None);
                     phrase @@ Wa.LocalGet (get_idx value_temp);
                     phrase @@ Wa.Call (get_idx assign_func_idx);
                     phrase @@ Wa.Drop;
                   ] );
            phrase @@ Wa.LocalGet (get_idx value_temp);
          ] )
  | Expr.Ref name ->
      let loc, env = env |> Env.get name in
      let ref =
        match loc with
        | Some l -> l
        | _ ->
            report_error
            @@ Printf.sprintf
                 "trying to get ref, var with name \"%s\" not found" name
      in
      let ref_num, env = env |> Env.add_ref ref in
      let type_idx, env = env |> Env.upsert_type stack_ref_type in
      ( env,
        [ phrase @@ get_const ref_num ]
        @ box
        @ [
            phrase @@ get_const ~-0xbeef;
            phrase @@ Wa.StructNew (get_idx type_idx, Explicit);
          ] )
  | Expr.ElemRef (arr, index) ->
      let env, array_code = compile_list env arr in
      let env, index_code = compile_list env index in
      let type_idx, env = env |> Env.upsert_type stack_ref_type in
      ( env,
        array_code @ index_code @ unbox
        @ [ phrase @@ Wa.StructNew (get_idx type_idx, Explicit) ] )
  | Expr.If (c, s1, s2, atr) ->
      let env, c_code = compile_list env c in
      let env, s1_code = compile_list env s1 in
      let env, s2_code = compile_list env s2 in
      let t =
        match atr with
        | Void -> Wa.ValBlockType None
        | _ -> Wa.ValBlockType (Some any_type)
      in
      (env, c_code @ unbox @ [ phrase @@ Wa.If (t, s1_code, s2_code) ])
  | Expr.While (cond, body) ->
      let env, c_code = compile_list env cond in
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
      let env, c_code = compile_list env cond in
      ( env,
        [
          phrase
          @@ Wa.Loop
               ( ValBlockType None,
                 body_code @ c_code @ unbox @ [ phrase @@ Wa.BrIf (get_idx 0) ]
               );
        ] )
  | Expr.Scope (decls, instr) ->
      let env' = env |> Env.enter_scope in
      let env', code = compile_scope decls instr false env' in
      (env' |> Env.exit_scope, code)
  | Expr.String str ->
      let type_idx, env = env |> Env.upsert_type string_type in
      let data_idx, env = env |> Env.upsert_data str in
      let size = String.length str in
      let instr = Wa.ArrayNewData (get_idx type_idx, get_idx data_idx) in
      (env, [ phrase @@ get_const 0; phrase @@ get_const size; phrase @@ instr ])
  | Expr.Elem (arr, index) ->
      let elem_func_idx, env = add_helper_elem env in
      let env, arr_code = compile_list env arr in
      let env, index_code = compile_list env index in
      ( env,
        arr_code @ index_code @ unbox
        @ [ phrase @@ Wa.Call (get_idx elem_func_idx) ] )
  | Expr.Array elems ->
      let array_type_idx, env = env |> Env.upsert_type array_type in
      let env, code =
        List.fold_left
          (fun (env, acc) elem ->
            let env, code = compile_list env elem in
            (env, acc @ code))
          (env, []) elems
      in
      let elems_length = List.length elems in
      ( env,
        code
        @ [
            phrase
            @@ Wa.ArrayNewFixed
                 (get_idx array_type_idx, Int32.of_int elems_length);
          ] )
  | Expr.Sexp (tag, vals) ->
      let hash_value = hash tag in
      let array_type_idx, env = env |> Env.upsert_type array_type in
      let sexp_type_idx, env =
        env |> Env.upsert_type (sexp_type array_type_idx)
      in
      let env, vals_code =
        List.fold_left
          (fun (env, acc) elem ->
            let env, code = compile_list env elem in
            (env, acc @ code))
          (env, []) vals
      in
      let vals_length = List.length vals in
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
      let value_temp, env = env |> Env.add_unnamed_local in
      let elem_func_idx, env = add_helper_elem env in
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
            let array_type_idx, env = env |> Env.upsert_type array_type in
            let sexp_type_idx, env =
              env |> Env.upsert_type (sexp_type array_type_idx)
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
               let env = env |> Env.enter_scope in
               let env, check_code, bindings = compile_pattern env p [] in
               let env, bindings_code =
                 List.fold_left
                   (fun (env, result) (name, code) ->
                     let idx, env = env |> Env.add_local name in
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
               (env |> Env.exit_scope, blocks @ [ block ]))
             (env, [])
      in
      let env, t =
        match attr with Void -> (env, None) | _ -> (env, Some any_type)
      in
      ( env,
        value_code
        @ [
            phrase @@ Wa.LocalSet (get_idx value_temp);
            phrase
            @@ Wa.Block (ValBlockType t, blocks @ [ phrase @@ Wa.Unreachable ]);
          ] )
  | Expr.Lambda (args, body) ->
      let func_idx, env =
        compile_and_add_function env args body (Env.add_function None)
      in
      let env = env |> Env.register_call func_idx in
      (* placeholder for creating a closure in 2nd pass *)
      (env, [ phrase @@ Wa.ElemDrop (get_idx func_idx) ])
  | _ ->
      report_error
      @@ Printf.sprintf "unsupported structure %s\n" (GT.show Expr.t ast)

and compile_scope decls instr is_top_level env =
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
    List.fold_left
      (fun env (name, _) ->
        if is_top_level then snd (env |> Env.add_global name)
        else snd (env |> Env.add_local name))
      env locals
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
  let env = env |> Env.allocate_functions (List.map fst functions) in
  let env =
    List.fold_left
      (fun env (name, (args, body)) ->
        snd @@ compile_and_add_function env args body (Env.place_function name))
      env functions
  in

  let env, locals_init_code =
    locals
    |> List.map (fun (name, init) ->
           match init with Some i -> (name, i) | _ -> (name, Expr.Const 0))
    |> List.fold_left
         (fun (env, acc) (name, instr) ->
           let env, code = compile_list env instr in
           let loc, env = env |> Env.get name in
           let init_code =
             match loc with
             | Some (Global index) when is_top_level ->
                 phrase @@ Wa.GlobalSet (get_idx @@ index)
             | Some (Local (index, _)) when not is_top_level ->
                 phrase @@ Wa.LocalSet (get_idx @@ index)
             | _ -> report_error "loc was not added properly"
           in
           (env, acc @ code @ [ init_code ]))
         (env, [])
  in

  let env, code = compile_list env instr in
  (env, locals_init_code @ code)

and compile_and_add_function env args body add =
  let array_type_idx, env = env |> Env.upsert_type array_type in
  let env' = Env.enter_function env in
  let _, env' = env' |> Env.add_unnamed_local in
  let env' =
    List.fold_left (fun env' arg -> snd (env' |> Env.add_local arg)) env' args
  in
  let env', code = compile_list env' body in
  let locals_count = Env.get_locals_count env' - List.length args - 1 in
  let env = env' |> Env.exit_function env in
  let t =
    Wt.(
      FuncT
        ( RefT (ref_type_of array_type_idx)
          :: List.init (List.length args) (fun _ -> any_type),
          [ any_type ] ))
  in
  add t locals_count code (Env.get_value_locs env') (Env.get_call_map env') env

let add_runtime env =
  let block_type_idx, env =
    env
    |> Env.upsert_type
         Wt.(
           RecT
             [ SubT (Final, [], DefFuncT (FuncT ([ any_type ], [ any_type ]))) ])
  in
  let array_type_idx, env = env |> Env.upsert_type array_type in
  let sexp_type_idx, env = env |> Env.upsert_type (sexp_type array_type_idx) in
  let _, env =
    env
    |> Env.add_function (Some "length")
         (Wt.FuncT
            ([ RefT (ref_type_of array_type_idx); any_type ], [ any_type ]))
         0
         [
           phrase @@ Wa.LocalGet (get_idx 1);
           phrase
           @@ Wa.Block
                ( VarBlockType (get_idx block_type_idx),
                  [
                    phrase
                    @@ Wa.BrOnCastFail
                         (get_idx 0, any_ref_type, ref_type_of sexp_type_idx);
                    phrase
                    @@ Wa.StructGet (get_idx sexp_type_idx, get_idx 1, None);
                    phrase @@ Wa.ArrayLen;
                    phrase @@ Wa.RefI31;
                    phrase @@ Wa.Return;
                  ] );
           phrase @@ Wa.RefCast (NoNull, ArrayHT);
           phrase @@ Wa.ArrayLen;
           phrase @@ Wa.RefI31;
         ]
         Mi.empty Si.empty
  in
  env

let compile ast =
  let env = Env.empty in
  let array_type_idx, env = env |> Env.upsert_type array_type in
  let env = env |> Env.enter_scope in
  let env =
    env
    |> Env.add_function_import "write"
         (FuncT ([ RefT (ref_type_of array_type_idx); any_type ], [ any_type ]))
  in
  let env =
    env
    |> Env.add_function_import "read"
         (FuncT ([ RefT (ref_type_of array_type_idx) ], [ any_type ]))
  in
  let env = add_runtime env in

  match ast with
  | Expr.Scope (decls, instr) ->
      let env = env |> Env.enter_function in
      let env, code = compile_scope decls (Expr.Ignore instr) true env in
      let func_idx, env =
        env
        |> Env.add_function (Some "main")
             (FuncT ([], []))
             (Env.get_locals_count env) code (Env.get_value_locs env)
             (Env.get_call_map env)
      in
      let env = env |> Env.export_function "main" func_idx in
      let env = env |> Env.expand_closures in
      let env = env |> Env.second_pass in
      env |> Env.assemble_module
  | _ -> report_error "expected root scope"

let genast _ ((_, _), p) = compile p

let build cmd prog =
  let module' = genast cmd prog in
  let oc = open_out (cmd#basename ^ ".wast") in
  Wasm.Print.module_ oc 80 module';
  close_out oc;
  Wasm.Valid.check_module module';
  cmd#dump_file "wasm" (Wasm.Encode.encode module')
