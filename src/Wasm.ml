open SM
open Language

(* A set of strings *)
module S = Set.Make (String)

let compile_instr globals instr =
  match instr with
  | CONST n -> (globals, [ Printf.sprintf "i32.const %d" n ])
  | BINOP op -> (globals, (
    match op with
      | "+" -> [ "i32.add" ]
      | "-" -> [ "i32.sub" ]
      | "*" -> [ "i32.mul" ]
      | "/" -> [ "i32.div_s" ]
      | "%" -> [ "i32.rem_s" ]
      | "==" -> [ "i32.eq" ]
      | "!=" -> [ "i32.ne" ]
      | "<=" -> [ "i32.le_s" ]
      | "<" -> [ "i32.lt_s" ]
      | ">=" -> [ "i32.ge_s" ]
      | ">" -> [ "i32.gt_s" ]
      | "&&" -> [
        "(if (param i32) (result i32)";
        "(then";
        "i32.const 0";
        "i32.ne";
        ")";
        "(else";
        "drop";
        "i32.const 0";
        ")";
        ")"
      ]
      | "!!" -> [
        "i32.or";
        "i32.const 0";
        "i32.ne"
      ]
      | _ -> Printf.printf "unsupported binop %s\n" op ; []
    ))
  | CALL (f, _, _) -> (globals, [ Printf.sprintf "call $%s" f ])
  | LD x -> (
    match x with
    | Value.Global name -> (S.add ("$global_" ^ name) globals, ["global.get $global_" ^ name])
    | x -> Printf.printf "unsupported memory %s\n" (GT.show Value.designation x) ; (globals, [])
    )
  | ST x -> (
    match x with
    | Value.Global name -> (S.add ("$global_" ^ name) globals, ["global.set $global_" ^ name])
    | x -> Printf.printf "unsupported memory %s\n" (GT.show Value.designation x) ; (globals, [])
    )
  | i -> Printf.printf "unsupported instr %s\n" (GT.show insn i) ; (globals, [])

let rec compile globals instrs =
  match instrs with
    | [] -> (globals, [])
    | instr :: instrs' -> (
      let (globals', code) = compile_instr globals instr in
      let (globals'', code') = compile globals' instrs' in
      (globals'', code @ code')
    )

let genwat cmd prog =
  let sm = SM.compile cmd prog in
  let globals = S.empty in
  let (globals', code) = compile globals sm in
  let wat = Buffer.create 1024 in
  List.iter (fun instr -> Buffer.add_string wat (instr ^ "\n"))
  (
    [
      "(module";
      "(import \"lama\" \"Lwrite\" (func $Lwrite (param i32)))"
    ]
    @ List.map
      (fun name -> Printf.sprintf "(global %s (mut i32) (i32.const 0))" name)
      (S.elements globals')
    @
    [
      "(func (export \"main\")"
    ]
    @ code @ [
      "))"
    ]
  );
  Buffer.contents wat

let build cmd prog =
  cmd#dump_file "wat" (genwat cmd prog)
