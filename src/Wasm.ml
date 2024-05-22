open SM

let compile_instr instr = match instr with
  | CONST n -> [ Printf.sprintf "i32.const %d" n ]
  | BINOP op -> (
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
    )
  | CALL (f, _, _) -> [ Printf.sprintf "call $%s" f ]
  | i -> Printf.printf "unsupported instr %s\n" (GT.show insn i) ; []

let rec compile instrs =
  match instrs with
    | [] -> []
    | instr :: instrs' -> (
      let code = compile_instr instr in
      let code' = compile instrs' in
      code @ code'
    )

let genwat cmd prog =
  let sm = SM.compile cmd prog in
  let code = compile sm in
  let wat = Buffer.create 1024 in
  List.iter (fun instr -> Buffer.add_string wat (instr ^ "\n"))
  (
    [
      "(module";
      "(import \"lama\" \"Lwrite\" (func $Lwrite (param i32)))";
      "(func (export \"main\")"
    ]
    @ code @ [
      "))"
    ]
  );
  Buffer.contents wat

let build cmd prog =
  cmd#dump_file "wat" (genwat cmd prog)
