(module
  (type $string_type (array (mut i8)))
  (type $array_type (array (mut (ref any))))
  (type $closure_type (struct (field (ref func)) (field (ref $array_type))))
  (type $sexp_type (struct (field i32) (field (ref $array_type))))
  ;; (import "Std" "write" (func $write (param (ref any)) (param (ref any)) (result (ref any))))

  (memory (export "_memory") 1)
  (table $tbl (export "_table") 0 (ref any) i32.const 0 ref.i31)

  ;; helpers
  (func $elem (export "elem") (param $arr (ref any)) (param $index i32) (result (ref any))
    local.get $arr
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $sexp_type)
      struct.get $sexp_type 1
      local.get $index
      array.get $array_type
      return
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $closure_type)
      struct.get $closure_type 1
      local.get $index
      array.get $array_type
      return
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $string_type)
      local.get $index
      array.get_s $string_type
      ref.i31
      return
    )
    ref.cast (ref $array_type)
    local.get $index
    array.get $array_type
  )
  (func (export "assign") (param $arr (ref any)) (param $index i32) (param $value (ref any)) (result (ref any))
    local.get $arr
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $sexp_type)
      struct.get $sexp_type 1
      local.get $index
      local.get $value
      array.set $array_type
      local.get $value
      return
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $closure_type)
      struct.get $closure_type 1
      local.get $index
      local.get $value
      array.set $array_type
      local.get $value
      return
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $string_type)
      local.get $index
      local.get $value
      ref.cast (ref i31)
      i31.get_s
      array.set $string_type
      local.get $value
      return
    )
    ref.cast (ref $array_type)
    local.get $index
    local.get $value
    array.set $array_type
    local.get $value
  )
  (func $strcmp (export "strcmp") (param $str1 (ref $string_type)) (param $str2 (ref $string_type)) (result i32)
    (local $tmp i32) (local $i i32)
    (i32.sub (array.len (local.get $str1)) (array.len (local.get $str2)))
    local.tee $tmp
    (if (then
      local.get $tmp
      return
    ))

    (block $exit
      (loop $loop
        (i32.eqz (i32.lt_u (local.get $i) (array.len (local.get $str1))))
        br_if $exit

        (i32.sub
          (array.get_u $string_type (local.get $str1) (local.get $i))
          (array.get_u $string_type (local.get $str2) (local.get $i))
        )
        local.tee $tmp
        (if (then
          local.get $tmp
          return
        ))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        br $loop
      )
    )
    i32.const 0
  )
  (func (export "is_string") (param $p (ref any)) (result i32)
    local.get $p
    ref.test (ref $string_type)
  )
  (func (export "is_closure") (param $p (ref any)) (result i32)
    local.get $p
    ref.test (ref $closure_type)
  )
  (func (export "is_array") (param $p (ref any)) (result i32)
    local.get $p
    ref.test (ref $array_type)
  )
  (func (export "is_sexp") (param $p (ref any)) (result i32)
    local.get $p
    ref.test (ref $sexp_type)
  )
  (func $array_to_table (export "array_to_table") (param $arr (ref $array_type)) (result i32)
    (local $i i32)
    (ref.i31 (i32.const 0))
    (array.len (local.get $arr))
    (i32.sub (table.size $tbl))
    (drop (table.grow $tbl))

    (block $exit
      (loop $loop
        (i32.eqz (i32.lt_u (local.get $i) (array.len (local.get $arr))))
        br_if $exit

        local.get $i
        (array.get $array_type (local.get $arr) (local.get $i))
        table.set $tbl

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        br $loop
      )
    )

    (array.len (local.get $arr))
  )
  (func (export "closure_to_table") (param $clo (ref $closure_type)) (result i32)
    (struct.get $closure_type 1 (local.get $clo))
    call $array_to_table
  )
  (func (export "sexp_to_table") (param $sexp (ref $sexp_type)) (result i32)
    (struct.get $sexp_type 1 (local.get $sexp))
    call $array_to_table
  )
  (func (export "sexp_to_tag") (param $sexp (ref $sexp_type)) (result i32)
    (struct.get $sexp_type 0 (local.get $sexp))
  )
  (func (export "string_to_memory") (param $str (ref $string_type)) (result i32)
    (local $i i32)
    (array.len (local.get $str))
    (i32.div_u (i32.const 65536))
    (i32.add (i32.const 1))
    (i32.sub (memory.size))
    (drop (memory.grow))

    (block $exit
      (loop $loop
        (i32.eqz (i32.lt_u (local.get $i) (array.len (local.get $str))))
        br_if $exit

        local.get $i
        (array.get_u $string_type (local.get $str) (local.get $i))
        i32.store8

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        br $loop
      )
    )

    (array.len (local.get $str))
  )
  (func (export "string_from_memory") (param $len i32) (result (ref $string_type))
    (local $arr (ref $string_type)) (local $i i32)
    (array.new_default $string_type (local.get $len))
    local.set $arr

    (block $exit
      (loop $loop
        (i32.eqz (i32.lt_u (local.get $i) (local.get $len)))
        br_if $exit

        local.get $arr
        local.get $i
        (i32.load8_u (local.get $i))
        array.set $string_type

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        br $loop
      )
    )

    local.get $arr
  )
  (func $clone_array (param $arr (ref $array_type)) (result (ref $array_type))
    (local $new_arr (ref $array_type))
    (ref.i31 (i32.const 0))
    (array.len (local.get $arr))
    array.new $array_type
    local.set $new_arr

    (array.copy $array_type $array_type
      (local.get $new_arr)
      (i32.const 0)
      (local.get $arr)
      (i32.const 0)
      (array.len (local.get $arr))
    )

    (return (local.get $new_arr))
  )
  (func $length (param $arg (ref any)) (result i32)
    local.get $arg
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $sexp_type)
      struct.get $sexp_type 1
      (return (array.len))
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $closure_type)
      struct.get $closure_type 1
      (return (array.len))
    )
    ref.cast (ref array)
    array.len
  )
  (func $kindOf (param $p (ref any)) (result i32)
    local.get $p
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $string_type)
      (return (i32.const 1))
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $array_type)
      (return (i32.const 3))
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $sexp_type)
      (return (i32.const 5))
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $closure_type)
      (return (i32.const 7))
    )
    ref.cast (ref i31)
    (return (i32.const 9))
  )
  (func $hash_append (param $x i32) (param $acc i32) (result i32)
    (i32.add (local.get $acc) (local.get $x))
    (i32.shl (i32.const 16))
    (i32.add (local.get $acc) (local.get $x))
    (i32.shr_u (i32.const 16))
    i32.or
  )
  (func $hash_string (param $str (ref $string_type)) (param $acc i32) (result i32)
    (local $i i32)
    (block $exit
      (loop $loop
        (i32.eqz (i32.lt_u (local.get $i) (array.len (local.get $str))))
        br_if $exit

        (array.get_s $string_type (local.get $str) (local.get $i))
        local.get $acc
        (local.set $acc (call $hash_append))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        br $loop
      )
    )

    local.get $acc
  )
  (func $inner_hash (param $depth i32) (param $acc i32) (param $p (ref any)) (result i32)
    (local $arr (ref $array_type)) (local $i i32)
    (if (i32.gt_s (local.get $depth) (i32.const 3))
    (then
      (return (local.get $acc))
    ))

    (drop (block (result (ref any))
      (br_on_cast_fail 0 (ref any) (ref i31) (local.get $p))
      i31.get_s
      local.get $acc
      (return (call $hash_append))
    ))

    (local.set $acc (call $hash_append (call $kindOf (local.get $p)) (local.get $acc)))
    (local.set $acc (call $hash_append (call $length (local.get $p)) (local.get $acc)))

    (block $outer (result (ref $array_type))
      local.get $p
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $string_type)
        local.get $acc
        (return (call $hash_string))
      )
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $array_type)
        br $outer
      )
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $sexp_type)
        struct.get $sexp_type 0
        local.get $acc
        (local.set $acc (call $hash_append))

        (ref.cast (ref $sexp_type) (local.get $p))
        struct.get $sexp_type 1
        br $outer
      )
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $closure_type)
        struct.get $closure_type 1
        br $outer
      )
      unreachable
    )

    local.set $arr

    (block $exit
      (loop $loop
        (i32.eqz (i32.lt_u (local.get $i) (array.len (local.get $arr))))
        br_if $exit

        (i32.add (local.get $depth) (i32.const 1))
        local.get $acc
        (array.get $array_type (local.get $arr) (local.get $i))
        call $inner_hash
        local.set $acc

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        br $loop
      )
    )

    local.get $acc
  )

  ;; stdlib
  (func (export "length") (param (ref $array_type)) (param $arg (ref any)) (result (ref any))
    (ref.i31 (call $length (local.get $arg)))
  )
  (func (export "makeArray") (param (ref $array_type)) (param $len (ref any)) (result (ref any))
    (ref.i31 (i32.const 0))
    (i31.get_s (ref.cast (ref i31) (local.get $len)))
    array.new $array_type
  )
  (func (export "makeString") (param (ref $array_type)) (param $len (ref any)) (result (ref any))
    i32.const 0
    (i31.get_s (ref.cast (ref i31) (local.get $len)))
    array.new $string_type
  )
  (func (export "kindOf") (param (ref $array_type)) (param $p (ref any)) (result (ref any))
    (return (ref.i31 (call $kindOf (local.get $p))))
  )
  (func $compare (export "compare") (param (ref $array_type)) (param $p (ref any)) (param $q (ref any)) (result (ref any))
    (local $tmp i32) (local $i i32) (local $pa (ref $array_type)) (local $qa (ref $array_type))
    (ref.cast (ref eq) (local.get $p))
    (ref.cast (ref eq) (local.get $q))
    (if (ref.eq) (then
      (return (ref.i31 (i32.const 0)))
    ))

    (block (result (ref any))
      (br_on_cast_fail 0 (ref any) (ref i31) (local.get $p))
      i31.get_s
      (block (param i32) (result (ref any))
        (br_on_cast_fail 0 (ref any) (ref i31) (local.get $q))
        i31.get_s
        (return (ref.i31 (i32.sub)))
      )
      (return (ref.i31 (i32.const -1)))
    )
    drop
    (block (result (ref any))
      (br_on_cast_fail 0 (ref any) (ref i31) (local.get $q))
      (return (ref.i31 (i32.const 1)))
    )
    drop

    (call $kindOf (local.get $p))
    (call $kindOf (local.get $q))
    i32.sub
    local.tee $tmp
    (if (then
      (return (ref.i31 (local.get $tmp)))
    ))

    (block $outer (result (ref $array_type) (ref $array_type))
      local.get $p
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $string_type)
        (ref.cast (ref $string_type) (local.get $q))
        (return (ref.i31 (call $strcmp)))
      )
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $array_type)
        (ref.cast (ref $array_type) (local.get $q))
        br $outer
      )
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $sexp_type)
        struct.get $sexp_type 0
        (ref.cast (ref $sexp_type) (local.get $q))
        struct.get $sexp_type 0
        i32.sub
        local.tee $tmp
        (if (then
          (return (ref.i31 (local.get $tmp)))
        ))

        (ref.cast (ref $sexp_type) (local.get $p))
        struct.get $sexp_type 1
        (ref.cast (ref $sexp_type) (local.get $q))
        struct.get $sexp_type 1
        br $outer
      )
      (block (param (ref any)) (result (ref any))
        br_on_cast_fail 0 (ref any) (ref $closure_type)
        struct.get $closure_type 1
        (ref.cast (ref $closure_type) (local.get $q))
        struct.get $closure_type 1
        br $outer
      )
      unreachable
    )

    local.set $qa
    local.set $pa

    (array.len (local.get $pa))
    (array.len (local.get $qa))
    i32.sub
    local.tee $tmp
    (if (then
      (return (ref.i31 (local.get $tmp)))
    ))

    (block $exit
      (loop $loop
        (i32.eqz (i32.lt_u (local.get $i) (array.len (local.get $pa))))
        br_if $exit

        (call $compare
          (array.new_fixed $array_type 0)
          (array.get $array_type (local.get $pa) (local.get $i))
          (array.get $array_type (local.get $qa) (local.get $i))
        )
        ref.cast (ref i31)
        i31.get_s
        local.tee $tmp
        (if (then
          (return (ref.i31 (local.get $tmp)))
        ))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        br $loop
      )
    )

    (ref.i31 (i32.const 0))
  )
  (func (export "clone") (param (ref $array_type)) (param $p (ref any)) (result (ref any))
    (local $new_len i32) (local $new_str (ref $string_type))
    local.get $p
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $string_type)
      drop
      i32.const 0
      (array.len (ref.cast (ref $string_type) (local.get $p)))
      local.tee $new_len
      array.new $string_type
      local.set $new_str

      (array.copy $string_type $string_type
        (local.get $new_str)
        (i32.const 0)
        (ref.cast (ref $string_type) (local.get $p))
        (i32.const 0)
        (local.get $new_len)
      )

      (return (local.get $new_str))
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $array_type)
      call $clone_array
      return
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $sexp_type)
      struct.get $sexp_type 0
      (struct.get $sexp_type 1 (ref.cast (ref $sexp_type) (local.get $p)))
      call $clone_array
      (return (struct.new $sexp_type))
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $closure_type)
      struct.get $closure_type 0
      (struct.get $closure_type 1 (ref.cast (ref $closure_type) (local.get $p)))
      call $clone_array
      (return (struct.new $closure_type))
    )
    ref.cast (ref i31)
  )
  (func $strcat (export "i__Infix_4343") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (local $res (ref $string_type))
    i32.const 0
    (array.len (ref.cast (ref $string_type) (local.get $a)))
    (array.len (ref.cast (ref $string_type) (local.get $b)))
    i32.add
    array.new $string_type
    local.set $res

    (array.copy $string_type $string_type
      (local.get $res)
      (i32.const 0)
      (ref.cast (ref $string_type) (local.get $a))
      (i32.const 0)
      (array.len (ref.cast (ref $string_type) (local.get $a)))
    )

    (array.copy $string_type $string_type
      (local.get $res)
      (array.len (ref.cast (ref $string_type) (local.get $a)))
      (ref.cast (ref $string_type) (local.get $b))
      (i32.const 0)
      (array.len (ref.cast (ref $string_type) (local.get $b)))
    )

    local.get $res
  )
  (func (export "fst") (export "hd") (param (ref $array_type)) (param $p (ref any)) (result (ref any))
    (call $elem (local.get $p) (i32.const 0))
  )
  (func (export "snd") (export "tl") (param (ref $array_type)) (param $p (ref any)) (result (ref any))
    (call $elem (local.get $p) (i32.const 1))
  )
  (func (export "compareTags") (param (ref $array_type)) (param $p (ref any)) (param $q (ref any)) (result (ref any))
    (ref.cast (ref $sexp_type) (local.get $p))
    struct.get $sexp_type 0
    (ref.cast (ref $sexp_type) (local.get $q))
    struct.get $sexp_type 0
    i32.sub
    ref.i31
  )
  (func (export "s__Infix_43") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.add))
  )
  (func (export "s__Infix_45") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.sub))
  )
  (func (export "s__Infix_42") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.mul))
  )
  (func (export "s__Infix_47") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.div_s))
  )
  (func (export "s__Infix_37") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.rem_s))
  )
  (func (export "s__Infix_6161") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (ref.cast (ref eq) (local.get $a))
    (ref.cast (ref eq) (local.get $b))
    (ref.i31 (ref.eq))
  )
  (func (export "s__Infix_3361") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.ne))
  )
  (func (export "s__Infix_6061") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.le_s))
  )
  (func (export "s__Infix_60") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.lt_s))
  )
  (func (export "s__Infix_6261") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.ge_s))
  )
  (func (export "s__Infix_62") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (ref.i31 (i32.gt_s))
  )
  (func (export "s__Infix_3838") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    (if (param i32) (result i32)
    (then
      i32.const 0
      i32.ne
    )
    (else
      drop
      i32.const 0
    ))
    ref.i31
  )
  (func (export "s__Infix_3333") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    (i31.get_s (ref.cast (ref i31) (local.get $a)))
    (i31.get_s (ref.cast (ref i31) (local.get $b)))
    i32.or
    (i32.ne (i32.const 0))
    ref.i31
  )
  (func (export "s__Infix_58") (param (ref $array_type)) (param $a (ref any)) (param $b (ref any)) (result (ref any))
    i32.const 848787 ;; hash of "cons"
    local.get $a
    local.get $b
    array.new_fixed $array_type 2
    struct.new $sexp_type
  )
  (func (export "substring") (param (ref $array_type)) (param $str (ref any)) (param $pos (ref any)) (param $len (ref any)) (result (ref any))
    (local $res (ref $string_type))
    i32.const 0
    (i31.get_s (ref.cast (ref i31) (local.get $len)))
    array.new $string_type
    local.set $res

    (array.copy $string_type $string_type
      (local.get $res)
      (i32.const 0)
      (ref.cast (ref $string_type) (local.get $str))
      (i31.get_s (ref.cast (ref i31) (local.get $pos)))
      (array.len (local.get $res))
    )

    local.get $res
  )
  (func (export "hash") (param (ref $array_type)) (param $p (ref any)) (result (ref any))
    (call $inner_hash (i32.const 0) (i32.const 0) (local.get $p))
    (i32.and (i32.const 0x3fffff))
    ref.i31
  )
)
