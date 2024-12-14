(module
  (type $string_type (array (mut i8)))
  (type $array_type (array (mut (ref any))))
  (type $closure_type (struct (field (ref func)) (field (ref $array_type))))
  (type $sexp_type (struct (field i32) (field (ref $array_type))))
  ;; (import "Std" "write" (func $write (param (ref any)) (param (ref any)) (result (ref any))))

  (memory (export "_memory") 1)
  (table $tbl (export "_table") 0 (ref any) i32.const 0 ref.i31)

  ;; helpers
  (func (export "elem") (param $arr (ref any)) (param $index i32) (result (ref any))
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
  (func (export "strcmp") (param $str1 (ref $string_type)) (param $str2 (ref $string_type)) (result i32)
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

  ;; stdlib
  (func (export "length") (param (ref $array_type)) (param $arg (ref any)) (result (ref any))
    local.get $arg
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $sexp_type)
      struct.get $sexp_type 1
      array.len
      ref.i31
      return
    )
    (block (param (ref any)) (result (ref any))
      br_on_cast_fail 0 (ref any) (ref $closure_type)
      struct.get $closure_type 1
      array.len
      ref.i31
      return
    )
    ref.cast (ref array)
    array.len
    ref.i31
  )
  (func (export "makeArray") (param (ref $array_type)) (param $len (ref any)) (result (ref any))
    (ref.i31 (i32.const 0))
    (i31.get_s (ref.cast (ref i31) (local.get $len)))
    array.new $array_type
  )
)