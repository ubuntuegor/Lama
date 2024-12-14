const fs = require("fs")
const { argv } = require("process")
const printf = require("./printf")

const readBuffer = []

function readNum() {
  if (readBuffer.length == 0) {
    const buf = Buffer.alloc(1024)
    const read = fs.readSync(0, buf)
    buf.subarray(0, read).toString().trim().split("\n").forEach(value => {
      readBuffer.push(parseInt(value))
    })
  }

  return readBuffer.shift()
}

function internalizeString(str) {
  const memory = runtime.Std._memory
  const reqPages = Math.floor(str.length / 65536) + 1
  const gotPages = Math.floor(memory.buffer.byteLength / 65536)
  memory.grow(reqPages - gotPages)
  const encoder = new TextEncoder()
  encoder.encodeInto(str, new Uint8Array(memory.buffer))
  return runtime.Std.string_from_memory(str.length)
}

function externalizeString(pointer) {
  const len = runtime.Std.string_to_memory(pointer)
  const memory = runtime.Std._memory
  const view = new DataView(memory.buffer, 0, len)
  const decoder = new TextDecoder()
  return decoder.decode(view)
}

function externalizeClosure(pointer) {
  const len = runtime.Std.closure_to_table(pointer)
  const table = runtime.Std._table
  const result = []

  for (let i = 0; i < len; i++) {
    result.push(table.get(i))
  }

  return result
}

function externalizeArray(pointer) {
  const len = runtime.Std.array_to_table(pointer)
  const table = runtime.Std._table
  const result = []

  for (let i = 0; i < len; i++) {
    result.push(table.get(i))
  }

  return result
}

function de_hash(hash) {
  const chars = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'"
  const result = []

  while (hash != 0) {
    result.unshift(chars[hash & 0b00111111])
    hash = hash >> 6
  }

  return result.join("")
}

function externalizeSexp(pointer) {
  const tag = de_hash(runtime.Std.sexp_to_tag(pointer))
  const len = runtime.Std.sexp_to_table(pointer)
  const table = runtime.Std._table
  const result = []

  for (let i = 0; i < len; i++) {
    result.push(table.get(i))
  }

  return [tag, result]
}

function basePrintf(args) {
  const formatString = externalizeString(args.shift())
  for (let i = 0; i < args.length; i++) {
    if (runtime.Std.is_string(args[i])) {
      args[i] = externalizeString(args[i])
    }
  }
  return printf(formatString, ...args)
}

const runtime = {
  "Std": {
    "write": (_, num) => {
      console.log(num)
      return 0
    },
    "read": (_) => {
      fs.writeSync(1, "> ")
      return readNum()
    },
    "printf": (_, args) => {
      args = externalizeArray(args)
      process.stdout.write(basePrintf(args))
      return 0
    },
    "sprintf": (_, args) => {
      args = externalizeArray(args)
      return internalizeString(basePrintf(args))
    },
    "failure": (_, args) => {
      args = externalizeArray(args)
      throw new Error(basePrintf(args))
    },
    "string": (_, arg) => {
      function inner(arg) {
        if (typeof arg == "number") {
          return arg.toString()
        }
        if (runtime.Std.is_string(arg)) {
          const str = externalizeString(arg)
          return `"${str}"`
        }
        if (runtime.Std.is_closure(arg)) {
          const vals = externalizeClosure(arg)
          const strs = vals.map(v => inner(v))
          return `<closure ${strs.join(", ")}>`
        }
        if (runtime.Std.is_array(arg)) {
          const vals = externalizeArray(arg)
          const strs = vals.map(v => inner(v))
          return `[${strs.join(", ")}]`
        }
        if (runtime.Std.is_sexp(arg)) {
          const [tag, vals] = externalizeSexp(arg)
          if (tag == "cons") {
            const elems = [vals[0]]
            let next = vals[1]
            while (runtime.Std.is_sexp(next)) {
              const [_, nextVals] = externalizeSexp(next)
              elems.push(nextVals[0])
              next = nextVals[1]
            }
            const strs = elems.map(v => inner(v))
            return `{${strs.join(", ")}}`
          } else {
            const strs = vals.map(v => inner(v))
            return tag + (strs.length > 0 ? ` (${strs.join(", ")})` : "")
          }
        }
        return "unknown type"
      }

      return internalizeString(inner(arg))
    }
  }
}

async function loadLib(name) {
  const module = await WebAssembly.instantiate(fs.readFileSync(__dirname + `/../stdlib/${name}.wasm`), runtime)
  module.instance.exports.main()
  runtime[name] = module.instance.exports
}

async function main() {
  const filePath = argv[2]

  const stdModule = await WebAssembly.instantiate(fs.readFileSync(__dirname + "/Std.wasm"), runtime)
  runtime.Std = { ...runtime.Std, ...stdModule.instance.exports }

  await loadLib("Lazy")
  await loadLib("Ref")
  await loadLib("Fun")

  const mainModule = await WebAssembly.instantiate(fs.readFileSync(filePath), runtime)
  mainModule.instance.exports.main()
}

main()
