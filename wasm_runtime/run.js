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

function toWasmString(str) {
    const memory = runtime.Std._memory
    const reqPages = Math.floor(str.length / 65536) + 1
    const gotPages = Math.floor(memory.buffer.byteLength / 65536)
    memory.grow(reqPages - gotPages)
    const encoder = new TextEncoder()
    encoder.encodeInto(str, new Uint8Array(memory.buffer))
    return runtime.Std.from_memory(str.length)
}

function toJsString(pointer) {
    const len = runtime.Std.to_memory(pointer)
    const memory = runtime.Std._memory
    const view = new DataView(memory.buffer, 0, len)
    const decoder = new TextDecoder()
    return decoder.decode(view)
}

function basePrintf(...args) {
    const formatString = toJsString(args.shift())
    for (let i = 0; i < args.length; i++) {
        if (runtime.Std.is_string(args[i])) {
            args[i] = toJsString(args[i])
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
        "printf": (_, ...args) => {
            process.stdout.write(basePrintf(...args))
            return 0
        },
        "sprintf": (_, ...args) => {
            const result = basePrintf(...args)
            return toWasmString(result) 
        },
        "failure": (_, ...args) => {
            throw new Error(basePrintf(...args))
        }
    }
}

async function main() {
    const filePath = argv[2]

    const stdModule = await WebAssembly.instantiate(fs.readFileSync(__dirname + "/Std.wasm"), runtime)
    runtime.Std = { ...runtime.Std, ...stdModule.instance.exports }

    const refModule = await WebAssembly.instantiate(fs.readFileSync(__dirname + "/../stdlib/Ref.wasm"), runtime)
    refModule.instance.exports.main()
    runtime.Ref = refModule.instance.exports

    const mainModule = await WebAssembly.instantiate(fs.readFileSync(filePath), runtime)

    mainModule.instance.exports.main()
}

main()
