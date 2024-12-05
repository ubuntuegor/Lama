const fs = require("fs")
const { argv } = require("process")

const buffer = []

function readNum() {
    if (buffer.length == 0) {
        const buf = Buffer.alloc(1024)
        const read = fs.readSync(0, buf)
        buf.subarray(0, read).toString().trim().split("\n").forEach(value => {
            buffer.push(parseInt(value))
        })
    }

    return buffer.shift()
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
