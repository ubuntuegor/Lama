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

const filePath = argv[2]
const wasmFile = fs.readFileSync(filePath)
WebAssembly.instantiate(wasmFile, {
    "lama": {
        "write": num => {
            console.log(num)
            return 0
        },
        "read": () => {
            fs.writeSync(1, "> ")
            return readNum()
        }
    }
}).then(wasmModule => {
    const instance = wasmModule.instance
    const main = instance.exports.main
    main()
})
