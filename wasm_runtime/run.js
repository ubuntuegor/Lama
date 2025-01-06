import { argv } from "process"
import { LamaRuntime } from "./lib.js"
import { fileURLToPath } from "url"
import { dirname } from "path"

const __filename = fileURLToPath(import.meta.url)
const __dirname = dirname(__filename)

async function main() {
  const filePath = argv[2]

  const runtime = new LamaRuntime(__dirname, __dirname + "/../stdlib")
  await runtime.initialize()

  await runtime.runModule("main", filePath)
}

main()
