WASM = ../_build/default/wasm_runtime/wasm_tool.exe

Std.wasm: Std.wat $(WASM)
	$(WASM) -d Std.wat -o Std.wasm

$(WASM): dune
	dune build wasm_tool.exe

clean:
	rm Std.wasm
