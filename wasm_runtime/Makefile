WASM = ../_build/default/wasm_runtime/wasm.exe

Std.wasm: Std.wat $(WASM)
	$(WASM) -d Std.wat -o Std.wasm

$(WASM): dune
	dune build wasm.exe

clean:
	rm Std.wasm
