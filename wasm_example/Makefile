LAMAC=../src/lamac

.PHONY: hello.html hello.wasm hello hello.sm run

hello.html:
	$(LAMAC) -dp hello.lama
	code hello.html

hello.wasm:
	LAMA=../wasm_runtime $(LAMAC) -wasm hello.lama -I ../stdlib

hello:
	$(LAMAC) hello.lama

hello.sm:
	$(LAMAC) -ds hello.lama

ast: hello.html
wasm: hello.wasm
compile: hello
sm: hello.sm

run: hello.wasm
	node ../wasm_runtime/run.js hello.wasm
