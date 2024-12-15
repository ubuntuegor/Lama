SHELL := /bin/bash

FILES=$(wildcard *.lama)
ALL=$(sort $(FILES:.lama=.o))
LAMAC=../src/lamac -g

all: $(ALL) wasm

Fun.o: Ref.o

Data.o: Ref.o Collection.o

Collection.o: List.o Ref.o

Array.o: List.o

Ostap.o: List.o Collection.o Ref.o Fun.o Matcher.o

Buffer.o: List.o

STM.o: List.o Fun.o

%.o: %.lama
	LAMA=../runtime $(LAMAC) -I . -c $<

%.wasm: %.lama
	LAMA=../wasm_runtime $(LAMAC) -I . -wasm $<

wasm: Lazy.wasm Ref.wasm Fun.wasm List.wasm Array.wasm Buffer.wasm Collection.wasm Data.wasm

clean:
	rm -Rf *.s *.o *.i *~ *.wasm *.wat
	pushd regression && make clean && popd

