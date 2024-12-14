TESTS=$(sort $(filter-out test30, $(basename $(wildcard test*.lama))))

LAMAC=../../src/lamac

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "stdlib/regression/$@"
	@LAMA=../../runtime $(LAMAC) -I .. -ds -dp $< && ./$@ > $@.log && diff $@.log orig/$@.log
	@LAMA=../../wasm_runtime $(LAMAC) -I .. -wasm $< && node ../../wasm_runtime/run.js $@.wasm > $@.log && diff $@.log orig/$@.log

clean:
	$(RM) test*.log *.s *~ $(TESTS) *.i *.wat *.wasm
