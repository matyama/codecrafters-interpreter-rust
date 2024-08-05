TESTS := test-tokenize test-parse test-evaluate
TESTS_DIR := tests

.PHONY: test
test: $(TESTS)

.PHONY: $(TESTS)
$(TESTS):
	./tests/$@.sh
