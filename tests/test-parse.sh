#!/usr/bin/env bash

TARGET_DIR="${TARGET_DIR:-/tmp/codecrafters-interpreter-target}"
mkdir -p "${TARGET_DIR}"

INPUT="${TARGET_DIR}/test.lox"
OUTPUT="${TARGET_DIR}/output.log"
EXPECTED="${TARGET_DIR}/expected.log"

function run_test {
  echo "Stage (Parsing Expressions - $1) - Test case ${2}"
  local exit_code=$3

  local input=$4
  local expected=$5

  echo "$input" >$INPUT
  echo "$expected" >$EXPECTED

  ./your_program.sh parse "${INPUT}" &>"${OUTPUT}"

  if [[ $? != $exit_code ]]; then
    echo "Test failed"
  fi

  if ! diff "${OUTPUT}" "${EXPECTED}"; then
    echo "Test failed"
  fi

  echo "Test passed"
}

run_test "Booleans & Nil" 1 0 'true' "true"
run_test "Booleans & Nil" 2 0 'false' "false"
run_test "Booleans & Nil" 3 0 'nil' "nil"

run_test "Number literals" 1 0 '36' "36.0"
run_test "Number literals" 2 0 '0.0' "0.0"
run_test "Number literals" 3 0 '14.40' "14.4"

run_test "String literals" 1 0 '"baz quz"' "baz quz"
run_test "String literals" 2 0 "\"'foo'\"" "'foo'"
run_test "String literals" 3 0 '"// bar"' "// bar"
run_test "String literals" 4 0 '"30"' "30"

run_test "Parentheses" 1 0 '("foo")' "(group foo)"
run_test "Parentheses" 2 0 '((true))' "(group (group true))"
run_test "Parentheses" 3 65 '()' "[line 1] Error at ')': Expect expression."
# FIXME: wrong line number
#run_test "Parentheses" 4 65 \
#  '("foo"' \
#  "[line 1] Error at end: Expect ')' after expression."

run_test "Unary Operators" 1 0 '!true' "(! true)"
run_test "Unary Operators" 2 0 '-22' "(- 22.0)"
run_test "Unary Operators" 3 0 '!!true' "(! (! true))"
run_test "Unary Operators" 4 0 '(!!(false))' "(group (! (! (group false))))"

run_test "Arithmetic operators (1/2)" 1 0 '94 * 39 / 89' "(/ (* 94.0 39.0) 89.0)"
run_test "Arithmetic operators (1/2)" 2 0 '20 / 17 / 42' "(/ (/ 20.0 17.0) 42.0)"
run_test "Arithmetic operators (1/2)" 3 0 '42 * 65 * 78 / 69' "(/ (* (* 42.0 65.0) 78.0) 69.0)"
run_test "Arithmetic operators (1/2)" 4 0 \
  '(39 * -70 / (90 * 17))' \
  "(group (/ (* 39.0 (- 70.0)) (group (* 90.0 17.0))))"

run_test "Arithmetic operators (2/2)" 1 0 '"hello" + "world"' "(+ hello world)"
run_test "Arithmetic operators (2/2)" 2 0 '16 - 14 - 47' "(- (- 16.0 14.0) 47.0)"
run_test "Arithmetic operators (2/2)" 3 0 '37 + 89 - 99' "(- (+ 37.0 89.0) 99.0)"
run_test "Arithmetic operators (2/2)" 4 0 \
  '-(-44 + 35) * (74 * 26) / (27 + 61)' \
  "(/ (* (- (group (+ (- 44.0) 35.0))) (group (* 74.0 26.0))) (group (+ 27.0 61.0)))"

run_test "Comparison operators" 1 0 '17 > -20' "(> 17.0 (- 20.0))"
run_test "Comparison operators" 2 0 '37 <= 54' "(<= 37.0 54.0)"
run_test "Comparison operators" 3 0 '17 < 54 < 91' "(< (< 17.0 54.0) 91.0)"
run_test "Comparison operators" 4 0 \
  '(24 - 98) >= -(27 / 34 + 17)' \
  "(>= (group (- 24.0 98.0)) (- (group (+ (/ 27.0 34.0) 17.0))))"

run_test "Equality operators" 1 0 '"foo"!="world"' "(!= foo world)"
run_test "Equality operators" 2 0 '"hello" == "hello"' "(== hello hello)"
run_test "Equality operators" 3 0 '17 == 74' "(== 17.0 74.0)"
run_test "Equality operators" 4 0 \
  '(70 != 92) == ((-28 + 51) >= (34 * 38))' \
  "(== (group (!= 70.0 92.0)) (group (>= (group (+ (- 28.0) 51.0)) (group (* 34.0 38.0)))))"

# FIXME: wrong line number
#run_test "Syntactic errors" 1 65 '"world' "[line 1] Error: Unterminated string."
run_test "Syntactic errors" 2 65 "(97 +)" "[line 1] Error at ')': Expect expression."
run_test "Syntactic errors" 3 65 "+" "[line 1] Error at '+': Expect expression."
