#!/usr/bin/env bash

TARGET_DIR="${TARGET_DIR:-/tmp/codecrafters-interpreter-target}"
mkdir -p "${TARGET_DIR}"

INPUT="${TARGET_DIR}/test.lox"
OUTPUT="${TARGET_DIR}/output.log"
EXPECTED="${TARGET_DIR}/expected.log"

function run_test {
  echo "Stage (Evaluating Expressions - $1) - Test case ${2}"
  local exit_code=$3

  local input=$4
  local expected=$5

  echo "$input" >$INPUT
  echo "$expected" >$EXPECTED

  ./your_program.sh evaluate "${INPUT}" &>"${OUTPUT}"

  if [[ $? != $exit_code ]]; then
    echo "Test failed"
  fi

  if ! diff "${OUTPUT}" "${EXPECTED}"; then
    echo "Test failed"
  fi

  echo "Test passed"
}

run_test "Literals: Booleans & Nil" 1 0 "true" "true"
run_test "Literals: Booleans & Nil" 2 0 "false" "false"
run_test "Literals: Booleans & Nil" 3 0 "nil" "nil"

run_test "Literals: Strings & Numbers" 1 0 '59' '59'
run_test "Literals: Strings & Numbers" 2 0 '15.89' '15.89'
run_test "Literals: Strings & Numbers" 3 0 '"quz world"' 'quz world'
run_test "Literals: Strings & Numbers" 4 0 '"56"' '56'

run_test "Parentheses" 1 0 '(true)' 'true'
run_test "Parentheses" 2 0 '(36)' '36'
run_test "Parentheses" 3 0 '("hello foo")' 'hello foo'
run_test "Parentheses" 4 0 '((false))' 'false'

run_test "Unary Operators: Negation & Not" 1 0 '-50' '-50'
run_test "Unary Operators: Negation & Not" 2 0 '!true' 'false'
run_test "Unary Operators: Negation & Not" 3 0 '!nil' 'true'
run_test "Unary Operators: Negation & Not" 4 0 '(!!75)' 'true'

run_test "Arithmetic Operators (1/2)" 1 0 '34 * 16' '544'
run_test "Arithmetic Operators (1/2)" 2 0 '89 / 5' '17.8'
run_test "Arithmetic Operators (1/2)" 3 0 '7 * 2 / 7 / 1' '2'
run_test "Arithmetic Operators (1/2)" 4 0 '(18 * 2 / (3 * 6))' '2'

run_test "Arithmetic Operators (2/2)" 1 0 '99 - 85' '14'
run_test "Arithmetic Operators (2/2)" 2 0 '37 + 53 - 55' '35'
run_test "Arithmetic Operators (2/2)" 3 0 '73 + 88 - (-(77 - 41))' '197'
run_test "Arithmetic Operators (2/2)" 4 0 '-(-73 + 13) * (82 * 38) / (1 + 4)' '37392'

run_test "String Concatenation" 1 0 '"foo" + "quz"' 'fooquz'
run_test "String Concatenation" 2 0 '"bar" + "75"' 'bar75'
run_test "String Concatenation" 3 0 '"hello" + "baz" + "foo"' 'hellobazfoo'
run_test "String Concatenation" 4 0 '("quz" + "quz") + ("hello" + "baz")' 'quzquzhellobaz'

run_test "Relational Operators" 1 0 '11 > -48' 'true'
run_test "Relational Operators" 2 0 '11 <= 96' 'true'
run_test "Relational Operators" 3 0 '48 >= 48' 'true'
run_test "Relational Operators" 4 0 '(76 - 80) >= -(22 / 11 + 13)' 'true'

run_test "Equality Operators" 1 0 '"hello" != "foo"' 'true'
run_test "Equality Operators" 2 0 '"hello" == "hello"' 'true'
run_test "Equality Operators" 3 0 '31 == "31"' 'false'
run_test "Equality Operators" 4 0 '121 == (88 + 33)' 'true'

read -r -d '' expected <<EOM
Operand must be a number.
[line 1]
EOM

run_test "Runtime Errors: Unary Operators" 1 70 '-"quz"' "$expected"
run_test "Runtime Errors: Unary Operators" 2 70 '-true' "$expected"
run_test "Runtime Errors: Unary Operators" 3 70 '-false' "$expected"
run_test "Runtime Errors: Unary Operators" 4 70 '-("foo" + "hello")' "$expected"

read -r -d '' expected <<EOM
Operands must be numbers.
[line 1]
EOM

read -r -d '' expected2 <<EOM
Operands must be two numbers or two strings.
[line 1]
EOM

run_test "Runtime Errors: Binary Operators (1/2)" 1 70 '81 * "hello"' "$expected"
run_test "Runtime Errors: Binary Operators (1/2)" 2 70 '"bar" / 73' "$expected"
run_test "Runtime Errors: Binary Operators (1/2)" 3 70 'true / false' "$expected"
run_test "Runtime Errors: Binary Operators (1/2)" 4 70 '("quz" + "world") * ("world" + "bar")' "$expected"

run_test "Runtime Errors: Binary Operators (2/2)" 1 70 '"world" + false' "$expected2"
run_test "Runtime Errors: Binary Operators (2/2)" 2 70 '39 + "bar" + 32' "$expected2"
run_test "Runtime Errors: Binary Operators (2/2)" 3 70 '80 - true' "$expected"
run_test "Runtime Errors: Binary Operators (2/2)" 4 70 'false - ("quz" + "baz")' "$expected"

run_test "Runtime Errors: Relational Operators" 1 70 '"world" < false' "$expected"
run_test "Runtime Errors: Relational Operators" 2 70 'false <= (11 + 36)' "$expected"
run_test "Runtime Errors: Relational Operators" 3 70 '32 > ("foo" + "baz")' "$expected"
run_test "Runtime Errors: Relational Operators" 4 70 'true >= false' "$expected"
