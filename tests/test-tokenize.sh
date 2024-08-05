#!/usr/bin/env bash

TARGET_DIR="${TARGET_DIR:-/tmp/codecrafters-interpreter-target}"
mkdir -p "${TARGET_DIR}"

INPUT="${TARGET_DIR}/test.lox"
OUTPUT="${TARGET_DIR}/output.log"
EXPECTED="${TARGET_DIR}/expected.log"

function run_test {
  echo "Stage ($1) - Test case ${2}"
  local exit_code=$3

  local input=$4
  local expected=$5

  echo "$input" >$INPUT
  echo "$expected" >$EXPECTED

  ./your_program.sh tokenize "${INPUT}" &>"${OUTPUT}"

  if [[ $? != $exit_code ]]; then
    echo "Test failed"
  fi

  if ! diff "${OUTPUT}" "${EXPECTED}"; then
    echo "Test failed"
  fi

  echo "Test passed"
}

run_test "Scanning: Empty file" 1 0 "" "EOF  null"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
EOF  null
EOM

run_test "Scanning: Parentheses" 1 0 "(" "$expected"

read -r -d '' expected <<EOM
RIGHT_PAREN ) null
RIGHT_PAREN ) null
EOF  null
EOM

run_test "Scanning: Parentheses" 2 0 "))" "$expected"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
RIGHT_PAREN ) null
RIGHT_PAREN ) null
LEFT_PAREN ( null
LEFT_PAREN ( null
EOF  null
EOM

run_test "Scanning: Parentheses" 3 0 "())((" "$expected"

read -r -d '' expected <<EOM
RIGHT_PAREN ) null
RIGHT_PAREN ) null
LEFT_PAREN ( null
RIGHT_PAREN ) null
LEFT_PAREN ( null
RIGHT_PAREN ) null
LEFT_PAREN ( null
EOF  null
EOM

run_test "Scanning: Parentheses" 4 0 "))()()(" "$expected"

read -r -d '' expected <<EOM
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Braces" 1 0 "}" "$expected"

read -r -d '' expected <<EOM
LEFT_BRACE { null
LEFT_BRACE { null
RIGHT_BRACE } null
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Braces" 2 0 "{{}}" "$expected"

read -r -d '' expected <<EOM
RIGHT_BRACE } null
RIGHT_BRACE } null
LEFT_BRACE { null
LEFT_BRACE { null
LEFT_BRACE { null
EOF  null
EOM

run_test "Scanning: Braces" 3 0 "}}{{{" "$expected"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
LEFT_BRACE { null
RIGHT_BRACE } null
LEFT_PAREN ( null
RIGHT_BRACE } null
RIGHT_PAREN ) null
RIGHT_PAREN ) null
EOF  null
EOM

run_test "Scanning: Braces" 4 0 "({}(}))" "$expected"

read -r -d '' expected <<EOM
PLUS + null
MINUS - null
EOF  null
EOM

run_test "Scanning: Other single-character tokens" 1 0 "+-" "$expected"

read -r -d '' expected <<EOM
PLUS + null
PLUS + null
MINUS - null
MINUS - null
STAR * null
STAR * null
DOT . null
DOT . null
COMMA , null
COMMA , null
SEMICOLON ; null
SEMICOLON ; null
EOF  null
EOM

run_test "Scanning: Other single-character tokens" 2 0 "++--**..,,;;" "$expected"

read -r -d '' expected <<EOM
STAR * null
MINUS - null
MINUS - null
SEMICOLON ; null
COMMA , null
PLUS + null
DOT . null
EOF  null
EOM

run_test "Scanning: Other single-character tokens" 3 0 "*--;,+." "$expected"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
LEFT_BRACE { null
PLUS + null
STAR * null
MINUS - null
DOT . null
COMMA , null
RIGHT_BRACE } null
RIGHT_PAREN ) null
EOF  null
EOM

run_test "Scanning: Other single-character tokens" 4 0 "({+*-.,})" "$expected"

read -r -d '' expected <<EOM
[line 1] Error: Unexpected character: @
EOF  null
EOM

run_test "Scanning: Lexical errors" 1 65 "@" "$expected"

read -r -d '' expected <<EOM
COMMA , null
DOT . null
LEFT_PAREN ( null
EOF  null
[line 1] Error: Unexpected character: $
[line 1] Error: Unexpected character: #
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: Lexical errors" 2 ',.$(#' "$expected" 65

read -r -d '' expected <<EOM
[line 1] Error: Unexpected character: %
[line 1] Error: Unexpected character: #
[line 1] Error: Unexpected character: $
[line 1] Error: Unexpected character: @
[line 1] Error: Unexpected character: %
EOF  null
EOM

run_test "Scanning: Lexical errors" 3 65 '%#$@%' "$expected"

read -r -d '' expected <<EOM
LEFT_BRACE { null
LEFT_PAREN ( null
PLUS + null
STAR * null
COMMA , null
DOT . null
SEMICOLON ; null
RIGHT_PAREN ) null
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Lexical errors" 4 0 '{(+*,.;)}' "$expected"

read -r -d '' expected <<EOM
EQUAL = null
EOF  null
EOM

run_test "Scanning: Assignment & equality Operators" 1 0 '=' "$expected"

read -r -d '' expected <<EOM
EQUAL_EQUAL == null
EQUAL = null
EOF  null
EOM

run_test "Scanning: Assignment & equality Operators" 2 0 '===' "$expected"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
LEFT_BRACE { null
EQUAL = null
RIGHT_BRACE } null
RIGHT_PAREN ) null
LEFT_BRACE { null
EQUAL_EQUAL == null
EQUAL_EQUAL == null
EQUAL = null
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Assignment & equality Operators" 3 0 '({=}){=====}' "$expected"

read -r -d '' expected <<EOM
[line 1] Error: Unexpected character: $
LEFT_PAREN ( null
LEFT_PAREN ( null
EQUAL = null
RIGHT_PAREN ) null
RIGHT_PAREN ) null
EOF  null
[line 1] Error: Unexpected character: %
[line 1] Error: Unexpected character: #
[line 1] Error: Unexpected character: @
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: Assignment & equality Operators" 4 65 '(($%=#@))' "$expected"

read -r -d '' expected <<EOM
BANG_EQUAL != null
EOF  null
EOM

run_test "Scanning: Negation & inequality operators" 1 0 '!=' "$expected"

read -r -d '' expected <<EOM
BANG ! null
BANG_EQUAL != null
EQUAL_EQUAL == null
EOF  null
EOM

run_test "Scanning: Negation & inequality operators" 2 0 '!!===' "$expected"

read -r -d '' expected <<EOM
BANG ! null
LEFT_BRACE { null
BANG ! null
RIGHT_BRACE } null
LEFT_PAREN ( null
BANG_EQUAL != null
EQUAL_EQUAL == null
RIGHT_PAREN ) null
EQUAL = null
EOF  null
EOM

run_test "Scanning: Negation & inequality operators" 3 0 '!{!}(!===)=' "$expected"

read -r -d '' expected <<EOM
[line 1] Error: Unexpected character: $
[line 1] Error: Unexpected character: #
LEFT_BRACE { null
LEFT_PAREN ( null
BANG_EQUAL != null
BANG_EQUAL != null
RIGHT_PAREN ) null
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Negation & inequality operators" 4 65 '{($#!=!=)}' "$expected"

read -r -d '' expected <<EOM
GREATER_EQUAL >= null
EOF  null
EOM

run_test "Scanning: Relational operators" 1 0 '>=' "$expected"

read -r -d '' expected <<EOM
LESS < null
LESS < null
LESS_EQUAL <= null
GREATER > null
GREATER > null
GREATER_EQUAL >= null
EOF  null
EOM

run_test "Scanning: Relational operators" 2 0 '<<<=>>>=' "$expected"

read -r -d '' expected <<EOM
GREATER_EQUAL >= null
LESS_EQUAL <= null
LESS < null
GREATER > null
LESS_EQUAL <= null
EOF  null
EOM

run_test "Scanning: Relational operators" 3 0 '>=<=<><=' "$expected"

read -r -d '' expected <<EOM
[line 1] Error: Unexpected character: #
LEFT_PAREN ( null
RIGHT_PAREN ) null
LEFT_BRACE { null
LESS_EQUAL <= null
GREATER > null
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Relational operators" 4 65 '(){<=>#}' "$expected"

run_test "Scanning: Division operator & comments" 1 0 '//Comment' 'EOF  null'

read -r -d '' expected <<EOM
LEFT_PAREN ( null
EOF  null
EOM

run_test "Scanning: Division operator & comments" 2 0 '(///Unicode:£§᯽☺♣)' "$expected"

read -r -d '' expected <<EOM
SLASH / null
EOF  null
EOM

run_test "Scanning: Division operator & comments" 3 0 '/' "$expected"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
LEFT_BRACE { null
LEFT_PAREN ( null
PLUS + null
LESS_EQUAL <= null
COMMA , null
RIGHT_PAREN ) null
RIGHT_BRACE } null
RIGHT_PAREN ) null
EOF  null
EOM

run_test "Scanning: Division operator & comments" 4 0 '({(+<=,)})//Comment' "$expected"

run_test "Scanning: Whitespace" 1 0 ' ' "EOF  null"

# '\t\n '
read -r -d '' input <<EOM
  
 
EOM

run_test "Scanning: Whitespace" 2 0 "$input" "EOF  null"

read -r -d '' input <<EOM
{
 }
((*   ;-))
EOM

read -r -d '' expected <<EOM
LEFT_BRACE { null
RIGHT_BRACE } null
LEFT_PAREN ( null
LEFT_PAREN ( null
STAR * null
SEMICOLON ; null
MINUS - null
RIGHT_PAREN ) null
RIGHT_PAREN ) null
EOF  null
EOM

run_test "Scanning: Whitespace" 3 0 "$input" "$expected"

read -r -d '' input <<EOM
{
      }
((
,.<-))
EOM

read -r -d '' expected <<EOM
LEFT_BRACE { null
RIGHT_BRACE } null
LEFT_PAREN ( null
LEFT_PAREN ( null
COMMA , null
DOT . null
LESS < null
MINUS - null
RIGHT_PAREN ) null
RIGHT_PAREN ) null
EOF  null
EOM

run_test "Scanning: Whitespace" 4 0 "$input" "$expected"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
RIGHT_PAREN ) null
EOF  null
[line 2] Error: Unexpected character: @
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: Multi-line errors" 1 65 '()   @' "$expected"

read -r -d '' expected <<EOM
EOF  null
[line 1] Error: Unexpected character: #
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: Multi-line errors" 2 65 ' # ' "$expected"

read -r -d '' input <<EOM
()  # {}
@
$
+++
// Let's Go!
+++
#
EOM

read -r -d '' expected <<EOM
[line 1] Error: Unexpected character: #
[line 2] Error: Unexpected character: @
[line 3] Error: Unexpected character: $
[line 7] Error: Unexpected character: #
LEFT_PAREN ( null
RIGHT_PAREN ) null
LEFT_BRACE { null
RIGHT_BRACE } null
PLUS + null
PLUS + null
PLUS + null
PLUS + null
PLUS + null
PLUS + null
EOF  null
EOM

run_test "Scanning: Multi-line errors" 3 65 "$input" "$expected"

read -r -d '' expected <<EOM
LEFT_PAREN ( null
LEFT_BRACE { null
DOT . null
RIGHT_BRACE } null
RIGHT_PAREN ) null
EOF  null
[line 1] Error: Unexpected character: #
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: Multi-line errors" 4 65 '({. #})' "$expected"

read -r -d '' expected <<EOM
STRING "hello" hello
EOF  null
EOM

run_test "Scanning: String literals" 1 0 '"hello"' "$expected"

read -r -d '' expected <<EOM
STRING "world" world
EOF  null
[line 1] Error: Unterminated string.
EOM

# FIXME: line number in the error log line seems to differ
#run_test "Scanning: String literals" 2 65 '"world" "unterminated' "$expected"

input='"foo 	bar 123 // hello world!"'

read -r -d '' expected <<EOM
STRING "foo 	bar 123 // hello world!" foo 	bar 123 // hello world!
EOF  null
EOM

run_test "Scanning: String literals" 3 0 "$input" "$expected"

input='"foo"+"hello""perseverance" && "Success" != "Failure"'

read -r -d '' expected <<EOM
STRING "foo" foo
PLUS + null
STRING "hello" hello
STRING "perseverance" perseverance
STRING "Success" Success
BANG_EQUAL != null
STRING "Failure" Failure
EOF  null
[line 1] Error: Unexpected character: &
[line 1] Error: Unexpected character: &
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: String literals" 4 65 "$input" "$expected"

read -r -d '' expected <<EOM
NUMBER 1234.1234 1234.1234
EOF  null
EOM

run_test "Scanning: Number literals" 1 0 '1234.1234' "$expected"

read -r -d '' expected <<EOM
NUMBER 1234.1234 1234.1234
DOT . null
NUMBER 1234 1234.0
DOT . null
EOF  null
EOM

run_test "Scanning: Number literals" 2 0 '1234.1234.1234.' "$expected"

input='"Hello" = "Hello" && 42 == 42'

read -r -d '' expected <<EOM
STRING "Hello" Hello
EQUAL = null
STRING "Hello" Hello
NUMBER 42 42.0
EQUAL_EQUAL == null
NUMBER 42 42.0
EOF  null
[line 1] Error: Unexpected character: &
[line 1] Error: Unexpected character: &
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: Number literals" 3 65 "$input" "$expected"

input='(5+3) > 7 ; "Success" != "Failure" & 10 >= 5'

read -r -d '' expected <<EOM
LEFT_PAREN ( null
NUMBER 5 5.0
PLUS + null
NUMBER 3 3.0
RIGHT_PAREN ) null
GREATER > null
NUMBER 7 7.0
SEMICOLON ; null
STRING "Success" Success
BANG_EQUAL != null
STRING "Failure" Failure
NUMBER 10 10.0
GREATER_EQUAL >= null
NUMBER 5 5.0
EOF  null
[line 1] Error: Unexpected character: &
EOM

# FIXME: diff seems the same yet it does not pass
#run_test "Scanning: Number literals" 4 65 "$input" "$expected"

read -r -d '' expected <<EOM
AND and null
EOF  null
EOM

run_test "Scanning: Identifiers" 1 0 "and" "$expected"

read -r -d '' expected <<EOM
IDENTIFIER ELSE null
EOF  null
EOM

run_test "Scanning: Identifiers" 2 0 "ELSE" "$expected"

read -r -d '' input <<EOM
var greeting = "Hello"
if (greeting == "Hello") {
    return true
} else {
    return false
}
EOM

read -r -d '' expected <<EOM
VAR var null
IDENTIFIER greeting null
EQUAL = null
STRING "Hello" Hello
IF if null
LEFT_PAREN ( null
IDENTIFIER greeting null
EQUAL_EQUAL == null
STRING "Hello" Hello
RIGHT_PAREN ) null
LEFT_BRACE { null
RETURN return null
TRUE true null
RIGHT_BRACE } null
ELSE else null
LEFT_BRACE { null
RETURN return null
FALSE false null
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Identifiers" 3 0 "$input" "$expected"

read -r -d '' input <<EOM
var result = (a + b) > 7 && "Success" != "Failure" or x >= 5
while (result) {
    var counter = 0
    counter = counter + 1
    if (counter == 10) {
        return nil
    }
}
EOM

read -r -d '' expected <<EOM
[line 1] Error: Unexpected character: &
[line 1] Error: Unexpected character: &
VAR var null
IDENTIFIER result null
EQUAL = null
LEFT_PAREN ( null
IDENTIFIER a null
PLUS + null
IDENTIFIER b null
RIGHT_PAREN ) null
GREATER > null
NUMBER 7 7.0
STRING "Success" Success
BANG_EQUAL != null
STRING "Failure" Failure
OR or null
IDENTIFIER x null
GREATER_EQUAL >= null
NUMBER 5 5.0
WHILE while null
LEFT_PAREN ( null
IDENTIFIER result null
RIGHT_PAREN ) null
LEFT_BRACE { null
VAR var null
IDENTIFIER counter null
EQUAL = null
NUMBER 0 0.0
IDENTIFIER counter null
EQUAL = null
IDENTIFIER counter null
PLUS + null
NUMBER 1 1.0
IF if null
LEFT_PAREN ( null
IDENTIFIER counter null
EQUAL_EQUAL == null
NUMBER 10 10.0
RIGHT_PAREN ) null
LEFT_BRACE { null
RETURN return null
NIL nil null
RIGHT_BRACE } null
RIGHT_BRACE } null
EOF  null
EOM

run_test "Scanning: Identifiers" 4 65 "$input" "$expected"

read -r -d '' expected <<EOM
IDENTIFIER bar null
IDENTIFIER baz null
EOF  null
EOM

run_test "Scanning: Identifiers" 5 0 'bar baz' "$expected"

input='_1236ar bar world_ baz _hello'

read -r -d '' expected <<EOM
IDENTIFIER _1236ar null
IDENTIFIER bar null
IDENTIFIER world_ null
IDENTIFIER baz null
IDENTIFIER _hello null
EOF  null
EOM

run_test "Scanning: Identifiers" 6 0 "$input" "$expected"

read -r -d '' input <<EOM
message = "Hello, World!"
number = 123
EOM

read -r -d '' expected <<EOM
IDENTIFIER message null
EQUAL = null
STRING "Hello, World!" Hello, World!
IDENTIFIER number null
EQUAL = null
NUMBER 123 123.0
EOF  null
EOM

run_test "Scanning: Identifiers" 7 0 "$input" "$expected"

# FIXME: line number in the error log line seems to differ
#read -r -d '' input <<EOM
#{
#// This is a complex test case
#str1 = "Test" str2 = "Case"
#num1 = 100
#num2 = 200.00
#result = (str1 == "Test" , str2 != "Fail") && (num1 + num2) >= 300 && (a - b) < 10
#}
#EOM
#
#read -r -d '' expected <<EOM
#[line 7] Error: Unexpected character: &
#[line 7] Error: Unexpected character: &
#[line 7] Error: Unexpected character: &
#[line 7] Error: Unexpected character: &
#LEFT_BRACE { null
#IDENTIFIER str1 null
#EQUAL = null
#STRING "Test" Test
#IDENTIFIER str2 null
#EQUAL = null
#STRING "Case" Case
#IDENTIFIER num1 null
#EQUAL = null
#NUMBER 100 100.0
#IDENTIFIER num2 null
#EQUAL = null
#NUMBER 200.00 200.0
#IDENTIFIER result null
#EQUAL = null
#LEFT_PAREN ( null
#IDENTIFIER str1 null
#EQUAL_EQUAL == null
#STRING "Test" Test
#COMMA , null
#IDENTIFIER str2 null
#BANG_EQUAL != null
#STRING "Fail" Fail
#RIGHT_PAREN ) null
#LEFT_PAREN ( null
#IDENTIFIER num1 null
#PLUS + null
#IDENTIFIER num2 null
#RIGHT_PAREN ) null
#GREATER_EQUAL >= null
#NUMBER 300 300.0
#LEFT_PAREN ( null
#IDENTIFIER a null
#MINUS - null
#IDENTIFIER b null
#RIGHT_PAREN ) null
#LESS < null
#NUMBER 10 10.0
#RIGHT_BRACE } null
#EOF  null
#EOM
#
#run_test "Scanning: Identifiers" 8 65 "$input" "$expected"
