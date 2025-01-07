#!/usr/bin/env bash

if [[ "$#" -lt 1 ]]; then
	echo "Expected a command to test as an argument"
	exit 1
fi

COMMAND="${1}"

TARGET_DIR="${TARGET_DIR:-/tmp/codecrafters-interpreter-target}"
mkdir -p "${TARGET_DIR}"

function run_test {
	echo "Testing ${COMMAND} on '${1}'"

	local input="${1}"
	local expected="${input%lox}out"

	local outdir="${TARGET_DIR}/$(dirname $expected)"
	mkdir -p "${outdir}"

	local output="${outdir}/$(basename $expected)"

	./your_program.sh "${COMMAND}" "${input}" &>"${output}"

	if diff "${output}" "${expected}"; then
		echo "✔ Test passed"
	else
		echo "𐄂 Test failed"
	fi
}

success=true

for file in $(find tests/ui/"${COMMAND}" -type f -name '*.lox'); do
	run_test $file

	if [[ $? != 0 ]]; then
		success=false
	fi

done

echo
if [[ "$success" = true ]]; then
	echo "✔ All test have passed!"
else
	echo "𐄂 Some tests have failed!"
fi
