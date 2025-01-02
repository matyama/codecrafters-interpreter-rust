#!/usr/bin/env bash

TARGET_DIR="${TARGET_DIR:-/tmp/codecrafters-interpreter-target}"
mkdir -p "${TARGET_DIR}"

function run_test {
	echo "Testing run on '${1}'"

	local input="${1}"
	local expected="${input%lox}out"

	local outdir="${TARGET_DIR}/$(dirname $expected)"
	mkdir -p "${outdir}"

	local output="${outdir}/$(basename $expected)"

	./your_program.sh run "${input}" &>"${output}"

	if diff "${output}" "${expected}"; then
		echo "✔ Test passed"
	else
		echo "𐄂 Test failed"
	fi
}

for file in $(find tests/ui/run -type f -name '*.lox'); do
	run_test $file
done
