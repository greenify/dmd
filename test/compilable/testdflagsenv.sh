#!/usr/bin/env bash

export DFLAGS="-version=Foo ${DFLAGS[@]}"

output="$($DMD -c -o- -v -conf= ${EXTRA_FILES}/${TEST_NAME}.d)"

echo "${output}" | grep "-version=Foo"
echo "${output}" | grep "predef.*Foo"

# test with a dummy config file
output="$($DMD -c -o- -v -conf=${EXTRA_FILES}/${TEST_NAME}.conf ${EXTRA_FILES}/${TEST_NAME}.d)"

echo "${output}" | grep "-version=Foo"
echo "${output}" | grep "predef.*Foo"

exit 1
