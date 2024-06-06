#! /bin/bash

# This script copies TypeScript conformance test cases and their associated
# reference files from the specified source directory.

if [ "$DEBUG" = "true" ] || [ "$DEBUG" = "1" ]; then
    DEBUG=true
    set -x
else
    DEBUG=false
fi

CASES_DEST="./tests/ts-conformance/cases"
REF_DEST="./tests/ts-conformance/reference"

if [ ! -d "$CASES_DEST" ]; then
    echo "Cannot find $CASES_DEST"
    echo "devtools/copy-ts-tests.sh must be run from SKJS root directory"
    exit 1
fi

if [ ! -d "$REF_DEST" ]; then
    echo "Cannot find $REF_DEST"
    exit 1
fi

if [ -z "$1" ]; then
    echo "Usage: devtools/copy-ts-tests.sh path/to/conformance/tests/to/copy'"
    exit 1
fi

TO_COPY="$(realpath --canonicalize-existing "$1")"

if [ ! -d "$TO_COPY" ]; then
    echo "Cannot find test directory $TO_COPY"
    exit 1
fi

TESTS_ROOT="$TO_COPY"

while test "$(basename "$TESTS_ROOT")" != "conformance"; do
    TESTS_ROOT="$(dirname "$TESTS_ROOT")"
    if [ "$TESTS_ROOT" = "/" ]; then
        echo "Cannot find conformance in the path $TO_COPY"
        exit 1
    fi
done

RELATIVE_PATH="${TO_COPY#"$TESTS_ROOT"/}"

TESTS_ROOT="${TESTS_ROOT%/cases/conformance}"
REF_DIR="$TESTS_ROOT/baselines/reference"

if [ ! -d "$REF_DIR" ]; then
    echo "Cannot find reference directory $REF_DIR"
    exit 1
fi

DEST="$CASES_DEST/$RELATIVE_PATH"
mkdir --parents "$DEST"

cp --recursive --interactive --verbose "$TO_COPY"/* "$DEST"

shopt -s globstar nullglob
for F in "$DEST"/**/*; do
    if [ ! -f "$F" ]; then
        continue
    fi
    if [ "${F: -3}" != ".ts" ]; then
        echo "Unexpected non-ts file: $F"
        exit 1
    fi
    B="$(basename "$F")"
    B="${B%.*}"
    REF="$REF_DIR/$B.errors.txt"
    if [ -f "$REF" ]; then
        cp --interactive --verbose "$REF" "$REF_DEST"
    fi
done

if $DEBUG; then
    set +x
fi
