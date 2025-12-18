#!/usr/bin/env bash
set -e

# Run the hic-check tool on toxcore files with necessary include paths.
# We need to find all .c and .h files in toxcore and its subdirectories,
# and also include defines.h from toxencryptsave.

ulimit -v 4000000

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

readarray -t HEADERS < <(find "$WORKSPACE_ROOT/c-toxcore/toxcore" -name "*.h" -exec realpath {} +)
DEFINES_H=$(realpath "$WORKSPACE_ROOT/c-toxcore/toxencryptsave/defines.h")

SOURCES=()
FLAGS=()
for arg in "$@"; do
    if [[ "$arg" == *.c ]]; then
        SOURCES+=("$(realpath "$arg")")
    else
        FLAGS+=("$arg")
    fi
done

if [ ${#SOURCES[@]} -eq 0 ]; then
    readarray -t SOURCES < <(find "$WORKSPACE_ROOT/c-toxcore/toxcore" -name "*.c" -exec realpath {} +)
fi

cd "$WORKSPACE_ROOT"
TMP_OUT=$(mktemp)
bazel run --ui_event_filters=-info --noshow_progress //hs-hic/tools:hic-check -- "${FLAGS[@]}" "${HEADERS[@]}" "${SOURCES[@]}" "$DEFINES_H" > "$TMP_OUT" 2>&1 || EXIT_CODE=$?

LINE_COUNT=$(wc -l < "$TMP_OUT")
if [ "$LINE_COUNT" -gt 200 ]; then
    cp "$TMP_OUT" hic-check.log
    echo "Full log saved to $(realpath hic-check.log)"
    head -n 100 "$TMP_OUT"
    echo ""
    echo "... $((LINE_COUNT - 200)) lines elided ..."
    echo ""
    tail -n 100 "$TMP_OUT"
else
    cat "$TMP_OUT"
fi

rm "$TMP_OUT"
exit ${EXIT_CODE:-0}
