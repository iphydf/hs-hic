#!/usr/bin/env bash
set -e
stack build --profile --fast --allow-different-user
BIN=/src/workspace/hs-hic/.stack-work/install/x86_64-linux-nix/153739851ec10a9ed78a6b93e6485e5e40dccd7af9965f37b67c84b1e50fe18a/9.4.8/bin/hic-check
readarray -t HEADERS < <(find /src/workspace/c-toxcore/toxcore -name "*.h" -exec realpath {} +)
DEFINES_H=$(realpath /src/workspace/c-toxcore/toxencryptsave/defines.h)
cd /tmp
"$BIN" +RTS -p -RTS --no-owner --no-nullable --solver ordered "${HEADERS[@]}" /src/workspace/c-toxcore/toxcore/net_crypto.c "$DEFINES_H" --max-errors 1
