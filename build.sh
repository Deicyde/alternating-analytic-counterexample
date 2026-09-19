#!/bin/bash
# usage: ./build.sh AltCounter/Foo.lean
# Compiles ONE file against the prebuilt Mathlib and writes its .olean into .build/ so that other files can import it.
# At most 3 compilations run at the same time (memory!): a simple directory-lock semaphore.
cd "$(dirname "$0")"
LP="$(cat .leanpath):$PWD/.build"
f="$1"; mod="${f%.lean}"; out=".build/${mod}.olean"; mkdir -p "$(dirname "$out")" .locks
slot=""
while [ -z "$slot" ]; do
  for i in 1 2 3; do
    if mkdir ".locks/slot$i" 2>/dev/null; then slot=".locks/slot$i"; break; fi
  done
  [ -z "$slot" ] && sleep 3
done
trap 'rmdir "$slot" 2>/dev/null' EXIT
# stale-lock protection: locks older than 30 minutes are removed by whoever notices
find .locks -maxdepth 1 -type d -name 'slot*' -mmin +30 -exec rmdir {} \; 2>/dev/null
LEAN_PATH="$LP" lean -o "$out" -i ".build/${mod}.ilean" "$f"
