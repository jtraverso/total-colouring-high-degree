#!/usr/bin/env bash
# Same protocol as /c/lean/palomar-helpers/lean_locked.sh (global mkdir lock, LEAN_NUM_THREADS=1),
# polling every 0.5 s instead of 5 s.
LOCK=/c/lean/.lean_global_lock
PROJ=$1; shift
while true; do
  if mkdir "$LOCK" 2>/dev/null; then
    echo $$ > "$LOCK/pid"; date +%s > "$LOCK/since"; echo "$PROJ $*" > "$LOCK/what"
    break
  fi
  holder=$(cat "$LOCK/pid" 2>/dev/null)
  if [ -n "$holder" ] && ! kill -0 "$holder" 2>/dev/null; then
    rm -rf "$LOCK"; continue
  fi
  sleep 0.5
done
trap 'rm -rf "$LOCK"' EXIT
cd "$PROJ" || exit 2
export LEAN_NUM_THREADS=1
timeout "${LEAN_LOCK_TIMEOUT:-3600}" "$@"
