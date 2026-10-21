#!/usr/bin/env bash
# At most two simultaneous interactive compiler jobs in this 8 GiB workspace.
# File-descriptor locks are automatically released when the job exits.
set -euo pipefail
dyson_project_root="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$dyson_project_root/.lake/compile-slots"
dyson_last_arg="${!#}"
if [[ "$dyson_last_arg" == "$dyson_project_root/"* ]]; then
  while [[ -f "$dyson_project_root/.lake/pause-verification" ]]; do
    sleep 0.2
  done
fi
while true; do
  for dyson_compile_slot in 1 2; do
    exec 9>"$dyson_project_root/.lake/compile-slots/$dyson_compile_slot.lock"
    if flock -n 9; then
      exec "$@"
    fi
    exec 9>&-
  done
  sleep 0.2
done
