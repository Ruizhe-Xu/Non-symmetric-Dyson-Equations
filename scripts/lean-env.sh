#!/usr/bin/env bash
set -euo pipefail
dyson_project_root="$(cd "$(dirname "$0")/.." && pwd)"
dyson_lean_root="${DYSON_LEAN_ROOT:-/tmp/lean-native-4.24.0}"
# On a normal machine use the pinned elan toolchain. The native-runtime
# override and /proc compatibility shim are only needed on this host.
if [[ -x "$dyson_lean_root/bin/lean" ]]; then
  export PATH="$dyson_project_root/scripts/bin:$dyson_lean_root/bin:$PATH"
  export LEAN_SYSROOT="$dyson_lean_root"
  if [[ -f "$dyson_project_root/scripts/lean_proc_self_compat.so" ]]; then
    export LD_PRELOAD="$dyson_project_root/scripts/lean_proc_self_compat.so${LD_PRELOAD:+:$LD_PRELOAD}"
  fi
fi
if command -v flock >/dev/null 2>&1 && [[ "${1:-}" == "lake" && "${2:-}" == "env" && "${3:-}" == "lean" ]]; then
  exec bash "$dyson_project_root/scripts/lean-compile-queue.sh" "$@"
fi
exec "$@"
