#!/usr/bin/env bash
# Copyright 2026 Naganori Yamaguchi.
# Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
# https://github.com/n-yamaguchi-0729
# Run a normal Lake stage and preserve enough disk space for runner diagnostics.
set -euo pipefail

if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_ENVIRONMENT:-}" != github-hosted ]]; then
  echo 'This disk-guarded build is restricted to ephemeral GitHub-hosted runners.' >&2
  exit 2
fi
if (( $# < 1 )) || [[ ! "$1" =~ ^(depth[123](-[a-z0-9-]+)?|library-[a-z0-9-]+|all)$ ]]; then
  echo 'Usage: library-build.sh library-name --library Prefix | all +Nyll.All' >&2
  exit 2
fi
stage="$1"
shift
if [[ "${1:-}" == --library ]]; then
  if (( $# != 2 )); then
    echo 'A library stage requires exactly one audited prefix.' >&2
    exit 2
  fi
  library="$2"
  plan_dir="tmp/ci-libraries/$stage-plan"
  python3 -B "${LIBRARY_PLANNER:-.github/scripts/build_stage.py}" --root . --library "$library" \
    --config "${LIBRARY_CONFIG:-.github/scripts/manifest-config.json}" \
    --output "$plan_dir" --plan-only
  python3 -B - "$plan_dir/receipt.json" > "$plan_dir/targets.txt" <<'PY'
import json
import sys
with open(sys.argv[1], encoding="utf-8") as stream:
    plan = json.load(stream)
if not plan["planOnly"] or plan["exitCode"] != 0:
    raise SystemExit("Invalid audited library frontier")
for module in plan["frontier"]:
    print("+" + module)
PY
  mapfile -t targets < "$plan_dir/targets.txt"
  if (( ${#targets[@]} == 0 )); then
    echo "No included sources in $library; the final owner stage checks all included modules."
    exit 0
  fi
  set -- "${targets[@]}"
fi
if (( $# == 0 )); then
  echo 'Missing Lake target.' >&2
  exit 2
fi
if [[ "$stage" == all ]]; then
  set -- "$@" +Nyll
fi
for target in "$@"; do
  if [[ ! "$target" =~ ^\+[A-Za-z0-9_.]+$ ]]; then
    echo 'Invalid Lake target.' >&2
    exit 2
  fi
done

mkdir -p tmp/ci-libraries
log="tmp/ci-libraries/$stage.log"
minimum_free_kib=2097152
build_pid=''
cleanup() {
  if [[ -n "$build_pid" ]] && kill -0 "$build_pid" 2>/dev/null; then
    kill -TERM -- "-$build_pid" 2>/dev/null || true
    sleep 2
    kill -KILL -- "-$build_pid" 2>/dev/null || true
    wait "$build_pid" 2>/dev/null || true
  fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

available_kib() {
  df -Pk . "${RUNNER_TEMP:-.}" / | awk 'NR > 1 && (!seen++ || $4 < free) { free=$4 } END { print free }'
}
free_kib="$(available_kib)"
if (( free_kib < minimum_free_kib )); then
  echo "::error::Insufficient disk space before $stage: $free_kib KiB free." | tee "$log"
  exit 1
fi

# Give Lake and tee one process group, so a capacity failure stops this stage only.
setsid bash -c 'set -o pipefail; log="$1"; shift; lake --wfail --no-ansi build "$@" 2>&1 | tee "$log"' \
  bash "$log" "$@" &
build_pid=$!
capacity_failed=false
polls=0
while kill -0 "$build_pid" 2>/dev/null; do
  free_kib="$(available_kib)"
  if (( free_kib < minimum_free_kib )); then
    capacity_failed=true
    cleanup
    echo "::error::Disk capacity guard stopped $stage with $free_kib KiB free." | tee -a "$log"
    break
  fi
  (( polls += 1 ))
  if (( polls % 15 == 0 )); then
    echo "$stage: $free_kib KiB free" | tee -a tmp/ci-libraries/capacity.log
  fi
  sleep 2
done
status=0
wait "$build_pid" || status=$?
build_pid=''
if [[ "$capacity_failed" == true ]]; then
  exit 1
fi
if (( status != 0 )); then
  exit "$status"
fi
