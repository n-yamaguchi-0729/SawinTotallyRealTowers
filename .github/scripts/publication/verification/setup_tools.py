#!/usr/bin/env python3
"""Install exact checker revisions; failures retain logs and a failed receipt."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

TOOLS = {
    "lean4export": ("https://github.com/leanprover/lean4export.git",
                    "6cea97789dc088ea47fcea15692db85685aedac5"),
    "nanoda_lib": ("https://github.com/ammkrn/nanoda_lib.git",
                   "4c544ed4099c8227f07d5de77ad1e69fb0740a27"),
}

def utc():
    return datetime.now(timezone.utc).isoformat()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkouts", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    receipt = {"passed": False, "startedUtc": utc(), "commands": [], "pins": TOOLS}
    code = 1

    def run(command, cwd=None):
        row = {"command": command, "cwd": str(cwd) if cwd else None, "startedUtc": utc(),
               "exitCode": None}
        receipt["commands"].append(row)
        began = time.monotonic()
        with (args.output / "setup.log").open("ab") as log:
            result = subprocess.run(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_NUM_THREADS="1", CARGO_BUILD_JOBS="1"))
        row.update(exitCode=result.returncode, completedUtc=utc(),
                   elapsedSeconds=round(time.monotonic() - began, 3))
        if result.returncode:
            raise RuntimeError("Tool setup command failed: " + repr(command))

    try:
        args.checkouts.mkdir(parents=True, exist_ok=False)
        for name, (url, commit) in TOOLS.items():
            dest = args.checkouts / name
            run(["git", "init", str(dest)])
            run(["git", "-C", str(dest), "remote", "add", "origin", url])
            run(["git", "-C", str(dest), "fetch", "--depth=1", "origin", commit])
            run(["git", "-C", str(dest), "checkout", "--detach", commit])
        run(["lake", "--no-ansi", "build", "Export"], args.checkouts / "lean4export")
        run(["cargo", "build", "--release", "--locked", "--bin", "nanoda_bin"],
            args.checkouts / "nanoda_lib")
        for name, (_, commit) in TOOLS.items():
            dest = args.checkouts / name
            actual = subprocess.check_output(["git", "-C", str(dest), "rev-parse", "HEAD"],
                                             text=True).strip()
            dirty = subprocess.check_output(["git", "-C", str(dest), "status", "--porcelain",
                                             "--untracked-files=all"], text=True).strip()
            if actual != commit or dirty:
                raise RuntimeError("Tool checkout is not exact and clean: " + name)
        receipt["rustcVersion"] = subprocess.check_output(["rustc", "--version"], text=True).strip()
        receipt["cargoVersion"] = subprocess.check_output(["cargo", "--version"], text=True).strip()
        receipt["passed"], code = True, 0
    except Exception as error:
        receipt["error"] = str(error)
    finally:
        log = args.output / "setup.log"
        receipt.update(completedUtc=utc(), elapsedSeconds=round(time.monotonic() - start, 3),
                       exitCode=code, logSha256=hashlib.sha256(log.read_bytes()).hexdigest()
                       if log.is_file() else None)
        (args.output / "setup.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return code

if __name__ == "__main__":
    raise SystemExit(main())
