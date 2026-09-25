#!/usr/bin/env python3
"""Check designated API presence/kinds in the compiled, audited declaration inventory."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check(contract, declarations):
    owner = contract.get("primaryOwner")
    if not isinstance(owner, str) or not owner:
        raise ValueError("Missing primary owner in main declaration contract")
    expected = contract["declarations"]
    if not expected or len({item["name"] for item in expected}) != len(expected):
        raise ValueError("Empty or duplicate main declaration contract")
    rows = {}
    for row in declarations:
        if row["name"] in rows:
            raise ValueError("Duplicate inventory name: " + row["name"])
        rows[row["name"]] = row
    for item in expected:
        name = item["name"]
        if name not in rows:
            raise ValueError("Missing main declaration: " + name)
        row = rows[name]
        if row["kind"] != item["kind"] or row["primaryOwner"] != owner:
            raise ValueError("Main declaration kind/owner changed: " + name)
        if item.get("module") and row["originModule"] != item["module"]:
            raise ValueError("Main declaration origin changed: " + name)
        if not row["isSafeKernelRoot"] or row["nonstandardAxioms"] or row["hasTransitiveSorry"]:
            raise ValueError("Main declaration failed proof policy: " + name)
    return len(expected)

def sawin_inventory(verification):
    receipt_path = verification / "receipt.json"
    inventory_path = verification / "inventory/declarations.jsonl"
    receipt = json.loads(receipt_path.read_text())
    if receipt.get("passed") is not True or receipt.get("nanoDaRun") is not True:
        raise ValueError("Mandatory Sawin verification has not passed NanoDa")
    if receipt.get("independentKernelCheckPerformed") is not True or \
            receipt.get("replay", {}).get("officialKernelReplay") != "PASS":
        raise ValueError("Independent checker or official replay did not complete")
    core = {"build", "inventory", "selection", "export", "coverage", "nanoda", "replay"}
    stages = receipt["stages"]
    if [row["name"] for row in stages if row["name"] in core] != \
            ["build", "inventory", "selection", "export", "coverage", "nanoda", "replay"]:
        raise ValueError("Mandatory Sawin stage sequence changed")
    for row in stages:
        if row.get("passed") is not True or row.get("exitCode") != 0:
            raise ValueError("Sawin verification stage did not pass: " + row["name"])
        if row.get("log") and digest(Path(row["log"])) != row.get("logSHA256"):
            raise ValueError("Sawin verification stage log changed: " + row["name"])
    bound = receipt["artifactsSHA256"]
    if bound.get("inventory/declarations.jsonl") != digest(inventory_path):
        raise ValueError("Inventory artifact does not match successful receipt")
    for relative, expected_sha in bound.items():
        path = (verification / relative).resolve()
        if not path.is_relative_to(verification.resolve()) or not path.is_file() or \
                digest(path) != expected_sha:
            raise ValueError("Sawin verification artifact changed: " + relative)
    if bound.get("sealed-inputs.json") != receipt.get("sealedInputsSHA256"):
        raise ValueError("Sealed source/tool inputs changed")
    return receipt_path, inventory_path

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, required=True)
    parser.add_argument("--verification", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    report = {"passed": False, "startedUtc": datetime.now(timezone.utc).isoformat()}
    code = 1
    try:
        receipt_path, inventory_path = sawin_inventory(args.verification)
        count = check(json.loads(args.contract.read_text()),
                      (json.loads(line) for line in inventory_path.read_text().splitlines()))
        report.update(passed=True, declarationCount=count, inputSha256={
            str(path): digest(path) for path in [args.contract, receipt_path, inventory_path]})
        code = 0
    except Exception as error:
        report["error"] = str(error)
    report.update(exitCode=code, completedUtc=datetime.now(timezone.utc).isoformat(),
                  elapsedSeconds=round(time.monotonic() - start, 3),
                  scope="Presence and declaration kind; this does not compare theorem statements.")
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    return code

if __name__ == "__main__":
    raise SystemExit(main())
