#!/usr/bin/env python3
"""Build Mean and compare example output with the checked-in snapshot."""

import argparse
import difflib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
EXAMPLES = "Examples/LeanToMean.lean"
EXPECTED = ROOT / "Examples" / "LeanToMean.out"


def run(*command: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        command, cwd=ROOT, capture_output=True, encoding="utf-8", check=False
    )


def example_output() -> tuple[str, int]:
    result = run("lake", "env", "lean", "--json", EXAMPLES)
    if result.returncode or result.stderr:
        raise RuntimeError(result.stdout + result.stderr)

    messages = [json.loads(line) for line in result.stdout.splitlines() if line]
    diagnostics = [m for m in messages if m["severity"] != "information"]
    if diagnostics:
        raise RuntimeError(json.dumps(diagnostics, ensure_ascii=False, indent=2))
    if not messages:
        raise RuntimeError("No example output was produced.")

    # Ignore file paths and source locations, which change when examples move.
    # Keep source order and every character of the actual messages, including
    # the leading blank lines emitted by the comparison commands.
    messages.sort(key=lambda m: (m["pos"]["line"], m["pos"]["column"]))
    return "".join(m["data"] + "\n" for m in messages), len(messages)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--update", action="store_true", help="replace the expected output; review the diff"
    )
    args = parser.parse_args()

    print("Building Mean and checking both directions...", flush=True)
    build = run("lake", "build")
    if build.returncode:
        print(build.stdout + build.stderr, file=sys.stderr)
        return 1

    try:
        actual, count = example_output()
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        print(f"Could not collect example output:\n{error}", file=sys.stderr)
        return 1

    if args.update:
        EXPECTED.parent.mkdir(parents=True, exist_ok=True)
        EXPECTED.write_bytes(actual.encode("utf-8"))
        print(f"Updated {EXPECTED.relative_to(ROOT)} ({count} examples). Review the diff.")
        return 0

    if not EXPECTED.exists():
        print("Expected output is missing. Run with --update to create it.", file=sys.stderr)
        return 1

    # Accept either checkout line ending; all other whitespace is significant.
    expected = EXPECTED.read_bytes().decode("utf-8").replace("\r\n", "\n")
    if actual != expected:
        diff = difflib.unified_diff(
            expected.splitlines(keepends=True),
            actual.splitlines(keepends=True),
            fromfile=str(EXPECTED.relative_to(ROOT)),
            tofile="actual example output",
        )
        sys.stdout.writelines(diff)
        print("Output changed. If intentional, run with --update and review the diff.")
        return 1

    print(f"PASS: {count} examples match {EXPECTED.relative_to(ROOT)}.")
    return 0


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    try:
        raise SystemExit(main())
    except OSError as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
