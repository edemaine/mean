#!/usr/bin/env python3
"""Build Mean and compare example output with the checked-in snapshot."""

import argparse
import difflib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
EXAMPLES = (
    "Examples/LeanToMean.lean",
    "Examples/Wang.lean",
)


def run(*command: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        command, cwd=ROOT, capture_output=True, encoding="utf-8", check=False
    )


def example_output(source: str) -> tuple[str, int]:
    result = run("lake", "env", "lean", "--json", source)
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
    header = (
        f"-- Automatically generated from {source} by python test.py --update.\n"
        "-- Each comparison shows elaborated Lean input followed by its checked Mean output.\n"
    )
    source_text = (ROOT / source).read_text(encoding="utf-8").lstrip()
    opening_comment = source_text[2:].partition("-/")[0] if source_text.startswith("/-") else ""
    for line in opening_comment.splitlines():
        if line.startswith(("Upstream source: ", "Upstream license: ")):
            header += f"-- {line}\n"
    return header + "".join(m["data"] + "\n" for m in messages), len(messages)


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

    snapshots = []
    for source in EXAMPLES:
        try:
            actual, count = example_output(source)
        except (OSError, ValueError, KeyError, RuntimeError) as error:
            print(f"Could not collect output from {source}:\n{error}", file=sys.stderr)
            return 1
        snapshots.append((ROOT / Path(source).with_suffix(".mean"), actual, count))

    failed = False
    for path, actual, count in snapshots:
        relative = path.relative_to(ROOT)
        if args.update:
            path.write_bytes(actual.encode("utf-8"))
            print(f"Updated {relative} ({count} examples). Review the diff.")
            continue

        if not path.exists():
            print(f"Missing {relative}. Run with --update to create it.", file=sys.stderr)
            failed = True
            continue

        # Accept either checkout line ending; all other whitespace is significant.
        expected = path.read_bytes().decode("utf-8").replace("\r\n", "\n")
        if actual != expected:
            diff = difflib.unified_diff(
                expected.splitlines(keepends=True),
                actual.splitlines(keepends=True),
                fromfile=str(relative),
                tofile=f"actual output from {path.with_suffix('.lean').relative_to(ROOT)}",
            )
            sys.stdout.writelines(diff)
            print("Output changed. If intentional, run with --update and review the diff.")
            failed = True
        else:
            print(f"PASS: {count} examples match {relative}.")
    return int(failed)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    try:
        raise SystemExit(main())
    except OSError as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
