#!/usr/bin/env python3
"""Build Mean and check Mean-only and paired Lean/Mean example snapshots."""

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


def example_outputs(source: str) -> tuple[dict[str, str], int]:
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
    header = f"-- Automatically generated from {source} by python test.py --update.\n"
    source_text = (ROOT / source).read_text(encoding="utf-8").lstrip()
    opening_comment = source_text[2:].partition("-/")[0] if source_text.startswith("/-") else ""
    attribution = ""
    for line in opening_comment.splitlines():
        if line.startswith(("Upstream source: ", "Upstream license: ")):
            attribution += f"-- {line}\n"

    comparisons = []
    renderings = []
    for message in messages:
        comparison = message["data"]
        if not comparison.startswith("\n-- LEAN INPUT:\n"):
            raise ValueError(f"Expected a Lean/Mean comparison, got:\n{comparison}")
        _, separator, mean = comparison.partition("\n-- MEAN OUTPUT:\n")
        if not separator or not mean:
            raise ValueError(f"Missing Mean output in comparison:\n{comparison}")
        comparisons.append(comparison + "\n")
        renderings.append("\n" + mean + "\n")

    paired_path = Path(source).with_suffix(".compare").as_posix()
    return {
        ".mean": header
        + f"-- Checked Mean output; see {paired_path} for paired Lean/Mean comparisons.\n"
        + attribution
        + "".join(renderings),
        ".compare": header
        + "-- Each comparison shows elaborated Lean input followed by its checked Mean output.\n"
        + attribution
        + "".join(comparisons),
    }, len(messages)


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
            outputs, count = example_outputs(source)
        except (OSError, ValueError, KeyError, RuntimeError) as error:
            print(f"Could not collect output from {source}:\n{error}", file=sys.stderr)
            return 1
        snapshots.extend(
            (ROOT / Path(source).with_suffix(suffix), actual, count)
            for suffix, actual in outputs.items()
        )

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
