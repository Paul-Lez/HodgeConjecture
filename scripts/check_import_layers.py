#!/usr/bin/env python3
"""Check the statement's local import boundary without loading Lean or Mathlib."""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
STATEMENT = "HodgeConjecture.Statement"


def without_comments(source: str) -> str:
    """Remove Lean's nested block comments and line comments, retaining newlines."""
    result = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result.append(" ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and source.startswith("--", i):
            newline = source.find("\n", i)
            i = len(source) if newline == -1 else newline
        else:
            if not depth or source[i] == "\n":
                result.append(source[i])
            i += 1
    return "".join(result)


def main() -> int:
    paths = [ROOT / "HodgeConjecture.lean", *sorted((ROOT / "HodgeConjecture").rglob("*.lean"))]
    graph = {}
    for path in paths:
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        graph[module] = {
            dependency
            for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)",
                                   without_comments(path.read_text()), re.MULTILINE)
            for dependency in line.split()
            if dependency == "HodgeConjecture" or dependency.startswith("HodgeConjecture.")
        }

    errors = []
    for module, dependencies in graph.items():
        for dependency in dependencies - graph.keys():
            errors.append(f"{module}: missing local import {dependency}")

    closure = set()
    pending = [STATEMENT]
    while pending:
        module = pending.pop()
        if module not in closure:
            closure.add(module)
            pending.extend(graph.get(module, ()))

    for module in sorted(closure):
        if module == "HodgeConjecture.Other" or module.startswith("HodgeConjecture.Other."):
            errors.append(f"statement imports Other material: {module}")
    for module in sorted(graph):
        if module.startswith(("HodgeConjecture.Definitions.", "HodgeConjecture.Lemmas.")):
            if module not in closure:
                errors.append(f"unused statement-layer module belongs in Other: {module}")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Import layers OK: {len(closure) - 1} local dependencies of {STATEMENT}; no Other imports.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
