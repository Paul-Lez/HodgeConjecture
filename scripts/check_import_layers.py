#!/usr/bin/env python3
"""Check local library and statement import boundaries without loading Lean or Mathlib."""

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


def import_closure(graph: dict[str, set[str]], root: str) -> set[str]:
    closure = set()
    pending = [root]
    while pending:
        module = pending.pop()
        if module not in closure:
            closure.add(module)
            pending.extend(graph.get(module, ()))
    return closure


def main() -> int:
    paths = [
        path
        for library in ("HodgeConjecture", "Other")
        for path in [ROOT / f"{library}.lean", *sorted((ROOT / library).rglob("*.lean"))]
    ]
    graph = {}
    for path in paths:
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        graph[module] = {
            dependency
            for line in re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)",
                                   without_comments(path.read_text()), re.MULTILINE)
            for dependency in line.split()
            if dependency in ("HodgeConjecture", "Other")
            or dependency.startswith(("HodgeConjecture.", "Other."))
        }

    errors = []
    for module, dependencies in graph.items():
        for dependency in dependencies - graph.keys():
            errors.append(f"{module}: missing local import {dependency}")
        if module == "HodgeConjecture" or module.startswith("HodgeConjecture."):
            for dependency in sorted(dependencies):
                if dependency == "Other" or dependency.startswith("Other."):
                    errors.append(f"HodgeConjecture library imports Other material: {module} -> {dependency}")

    if "HodgeConjecture" not in graph["Other"]:
        errors.append("Other umbrella must import HodgeConjecture")

    closure = import_closure(graph, STATEMENT)

    for module in sorted(closure):
        if module == "Other" or module.startswith("Other."):
            errors.append(f"statement imports Other material: {module}")
    for module in sorted(graph):
        if module.startswith(("HodgeConjecture.Definitions.", "HodgeConjecture.Lemmas.")):
            if module not in closure:
                errors.append(f"unused statement-layer module belongs in Other: {module}")
        if module.startswith("HodgeConjecture.Mathlib.") and module not in closure:
            errors.append(f"support-only Mathlib helper belongs in Other: {module}")

    for library in ("HodgeConjecture", "Other"):
        modules = {module for module in graph
                   if module == library or module.startswith(f"{library}.")}
        for module in sorted(modules - import_closure(graph, library)):
            errors.append(f"{library} umbrella does not import module: {module}")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Import layers OK: {len(closure) - 1} local dependencies of {STATEMENT}; no Other imports.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
