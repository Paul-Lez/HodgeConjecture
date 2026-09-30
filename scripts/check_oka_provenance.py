#!/usr/bin/env python3
"""Check the source marker and import boundary of the local Oka port."""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
OKA = ROOT / "Other" / "Oka"
UMBRELLA = ROOT / "Other" / "Oka.lean"
UPSTREAM = "https://github.com/chrisflav/oka"
REVISION = "441d02e06e68ba6ebeddd7e0e7240c766c3c3c09"
MATHLIB = "v4.33.1"
ROOTS = {
    "Other.Oka.Analytification.GAGA.Proper.Equivalence",
    "Other.Oka.Analytification.RET.EtaleLocalIso",
}


def without_comments(source: str) -> str:
    result = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
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


def imports(source: str) -> set[str]:
    return {
        dependency
        for line in re.findall(
            r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)",
            without_comments(source),
            re.MULTILINE,
        )
        for dependency in line.split()
    }


def main() -> int:
    paths = sorted(OKA.rglob("*.lean"))
    modules = {".".join(path.relative_to(ROOT).with_suffix("").parts): path for path in paths}
    graph = {module: imports(path.read_text()) for module, path in modules.items()}
    errors = []
    marker = re.compile(
        rf"Adapted from {re.escape(UPSTREAM)} at commit\s+"
        rf"{REVISION} for Mathlib {re.escape(MATHLIB)}\."
    )

    for module, path in modules.items():
        source = path.read_text()
        if not marker.search(source):
            errors.append(f"{path.relative_to(ROOT)}: missing exact upstream revision marker")
        for dependency in sorted(imports(source)):
            if not (
                dependency == "Mathlib"
                or dependency.startswith("Mathlib.")
                or dependency.startswith("Other.Oka.")
            ):
                errors.append(f"{module}: port escapes its boundary via {dependency}")
            if dependency.startswith("Other.Oka.") and dependency not in modules:
                errors.append(f"{module}: missing local import {dependency}")

    umbrella_imports = imports(UMBRELLA.read_text())
    if umbrella_imports != ROOTS:
        errors.append(
            f"Other/Oka.lean: expected roots {sorted(ROOTS)}, got {sorted(umbrella_imports)}"
        )

    reachable = set()
    pending = list(ROOTS)
    while pending:
        module = pending.pop()
        if module not in reachable:
            reachable.add(module)
            pending.extend(graph.get(module, set()) & modules.keys())
    for module in sorted(modules.keys() - reachable):
        errors.append(f"Other.Oka umbrella does not reach {module}")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(
        f"Oka provenance OK: {len(modules)} modules pinned to {REVISION}; "
        "imports stay within Mathlib and Other.Oka."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
