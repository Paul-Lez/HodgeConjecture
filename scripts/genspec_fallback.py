#!/usr/bin/env python3
"""Mark ascribed `sorry`s that failed to type-check so that the next generation emits them bare.

Usage: python3 scripts/genspec_fallback.py <root> <generated file> <compile log>

For every compile error on a line of the generated file that contains an ascription
`(sorry : …)`, the ascription text is looked up in the helper reports under `.lake/genspec/elab/`, and
the matching replacements are appended to `scripts/genspec-state/<root>.bare.json`. Rerun
`scripts/GenSpec.lean` afterwards.
"""
import json, re, sys
from pathlib import Path

root, generated, log = sys.argv[1:4]
lines = Path(generated).read_text().split("\n")
error_lines = set()
for m in re.finditer(r"^" + re.escape(generated) + r":(\d+):\d+: error", Path(log).read_text(), re.M):
    error_lines.add(int(m.group(1)))

def ascriptions(text):
    """All `(sorry : …)` substrings with balanced parentheses."""
    out = []
    i = 0
    while True:
        j = text.find("(sorry : ", i)
        if j < 0:
            return out
        depth, k = 0, j
        while k < len(text):
            if text[k] == "(":
                depth += 1
            elif text[k] == ")":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        out.append(text[j:k + 1])
        i = k + 1

wanted = set()
for ln in error_lines:
    if 1 <= ln <= len(lines):
        wanted.update(ascriptions(lines[ln - 1]))
if not wanted:
    print("no ascribed sorry on any error line")
    sys.exit(0)

bare_path = Path(f"scripts/genspec-state/{root}.bare.json")
marks = json.loads(bare_path.read_text()) if bare_path.exists() else []
known = {(m["module"], m["a"], m["b"]) for m in marks}
added = 0
for rep in sorted(Path(".lake/genspec/elab").glob("*.json")):
    if rep.name.endswith(".bare.json"):
        continue
    d = json.loads(rep.read_text())
    mod = d.get("module")
    for c in d.get("commands", []):
        for r in c.get("reps", []):
            asc = r[2]
            if asc.startswith(":= "):
                asc = asc[3:]
            if asc in wanted and (mod, r[0], r[1]) not in known:
                marks.append({"module": mod, "a": r[0], "b": r[1]})
                known.add((mod, r[0], r[1]))
                added += 1
bare_path.write_text(json.dumps(marks, indent=1))
print(f"{added} replacements marked bare ({len(marks)} total) from {len(wanted)} failing ascriptions")
