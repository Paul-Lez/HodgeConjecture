#!/usr/bin/env bash
# Regenerate Challenge/Constructed.lean, the self-contained statement of `HodgeConjecture`, to
# its fixpoint and certify it. Run from the repository root after `lake build HodgeConjecture`.
#
# One pass is: generate the file (scripts/GenSpec.lean, with per-module elaboration reports cached
# in .lake/genspec/elab), compile it, record the ascriptions the compiler rejected
# (scripts/genspec_fallback.py, into scripts/genspec-state/HodgeConjecture.bare.json), build it,
# and audit it (scripts/SpecAudit.lean: declarations unreachable from the statement go to
# scripts/genspec-state/HodgeConjecture.drop.json). Both state files are committed, so a single
# pass reproduces the committed file and the audit reports nothing unneeded; the loop only matters
# after the repository's definitions change.
set -u
root=HodgeConjecture; file=Challenge/Constructed.lean; mod=Challenge.Constructed
log=.lake/genspec; mkdir -p "$log" scripts/genspec-state

generate_compile() {
  for round in 1 2 3; do
    echo "== generate (round $round) $(date +%T)"
    if ! lake env lean scripts/GenSpec.lean > "$log/genspec.out" 2> "$log/genspec.err"; then
      grep -i "error" "$log/genspec.out" "$log/genspec.err" | head -5; return 1
    fi
    grep "^==" "$log/genspec.out"; grep "left out\|forced bare\|helper failed" "$log/genspec.err"
    echo "== compile $(date +%T)"
    lake env lean "$file" > "$log/compile.log" 2>&1
    errs=$(grep -c "error" "$log/compile.log")
    echo "errors: $errs; warnings: $(grep -c 'warning' "$log/compile.log")"
    [ "$errs" = 0 ] && return 0
    grep "error" "$log/compile.log" | head -5
    out=$(python3 scripts/genspec_fallback.py "$root" "$file" "$log/compile.log"); echo "$out"
    case "$out" in "0 replacements"*|"no ascribed"*) return 1;; esac
  done
  return 1
}

for pass in 1 2 3; do
  generate_compile || { echo "compile errors remain; see $log/compile.log"; exit 1; }
  echo "== build $(date +%T)"
  lake build "$mod" > "$log/build.log" 2>&1 || { tail -20 "$log/build.log"; exit 1; }
  echo "== audit $(date +%T)"
  qbefore=$(cat "scripts/genspec-state/$root.qualify.json" 2>/dev/null)
  lake env lean --run scripts/SpecAudit.lean "$mod" "$root" "scripts/genspec-state/$root.drop.json" > "$log/audit.log" 2>&1
  head -4 "$log/audit.log"; grep "UNNEEDED\|SORRY-ONLY\|UNATTACHED\|DRIFT" "$log/audit.log"
  unneeded=$(grep -o "unneeded declarations: [0-9]*" "$log/audit.log" | grep -o "[0-9]*$"); unneeded=${unneeded:-1}
  drift=$(grep -o "drifting declarations: [0-9]*" "$log/audit.log" | grep -o "[0-9]*$"); drift=${drift:-0}
  if [ "$unneeded" = 0 ] && [ "$drift" = 0 ]; then
    echo "== $file compiles, every declaration in it is reachable from $root, and each uses the constants its source uses"
    git diff --quiet -- "$file" && echo "== $file is unchanged (fixpoint reproduced)"
    exit 0
  fi
  qafter=$(cat "scripts/genspec-state/$root.qualify.json" 2>/dev/null)
  if [ "$drift" != 0 ] && [ "$qbefore" = "$qafter" ]; then
    echo "drift remains and no further qualification helps; see $log/audit.log"; exit 1
  fi
done
echo "still not minimal after 3 passes"; exit 1
