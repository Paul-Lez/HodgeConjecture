/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import HodgeConjecture.Statement

/-!
# Which definitions does the statement actually inspect?

A reader checking that `HodgeConjecture` says what it should has to unfold the definitions
the statement mentions, and the definitions *those* mention, and so on. That descent stops
at every proof: a term whose type is a `Prop` is interchangeable with any other proof of
the same `Prop`, so nothing about how it was built can change what the statement asserts.
A definition reached only through proofs therefore never has to be read, and belongs in
`HodgeConjecture.Lemmas` rather than `HodgeConjecture.Definitions`.

This script computes that distinction. It walks the dependencies of `HodgeConjecture`,
following the constants of every declaration's **type**, and the constants of its **body**
only when the body is data -- when the declaration is not itself a proof. What the walk
misses is exactly what no reader has to inspect.

Run it with

```
lake env lean scripts/PropOnlyDefinitions.lean
```

It prints the declarations of `HodgeConjecture.Definitions` that the statement never
inspects, grouped by module, and is a report rather than a gate. A proof-only definition
sometimes has to stay where it is:

* a lemma whose *statement* the reader does have to inspect may be proved with it, and
  that proof needs it in scope;
* instances are the common case, because they are found by resolution rather than by name,
  so no reading of the source reveals which proof depends on one;
* a `local instance` belongs to its file's context, since a module below it cannot
  register it there.

The complementary module-level checks live in `scripts/CheckStatementImports.lean` and
`scripts/check_import_layers.py`.
-/

open Lean Meta

namespace PropOnlyDefinitions

/-- Whether this declaration is a proof, so that proof irrelevance makes its body
immaterial. `Prop`-valued `instance`s land here too, which is what we want: nothing about
how such an instance was built is visible in what it proves. -/
def isProof (ci : ConstantInfo) : MetaM Bool := do
  match ci with
  | .thmInfo _ => return true
  | _ => try isProp ci.type catch _ => return false

/-- The constants the statement has to be read through, together with the data
declarations whose body was unavailable -- the walk is only complete if there are none. -/
partial def inspected (stack : List Name) (seen : Std.HashSet Name)
    (unreadable : Array Name) : MetaM (Std.HashSet Name × Array Name) := do
  match stack with
  | [] => return (seen, unreadable)
  | n :: rest =>
    if seen.contains n then inspected rest seen unreadable else
    let seen := seen.insert n
    let env ← getEnv
    let some ci := env.find? n | return (← inspected rest seen unreadable)
    let mut valueDeps : Array Name := #[]
    let mut unreadable := unreadable
    unless ← isProof ci do
      match ci.value? with
      | some v => valueDeps := v.getUsedConstants
      | none =>
        match ci with
        | .axiomInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => pure ()
        | _ => unreadable := unreadable.push n
    -- an inductive type is inspected through its constructors, and vice versa
    let structural : Array Name := match ci with
      | .inductInfo iv => iv.ctors.toArray
      | .ctorInfo cv => #[cv.induct]
      | .recInfo rv => rv.all.toArray
      | _ => #[]
    inspected ((ci.type.getUsedConstants ++ valueDeps ++ structural).toList ++ rest)
      seen unreadable

run_meta do
  let env ← getEnv
  let (seen, unreadable) ← inspected [`HodgeConjecture] {} #[]
  unless unreadable.isEmpty do
    logWarning m!"\
      {unreadable.size} data declaration(s) have no body in the imported environment, so \
      the walk below is incomplete:{indentD (.joinSep
        (unreadable.toList.map (m!"{·}")) "\n")}"
  let mut total := 0
  for i in [0 : env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    unless (`HodgeConjecture.Definitions).isPrefixOf moduleName do continue
    let mut uninspected : Array MessageData := #[]
    for c in env.header.moduleData[i]!.constNames do
      if c.isInternalDetail || seen.contains c then continue
      let some ci := env.find? c | continue
      -- proofs are not definitions, and a `notation` leaves a `«term...»` behind
      if (← isProof ci) || c.getString!.startsWith "term" then continue
      uninspected := uninspected.push m!"{c}"
    unless uninspected.isEmpty do
      total := total + uninspected.size
      logInfo m!"{moduleName}{indentD (.joinSep uninspected.toList "\n")}"
  logInfo m!"\
    the statement inspects {seen.size} declarations; {total} definition(s) of \
    `HodgeConjecture.Definitions` are reached only through proofs"

end PropOnlyDefinitions
