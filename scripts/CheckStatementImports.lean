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
# The statement does not depend on the `Other` library

The repository is split into three layers:

* `HodgeConjecture.Definitions`: definitions appearing in the statement of the conjecture;
* `HodgeConjecture.Lemmas`: results needed to build those definitions;
* `Other`: everything else.

The point of the split is that `Other` is *downstream* of the conjecture: nothing there may be
needed to state it. This file enforces that by importing the statement and inspecting the resulting
environment, so the check runs against the real import graph rather than a syntactic approximation
of it. It is built by `lake build`, and fails the build if the invariant is broken.

The complementary syntactic checks -- that every `Definitions`/`Lemmas` module really is used by
the statement, and that both umbrella modules are complete -- live in `scripts/check_import_layers.py`.
-/

open Lean

run_cmd do
  let offenders := (← getEnv).allImportedModuleNames.filter fun m => (`Other).isPrefixOf m
  unless offenders.isEmpty do
    throwError "\
      `HodgeConjecture.Statement` transitively imports {offenders.size} module(s) of the `Other` \
      library:{indentD (.joinSep (offenders.toList.map (m!"{·}")) "\n")}\n\n\
      Anything the statement needs belongs in `HodgeConjecture.Definitions` (if it defines \
      something the statement mentions) or in `HodgeConjecture.Lemmas` (if it only supports such a \
      definition). Move the offending modules there, or drop the dependency."
