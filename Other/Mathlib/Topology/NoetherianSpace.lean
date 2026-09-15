/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.NoetherianSpace

/-!
# Closed subsets of Noetherian spaces

A closed subset of a Noetherian space is a Noetherian space.
-/

@[expose] public section

namespace TopologicalSpace.Closeds

variable {X : Type*} [TopologicalSpace X]

/-- A closed subset of a Noetherian space is Noetherian: `NoetherianSpace.set` as an instance for
`Closeds`. -/
instance [NoetherianSpace X] (S : Closeds X) : NoetherianSpace S :=
  NoetherianSpace.set (S : Set X)

end TopologicalSpace.Closeds
