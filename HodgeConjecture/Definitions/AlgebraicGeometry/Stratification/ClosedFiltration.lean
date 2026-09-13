/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Basic
/-!
# The canonical smooth decomposition as a closed filtration

This module indexes the recursive smooth decomposition by natural
numbers. Consecutive closed supports differ by the smooth piece. The filtration
is empty at the length of the finite list and stays empty thereafter. This
format exposes precisely the nested closed supports required for localization induction.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- Iteration of the reduced singular remainder, padded only by empty supports
after the finite decomposition terminates. -/
def reducedSmoothClosedFiltration (S : Closeds X) : ℕ → Closeds X
  | 0 => S
  | k + 1 => reducedClosedSingularRemainder f (reducedSmoothClosedFiltration S k)

variable [PerfectField K] [NoetherianSpace X]

end AlgebraicGeometry
