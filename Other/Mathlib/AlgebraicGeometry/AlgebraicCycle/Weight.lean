/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Other.Mathlib.Topology.LocallyFinsupp

/-!
# Cycles of a given weight

The cycles whose points of nonzero coefficient all have a given weight for a weight function on
the points, such as the dimension or the codimension, form a subgroup of the algebraic cycles: the
cycles supported in a fiber of the weight function, `Function.locallyFinsupp.supported`.

## Main definitions

* `AlgebraicCycle.weightSubgroup X R w n`: the cycles whose points of nonzero coefficient have
  weight `n` for the weight function `w`.
* `AlgebraicCycle.dimSubgroup X R k` and `AlgebraicCycle.codimSubgroup X R p`: the cycles of
  dimension `k` and the cycles of codimension `p`.

## Main results

* `AlgebraicCycle.map_mem_weightSubgroup`: the pushforward of a cycle of weight `n` has weight
  `n`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable (X : Scheme.{u}) (R : Type*)

section AddGroup

variable [AddGroup R]

/-- The cycles whose points of nonzero coefficient all have weight `n` for the weight function
`w`, for example the dimension or the codimension of a point: the cycles supported in the fiber
`w ⁻¹' {n}`, so the `Function.locallyFinsupp.supported` API applies to them directly. -/
abbrev weightSubgroup {N : Type*} (w : X → N) (n : N) : AddSubgroup (AlgebraicCycle X R) :=
  Function.locallyFinsupp.supported X R (w ⁻¹' {n})

/-- The cycles of dimension `k`, the dimension of a point being its height for the specialization
order, that is, the dimension of its closure. -/
noncomputable abbrev dimSubgroup (k : ℕ∞) : AddSubgroup (AlgebraicCycle X R) :=
  weightSubgroup X R Order.height k

/-- The cycles of codimension `p`, the codimension of a point being its coheight for the
specialization order, that is, the codimension of its closure. -/
noncomputable abbrev codimSubgroup (p : ℕ∞) : AddSubgroup (AlgebraicCycle X R) :=
  weightSubgroup X R Order.coheight p

variable {X R}

/-- Membership in `weightSubgroup X R w n`, unfolded pointwise: every point with a nonzero
coefficient has weight `n`. -/
lemma mem_weightSubgroup {N : Type*} {w : X → N} {n : N} {c : AlgebraicCycle X R} :
    c ∈ weightSubgroup X R w n ↔ ∀ x, c x ≠ 0 → w x = n :=
  Iff.rfl

end AddGroup

section Map

variable {X R} [Ring R] {Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] {N : Type*}
  [DecidableEq N] {wx : X → N} {wy : Y → N} {n : N} {c : AlgebraicCycle X R}

/-- The pushforward of a cycle of weight `n` has weight `n`: `map f wx wy` only counts the points
`x` with `wx x = wy (f.base x)`, its coefficient `mapCoeff` vanishing at every other point. -/
lemma map_mem_weightSubgroup (hc : c ∈ weightSubgroup X R wx n) :
    map f wx wy c ∈ weightSubgroup Y R wy n :=
  Function.locallyFinsupp.support_map_subset_of_forall_mem _ _ _ _ _ hc fun x (hx : wx x = n) hw ↦
    by_contra fun hne ↦ hw <| by simp [mapCoeff, hx, Ne.symm hne]

end Map

end AlgebraicGeometry.AlgebraicCycle
