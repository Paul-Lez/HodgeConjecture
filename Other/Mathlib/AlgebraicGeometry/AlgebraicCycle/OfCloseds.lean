/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Mathlib.AlgebraicGeometry.AlgebraicCycle.Support

import Mathlib.Algebra.Order.Group.Indicator
public import Other.Mathlib.Topology.NoetherianSpace
import Other.Mathlib.Topology.Sober

/-!
# The cycle of a closed subset

The cycle of a closed subset `S` with finitely many irreducible components has coefficient `1` at
the generic point of each irreducible component of `S` and `0` elsewhere. Its support is `S`.

## Main definitions

* `AlgebraicCycle.ofCloseds S`: the cycle of the closed subset `S`.

## Main results

* `AlgebraicCycle.closedSupport_ofCloseds`: the support of the cycle of `S` is `S`.
* `AlgebraicCycle.ofCloseds_eq_single_of_isGenericPoint`: the cycle of an irreducible closed subset
  is the cycle with coefficient `1` at its generic point.
-/

@[expose] public section

open TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}}

/-- The cycle of a closed subset `S` with finitely many irreducible components: the coefficient
is `1` at the generic point of each irreducible component of `S` and `0` elsewhere. This is the
cycle of the reduced closed subscheme with underlying set `S`. -/
noncomputable def ofCloseds (S : Closeds X) [NoetherianSpace S] : AlgebraicCycle X ℤ where
  toFun := (Subtype.val '' genericPoints S).indicator 1
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, Filter.univ_mem,
      ((genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image _).subset
        (Set.inter_subset_right.trans Set.support_indicator_subset)⟩

variable (S : Closeds X) [NoetherianSpace S]

/-- The cycle of `S` is the indicator function of the set of generic points of the irreducible
components of `S`. -/
@[simp]
lemma coe_ofCloseds : ⇑(ofCloseds S) = (Subtype.val '' genericPoints S).indicator 1 :=
  rfl

/-- The support of the cycle of `S` is the finite set of generic points of the irreducible
components of `S`. -/
@[simp]
lemma support_ofCloseds : (ofCloseds S).support = Subtype.val '' genericPoints S := by
  simp [Function.locallyFinsuppWithin.support]

/-- The support of the cycle of `S` is `S` itself, so `ofCloseds` is a right inverse of
`closedSupport`. -/
@[simp]
lemma closedSupport_ofCloseds : (ofCloseds S).closedSupport = S := by
  refine le_antisymm (closedSupport_le_iff.2 <| (support_ofCloseds S).trans_subset
    (Subtype.coe_image_subset _ _)) fun y hy ↦ ?_
  obtain ⟨x, hx, hxy⟩ := genericPoints.exists_specializes (⟨y, hy⟩ : S)
  exact mem_closedSupport.2
    ⟨x, by simp [hx], Scheme.le_iff_specializes.2 (hxy.map continuous_subtype_val)⟩

/-- The cycle of a closed subset is effective: all its coefficients are `0` or `1`. -/
lemma ofCloseds_nonneg : 0 ≤ ofCloseds S :=
  Function.locallyFinsuppWithin.le_def.2 (Set.indicator_nonneg fun _ _ ↦ zero_le_one)

/-- The cycle of an irreducible closed subset with generic point `x` is the cycle with
coefficient `1` at `x`. -/
lemma ofCloseds_eq_single_of_isGenericPoint [DecidableEq X] {x : X} (hx : IsGenericPoint x S) :
    ofCloseds S = Function.locallyFinsuppWithin.single x 1 := by
  have : IrreducibleSpace S := Subtype.irreducibleSpace hx.isIrreducible
  have hgen : IsGenericPoint (⟨x, hx.mem⟩ : S) Set.univ :=
    isGenericPoint_def.2 <| Set.eq_univ_of_forall fun y ↦ specializes_iff_mem_closure.1
      (IsInducing.subtypeVal.specializes_iff.1 (hx.specializes y.2))
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  simp [genericPoints_eq_singleton, (genericPoint_spec _).eq hgen, Pi.single_apply]

variable [NoetherianSpace X]

/-- The cycle of the empty closed subset is `0`. -/
@[simp]
lemma ofCloseds_bot : ofCloseds (⊥ : Closeds X) = 0 :=
  closedSupport_eq_bot_iff.1 (closedSupport_ofCloseds ⊥)

/-- The cycle of the closure of a point `x` is the cycle with coefficient `1` at `x`, the unique
generic point of `closure {x}`. -/
@[simp]
lemma ofCloseds_closure_singleton [DecidableEq X] (x : X) :
    ofCloseds (Closeds.closure {x}) = Function.locallyFinsuppWithin.single x 1 :=
  ofCloseds_eq_single_of_isGenericPoint _ isGenericPoint_closure

end AlgebraicGeometry.AlgebraicCycle
