/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicUnitTransition
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# The holomorphic line bundle of a unit-sheaf extension

The transition functions obtained from local lifts of `1` in a unit-sheaf extension
define a rank-one complex vector bundle. Its transition functions are holomorphic,
so Mathlib's vector-bundle construction gives a holomorphic vector bundle.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance holomorphicLineBundleExtensionTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension X d)

/-- A transition function extended to the whole base, with value zero outside the overlap. -/
def transitionValue (i j x : ComplexPoint X) : ℂ := by
  classical
  exact if hx : x ∈ E.localLifts.opens i ⊓ E.localLifts.opens j then
    (E.transitionUnit i j (E.localLifts.opens i ⊓ E.localLifts.opens j)
      inf_le_left inf_le_right).val ⟨x, hx⟩
  else 0

/-- On its overlap, the total transition function is holomorphic. -/
theorem contMDiffOn_transitionValue (i j : ComplexPoint X) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (E.transitionValue i j)
      (↑(E.localLifts.opens i) ∩ ↑(E.localLifts.opens j)) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff (U := E.localLifts.opens i ⊓ E.localLifts.opens j)
    (x := ⟨x, hx⟩)).mp
  have hfun : (fun z : ↥(E.localLifts.opens i ⊓ E.localLifts.opens j) =>
      E.transitionValue i j z) =
      (E.transitionUnit i j (E.localLifts.opens i ⊓ E.localLifts.opens j)
        inf_le_left inf_le_right).val := by
    funext z
    exact dif_pos z.property
  rw [hfun]
  exact (E.transitionUnit i j (E.localLifts.opens i ⊓ E.localLifts.opens j)
    inf_le_left inf_le_right).val.contMDiff.contMDiffAt

/-- A self-transition has scalar value one. -/
theorem transitionValue_self (i x : ComplexPoint X) (hx : x ∈ E.localLifts.opens i) :
    E.transitionValue i i x = 1 := by
  rw [transitionValue, dif_pos (show x ∈ E.localLifts.opens i ⊓ E.localLifts.opens i from
    ⟨hx, hx⟩), transitionUnit_self]
  rfl

/-- Scalar transition functions satisfy the cocycle identity on triple overlaps. -/
theorem transitionValue_mul (i j k x : ComplexPoint X)
    (hx : x ∈ (E.localLifts.opens i ⊓ E.localLifts.opens j) ⊓ E.localLifts.opens k) :
    E.transitionValue i j x * E.transitionValue j k x = E.transitionValue i k x := by
  let V := (E.localLifts.opens i ⊓ E.localLifts.opens j) ⊓ E.localLifts.opens k
  have hi : V ≤ E.localLifts.opens i := inf_le_left.trans inf_le_left
  have hj : V ≤ E.localLifts.opens j := inf_le_left.trans inf_le_right
  have hk : V ≤ E.localLifts.opens k := inf_le_right
  let z : V := ⟨x, hx⟩
  have h := congrArg (fun u : (C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯)ˣ => u.val z)
    (E.transitionUnit_mul i j k V hi hj hk)
  change (E.transitionUnit i j V hi hj).val z * (E.transitionUnit j k V hj hk).val z =
    (E.transitionUnit i k V hi hk).val z at h
  rw [E.transitionUnit_restrict_apply i j inf_le_left inf_le_right (le_inf hi hj),
    E.transitionUnit_restrict_apply j k inf_le_left inf_le_right (le_inf hj hk),
    E.transitionUnit_restrict_apply i k inf_le_left inf_le_right (le_inf hi hk)] at h
  simpa only [transitionValue, dif_pos (show x ∈
    E.localLifts.opens i ⊓ E.localLifts.opens j from hx.1), dif_pos (show x ∈
    E.localLifts.opens j ⊓ E.localLifts.opens k from ⟨hx.1.2, hx.2⟩),
    dif_pos (show x ∈ E.localLifts.opens i ⊓ E.localLifts.opens k from ⟨hx.1.1, hx.2⟩)] using h

/-- The vector-bundle gluing data defined by the holomorphic transition functions. -/
def lineBundleCore : VectorBundleCore ℂ (ComplexPoint X) ℂ (ComplexPoint X) where
  baseSet i := E.localLifts.opens i
  isOpen_baseSet i := (E.localLifts.opens i).isOpen
  indexAt := id
  mem_baseSet_at := E.localLifts.mem_opens
  coordChange i j x := E.transitionValue i j x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    simp [E.transitionValue_self i x hx]
  continuousOn_coordChange i j :=
    (E.contMDiffOn_transitionValue i j).continuousOn.smul continuousOn_const
  coordChange_comp i j k x hx v := by
    change E.transitionValue j k x * (E.transitionValue i j x * v) =
      E.transitionValue i k x * v
    rw [← mul_assoc, mul_comm (E.transitionValue j k x), E.transitionValue_mul i j k x hx]

/-- The bundle glued from the extension has holomorphic transition functions. -/
instance lineBundleCore_isContMDiff :
    E.lineBundleCore.IsContMDiff 𝓘(ℂ, Fin d → ℂ) ω where
  contMDiffOn_coordChange i j :=
    (E.contMDiffOn_transitionValue i j).smul contMDiffOn_const

/-- Every fiber of the constructed bundle has complex dimension one. -/
theorem lineBundleCore_finrank (x : ComplexPoint X) :
    Module.finrank ℂ (E.lineBundleCore.Fiber x) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

end AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension
