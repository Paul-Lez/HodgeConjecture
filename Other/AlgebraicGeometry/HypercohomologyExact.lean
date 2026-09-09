/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Exactness of analytic hypercohomology

A short exact sequence of actual analytic sheaf complexes induces the usual image-kernel
identity on the small-localization model of hypercohomology used by the Hodge filtration.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

local instance : HasDerivedCategory (AnalyticAdditiveSheaf s) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf s)

/-- In a short exact sequence, a hypercohomology class lifts through the first map exactly when
its image under the second map vanishes. -/
theorem hypercohomologyMap_exact
    (S : ShortComplex (CochainComplex (AnalyticAdditiveSheaf s) ℤ)) (hS : S.ShortExact)
    (n : ℤ) (α : Hypercohomology s S.X₂ n) :
    (∃ β, hypercohomologyMap s S.f n β = α) ↔ hypercohomologyMap s S.g n α = 0 := by
  constructor
  · rintro ⟨β, rfl⟩
    rw [← hypercohomologyMap_comp_apply, S.zero, hypercohomologyMap_zero]
    rfl
  · intro hα
    let e (K : CochainComplex (AnalyticAdditiveSheaf s) ℤ) :
        Hypercohomology s K n ≃ ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt s))
          (DerivedCategory.Q.obj K) n :=
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms s) DerivedCategory.Q
    let F := preadditiveCoyoneda.obj
      (Opposite.op (DerivedCategory.Q.obj (constantIntegerSheafComplexInt s)))
    have he := F.homologySequence_exact₂ (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS) n
    have hz : e S.X₂ α ≫ (DerivedCategory.Q.map S.g)⟦n⟧' = 0 := by
      have h := congrArg (e S.X₃) hα
      simpa [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
        hypercohomologyEquiv_zero, ShiftedHom.comp_mk₀] using h
    obtain ⟨β, hβ⟩ := (ShortComplex.ab_exact_iff _).1 he (e S.X₂ α) hz
    change β ≫ (DerivedCategory.Q.map S.f)⟦n⟧' = e S.X₂ α at hβ
    refine ⟨(e S.X₁).symm β, ?_⟩
    apply (e S.X₂).injective
    simpa [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp, ShiftedHom.comp_mk₀] using hβ

end AlgebraicGeometry.ComplexPoint
