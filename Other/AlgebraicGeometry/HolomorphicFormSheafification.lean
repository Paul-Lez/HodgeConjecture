/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham
public import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sheafification preserves nonzero holomorphic forms

The analytic form relations are exactly the kernel of fixed-chart evaluation.
Since evaluation commutes with restriction, a form that vanishes locally is
already zero. Consequently the map to the actual holomorphic de Rham sheaf is
injective on sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Coordinate evaluation already detects precisely the analytic form relations:
restriction does not add new vanishing conditions. -/
theorem holomorphicFormRelations_eq_chartEvaluationKernel
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations X d U p = chartEvaluationKernel X d U p := by
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
  apply le_antisymm
  · intro r hr
    simp only [restrictionStableAnalyticKernel, Submodule.mem_iInf, Submodule.mem_comap] at hr
    have h := hr U (𝟙 U)
    rw [rawRestriction_id X d U p, LinearMap.id_apply] at h
    exact h
  · intro r hr
    simp only [restrictionStableAnalyticKernel, Submodule.mem_iInf, Submodule.mem_comap]
    intro V i
    apply (mem_chartEvaluationKernel_iff X d V p _).2
    intro z y hy
    rw [chartRawEvaluation_rawRestriction X d i z p r hy]
    exact (mem_chartEvaluationKernel_iff X d U p r).1 hr z y
      ⟨hy.1, leOfHom i.unop hy.2⟩

/-- A holomorphic form whose sheafification vanishes was already zero as a
presheaf section. The argument uses local equality and actual chart evaluation. -/
theorem holomorphicDeRham_toSheafify_eq_zero
    (U : Opens (TopCat.of (ComplexPoint X))) (p : ℕ)
    (ω : HolomorphicForm X d (.op U) p)
    (hω : (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)).app (.op U) ω = 0) : ω = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let P := holomorphicDeRhamPresheaf X d p
  let η := toSheafify J P
  have hcover := Presheaf.equalizerSieve_mem J η ω 0 (by simpa using hω)
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d (.op U) p) ω
  change Submodule.Quotient.mk r = 0
  rw [Submodule.Quotient.mk_eq_zero, holomorphicFormRelations_eq_chartEvaluationKernel]
  apply (mem_chartEvaluationKernel_iff X d (.op U) p r).2
  intro z y hy
  obtain ⟨V, i, hi, hyV⟩ := hcover
    ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y) hy.2
  have hlocal :
      (holomorphicFormRelations X d (.op V) p).mkQ (rawRestriction X d i.op p r) = 0 := by
    change P.map i.op ((holomorphicFormRelations X d (.op U) p).mkQ r) = P.map i.op 0 at hi
    rw [map_zero] at hi
    change holomorphicFormRestriction X d i.op p
      ((holomorphicFormRelations X d (.op U) p).mkQ r) = 0 at hi
    exact hi
  have hrel : rawRestriction X d i.op p r ∈ chartEvaluationKernel X d (.op V) p := by
    change Submodule.Quotient.mk (rawRestriction X d i.op p r) = 0 at hlocal
    rwa [Submodule.Quotient.mk_eq_zero, holomorphicFormRelations_eq_chartEvaluationKernel] at hlocal
  have hy' : y ∈ chartSectionDomain X d (.op V) z := ⟨hy.1, hyV⟩
  have heval := (mem_chartEvaluationKernel_iff X d (.op V) p _).1 hrel z y hy'
  rwa [chartRawEvaluation_rawRestriction X d i.op z p r hy'] at heval

/-- Sheafification of the actual holomorphic de Rham presheaf is injective on
sections over every analytic open and in every form degree. -/
theorem holomorphicDeRham_toSheafify_injective
    (U : Opens (TopCat.of (ComplexPoint X))) (p : ℕ) :
    Function.Injective ((toSheafify
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (.op U)) := by
  intro ω ω' h
  apply sub_eq_zero.mp
  apply holomorphicDeRham_toSheafify_eq_zero X d U p (ω - ω')
  rw [map_sub, h, sub_self]

/-- A nonzero analytic form remains nonzero in the actual holomorphic de Rham sheaf. -/
theorem holomorphicDeRham_toSheafify_ne_zero
    (U : Opens (TopCat.of (ComplexPoint X))) (p : ℕ)
    {ω : HolomorphicForm X d (.op U) p} (hω : ω ≠ 0) :
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)).app (.op U) ω ≠ 0 :=
  fun h => hω (holomorphicDeRham_toSheafify_eq_zero X d U p ω h)

end AlgebraicGeometry.ComplexPoint
