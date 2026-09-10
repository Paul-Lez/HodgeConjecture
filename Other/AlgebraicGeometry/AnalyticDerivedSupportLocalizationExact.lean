/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticDerivedSupportLocalizationBoundary
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Exactness of analytic derived-support localization

The localization boundary constructed from the fixed injective model vanishes
precisely on classes which extend from the whole analytic space.  This is the
elementwise exactness statement needed to prove that a punctured normal
coordinate gives a nonzero supported class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ)))
  (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsStrictlyGE 0]

local instance analyticDerivedSupportLocalizationExactSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance analyticDerivedSupportLocalizationExactGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- Elementwise exactness of the derived-support localization boundary: an
open-complement class has zero boundary exactly when it is the restriction of
a class on the whole space. -/
theorem analyticDerivedSupportLocalizationBoundary_eq_zero_iff
    (Z : Closeds (TopCat.of (ComplexPoint X))) (n : ℤ)
    (a : (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) (⊤ ⊓ Z.compl)).mapHomologicalComplex (.up ℤ)).obj
        (globalHypercohomologyInjectiveComplex X K)).homology (n - 1)) :
    analyticDerivedSupportLocalizationBoundary X K Z n a = 0 ↔
      ∃ b : (((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex (.up ℤ)).obj
          (globalHypercohomologyInjectiveComplex X K)).homology (n - 1),
        HomologicalComplex.homologyMap
          (analyticDerivedComplementRestriction X K Z) (n - 1) b = a := by
  let r := analyticDerivedComplementRestriction X K Z
  let T := CochainComplex.mappingCone.triangle r
  let eCone := TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone
    (TopCat.of (ComplexPoint X)) Z.compl ⊤
    (globalHypercohomologyInjectiveComplex X K)
    (fun _ ↦ TopCat.Sheaf.injective_isFlasque _ _) n
  let eSupport := analyticDerivedSupportIsoInjectiveHomology X K Z n
  have hExact := CochainComplex.homologyMap_exact₂_of_distTriang T
    (DerivedCategory.mappingCone_triangle_distinguished r) (n - 1)
  have hFunctionExact : Function.Exact
      (HomologicalComplex.homologyMap T.mor₁ (n - 1))
      (HomologicalComplex.homologyMap T.mor₂ (n - 1)) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp hExact
  constructor
  · intro h
    have h₁ := congrArg (fun x ↦ eSupport.hom x) h
    have h₂ := congrArg (fun x ↦ eCone.hom x) h₁
    have hker : HomologicalComplex.homologyMap T.mor₂ (n - 1) a = 0 := by
      simpa [analyticDerivedSupportLocalizationBoundary, T, eCone, eSupport,
        Function.comp_def] using h₂
    have ha := (hFunctionExact a).mp hker
    rcases ha with ⟨b, hb⟩
    exact ⟨b, by simpa [T, r] using hb⟩
  · rintro ⟨b, rfl⟩
    have hraw :
        (HomologicalComplex.homologyMap T.mor₂ (n - 1))
          ((HomologicalComplex.homologyMap T.mor₁ (n - 1)) b) = 0 :=
      Function.Exact.apply_apply_eq_zero hFunctionExact b
    change eSupport.inv
      (eCone.inv
        ((HomologicalComplex.homologyMap T.mor₂ (n - 1))
          ((HomologicalComplex.homologyMap T.mor₁ (n - 1)) b))) = 0
    rw [hraw]
    simp

end AlgebraicGeometry.ComplexPoint
