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
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyFlasqueModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedInjectiveModel
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Cohomology of the analytic space with support in a closed set

`H^n_Z(X(ℂ); K)` is the sheaf cohomology of `X(ℂ)` with support in the closed set `Z` and
coefficients in the constant sheaf `K`. Forgetting the support lands in `H^n(X(ℂ); K)`. With
rational coefficients it is compared with the sheafified relative singular cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] (X : Over (Spec ↧ℂ))

local instance withSupportAnalyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance withSupportAdditiveGroupsHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

set_option quotPrecheck false in
/-- `H_[Z]^n(X; K)` is the sheaf cohomology of the analytic space `X(ℂ)` with support in the closed
set `Z ⊆ X(ℂ)` and coefficients in the constant sheaf `K`, in degree `n`. -/
scoped notation:max "H_[" Z "]^" n:max "(" X "; " K ")" =>
  TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) Z
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of K)) n

variable (Z : Closeds (ComplexPoint X))

/-- The supported-section model of the support-forgetting map, before identifying the target with
hypercohomology. -/
def forgetSupportToGlobalSectionsHomology (n : ℕ) :
    H_[Z]^n(X; K) →+
      (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.injectiveResolutionComplex
          (TopCat.of (ComplexPoint X))
          ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
            (AddCommGrpCat.of K)))).homology n := by
  letI Y := TopCat.of (ComplexPoint X)
  letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  letI I := TopCat.Sheaf.injectiveResolutionComplex Y F
  letI S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤ I
  letI e := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y Z.compl ⊤ Z.compl
    (top_inf_eq _) inferInstance F I
    (TopCat.Sheaf.injectiveResolutionComplex_isKInjective Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso Y F) n
  exact (HomologicalComplex.homologyMap S.f n).hom.comp e.toAddMonoidHom

/-- `H_[Z]^n(X(ℂ); K) → H^n(X(ℂ); K)`, forgetting the support. The target is the new
hypercohomology object, reached through the canonical injective-resolution comparison. -/
def forgetSupport (n : ℕ) : H_[Z]^n(X; K) →+ H^n(X; K) :=
  letI Y := TopCat.of (ComplexPoint X)
  letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  letI I := TopCat.Sheaf.injectiveResolutionComplex Y F
  letI IP : CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
    ⟨I, ⟨0, TopCat.Sheaf.injectiveResolutionComplex_isStrictlyGE Y F⟩⟩
  letI : QuasiIso (constantFieldSheafComplexIntIsoSingle K X).hom := by
    letI : IsIso (constantFieldSheafComplexIntIsoSingle K X).hom :=
      (constantFieldSheafComplexIntIsoSingle K X).isIso_hom
    exact quasiIso_of_isIso _
  letI : QuasiIso (TopCat.Sheaf.injectiveResolutionAugmentation Y F) :=
    TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso Y F
  letI (i : ℤ) : Injective (IP.obj.X i) := by
    dsimp [IP]
    exact TopCat.Sheaf.injectiveResolutionComplex_injective Y F i
  letI f : constantFieldSheafComplexIntPlus K X ⟶ IP :=
    ⟨(constantFieldSheafComplexIntIsoSingle K X).hom ≫
      TopCat.Sheaf.injectiveResolutionAugmentation Y F⟩
  letI : QuasiIso f.hom := by
    change QuasiIso ((constantFieldSheafComplexIntIsoSingle K X).hom ≫
      TopCat.Sheaf.injectiveResolutionAugmentation Y F)
    infer_instance
  letI e := TopCat.Sheaf.hypercohomologyIsoOfQuasiIsoToInjective
    AddCommGrpCat Y f n
  (e.addCommGroupIsoToAddEquiv.symm.toAddMonoidHom).comp
    (forgetSupportToGlobalSectionsHomology K X Z n)

/-- Forgetting the support `X(ℂ)` itself is injective. -/
lemma forgetSupport_injective_of_eq_top (hZ : Z = ⊤) (n : ℕ) :
    Function.Injective (forgetSupport K X Z n) := by
  subst Z
  letI Y := TopCat.of (ComplexPoint X)
  letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  letI I := TopCat.Sheaf.injectiveResolutionComplex Y F
  letI U : Opens Y := (⊤ : Closeds (ComplexPoint X)).compl
  letI S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤ I
  letI (i : ℤ) : IsIso (S.f.f i) := by
    dsimp [S, U, TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex,
      TopCat.Sheaf.supportRestrictionComplexShortComplex]
    have hU : (⊤ : Closeds (ComplexPoint X)).compl = (⊥ : Opens Y) := by
      ext
      simp
    rw [hU]
    change IsIso ((TopCat.Sheaf.supportEvaluation Y ⊤).map
      ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y ⊥).app (I.X i)))
    letI : IsIso ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y ⊥).app (I.X i)) := by
      change IsIso (kernel.ι ((TopCat.Sheaf.toOpenRestrictionPushforward Y ⊥).app (I.X i)))
      rw [(TopCat.Sheaf.isZero_openRestrictionPushforward_bot Y (I.X i)).eq_zero_of_tgt
        ((TopCat.Sheaf.toOpenRestrictionPushforward Y ⊥).app (I.X i))]
      infer_instance
    exact Functor.map_isIso _ _
  letI : IsIso S.f := HomologicalComplex.Hom.isIso_of_components S.f
  letI e := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y U ⊤ U
    (top_inf_eq _) inferInstance F I
    (TopCat.Sheaf.injectiveResolutionComplex_isKInjective Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso Y F) n
  have hSupported :
      Function.Injective (forgetSupportToGlobalSectionsHomology K X (⊤ : Closeds (ComplexPoint X)) n) := by
    change Function.Injective ((HomologicalComplex.homologyMap S.f n).hom.comp e.toAddMonoidHom)
    exact ((AddCommGrpCat.mono_iff_injective _).mp inferInstance).comp e.injective
  dsimp [forgetSupport]
  exact (AddEquiv.injective _).comp hSupported

section Rational

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- If the lower relative cohomology sheaves with support in `S` vanish, this identifies
`H_[S]^n(X; ℚ)` with the global sections of `𝓗_[S]^n(X; ℚ)`. -/
def rationalSupportAddEquivSupportedGlobalSheafSection
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero (𝓗_[S]^j(TopCat.of (ComplexPoint X); ℚ))) :
  H_[S]^n(X; ℚ) ≃+
      (𝓗_[S]^n(TopCat.of (ComplexPoint X); ℚ)).presheaf.obj (op ⊤) :=
  rationalSupportAddEquivSupportedRelativeCohomologySheafSection X S n hH

end Rational

end AlgebraicGeometry.ComplexPoint

end
