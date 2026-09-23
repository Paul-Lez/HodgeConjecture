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
public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Cohomology of the analytic space with support in a closed set

`H^n_Z(X(ℂ); K)` is the sheaf cohomology of `X(ℂ)` with support in the closed set `Z` and
coefficients in the constant sheaf `K`. Forgetting the support lands in `H^n(X(ℂ); K)`. With
rational coefficients the group is computed by the sections supported in `Z` of the sheafified
singular cochains.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] (X : Over (Spec ↧ℂ))

set_option quotPrecheck false in
/-- `H_[Z]^n(X; K)` is the sheaf cohomology of the analytic space `X(ℂ)` with support in the closed
set `Z ⊆ X(ℂ)` and coefficients in the constant sheaf `K`, in degree `n`. -/
scoped notation:max "H_[" Z "]^" n:max "(" X "; " K ")" =>
  TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) Z
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of K)) n

variable (Z : Closeds (ComplexPoint X))

/-- `H^n_Z(X(ℂ); K) → H^n(X(ℂ); K)`, forgetting the support. -/
def forgetSupport (n : ℕ) : H_[Z]^n(X; K) →+ H^n(X; K) :=
  (Sheaf.H'.addEquivTerminal isTerminalTop _ n).toAddMonoidHom.comp
    (Sheaf.relH.forget _ (homOfLE (le_top : Z.compl ≤ ⊤)) n)

/-- Forgetting the support `X(ℂ)` itself is injective. -/
lemma forgetSupport_injective_of_eq_top (hZ : Z = ⊤) (n : ℕ) :
    Function.Injective (forgetSupport K X Z n) :=
  (Sheaf.H'.addEquivTerminal isTerminalTop _ n).injective.comp
    (TopCat.Sheaf.relH.forget_injective_of_eq_bot (TopCat.of (ComplexPoint X)) _ _
      (by rw [hZ]; ext; simp) n)

section Singular

open AlgebraicTopology.Singular

variable [IsIntegral X.left] [Smooth X.hom]

/-- The augmentation `ℚ[0] → C^•` of the sheafified rational singular cochains on `X(ℂ)`, indexed
by integers. -/
def rationalSingularAugmentation :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint X); ℚ) ⟶
      rationalSingularCochainComplex (TopCat.of (ComplexPoint X)) :=
  (constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫
    HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat

instance rationalSingularAugmentation_mono : Mono (rationalSingularAugmentation X) := by
  dsimp only [rationalSingularAugmentation]
  exact @mono_comp _ _ _ _ _ _ inferInstance _
    (constantsToSingularCochainComplexInt_mono ℚ (TopCat.of (ComplexPoint X)))

instance rationalSingularAugmentation_quasiIso : QuasiIso (rationalSingularAugmentation X) := by
  dsimp only [rationalSingularAugmentation]
  have : QuasiIso (HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr
      (constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
        (exists_contractibleOpen_le X))
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := this)

variable [IsProjective X.hom]

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- `H^n_Z(X(ℂ); ℚ) ≃ H^n(Γ_Z(X(ℂ), C^•))` for the sheafified rational singular cochains `C^•`. -/
def rationalSupportAddEquivSupportedSingularHomology (n : ℕ) :
    H_[Z]^n(X; ℚ) ≃+
      (((TopCat.Sheaf.supportEvaluation ↧(ComplexPoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportSingularComplex X Z)).homology n :=
  letI : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  @TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (ComplexPoint X))
    𝓒(↧(ComplexPoint X); ℚ) (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))
    (rationalSingularCochainComplex_isStrictlyGE _) (rationalSingularAugmentation X)
    (rationalSingularAugmentation_mono X) (rationalSingularAugmentation_quasiIso X)
    Z.compl ⊤ Z.compl (top_inf_eq _)
    (fun n => rationalSingularCochainComplex_isFlasque (TopCat.of (ComplexPoint X)) n)
    (analyticHasExt X) n

end Singular

end AlgebraicGeometry.ComplexPoint

end
