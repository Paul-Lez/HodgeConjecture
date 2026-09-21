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

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Cohomology of the analytic space with support in a closed set

`H^n_Z(X(ℂ); K)` is the sheaf cohomology of `X(ℂ)` with support in the closed set `Z` and
coefficients in the constant sheaf `K`. Forgetting the support lands in `H^n(X(ℂ); K)`. With
rational coefficients the group is computed by the sections supported in `Z` of the chosen
injective resolution of `ℚ`.
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

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- `H^n_Z(X(ℂ); ℚ) ≃ H^n(Γ_Z(X(ℂ), I))` for the chosen injective resolution `ℚ → I`. -/
def rationalSupportAddEquivSupportedInjectiveHomology (n : ℕ) :
    H_[Z]^n(X; ℚ) ≃+
      (((TopCat.Sheaf.supportEvaluation ↧(ComplexPoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportInjectiveComplex X Z)).homology n :=
  @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology (TopCat.of (ComplexPoint X)) Z.compl ⊤
    Z.compl (top_inf_eq _) (analyticHasExt X) _ (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n

end AlgebraicGeometry.ComplexPoint

end
