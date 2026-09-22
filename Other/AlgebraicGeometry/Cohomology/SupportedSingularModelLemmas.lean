/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Other.AlgebraicGeometry.Cohomology.SupportedSingularModel

/-!
# Supported singular models on smooth projective complex varieties

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `Y = X(ℂ)` its analytic topology. This
cochain map sends the sheafified rational singular cochain complex on `Y` to the chosen
injective resolution of the constant rational sheaf. It extends the identity on constant
cochains and uses local contractibility of `Y`. -/
def complexSingularToAmbientInjective :
    rationalSingularCochainComplex (TopCat.of (ComplexPoint X)) ⟶
      ambientRationalInjectiveComplex X :=
  singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X)

instance complexSingularToAmbientInjective_quasiIso :
    QuasiIso (complexSingularToAmbientInjective X) :=
  singularToConstantInjectiveComplex_quasiIso _ _

variable [IsProjective X.hom]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `Y = X(ℂ)` its analytic topology. Assume
also that `X` is projective, and let `U,V ⊆ Y` be open. The comparison from sheafified rational
singular cochains `C` to a constant-sheaf injective resolution `I` induces this isomorphism
`H^n(Γ_{Y \ U}(V,C)) ≅ H^n(Γ_{Y \ U}(V,I))` for every integer `n`. In each complex, sections
over `V` are required to vanish on `V ∩ U`. -/
def complexSupportedSingularInjectiveHomologyIso
    (U V : Opens (ComplexPoint X)) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj
        (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj
        (((TopCat.Sheaf.sheafSectionsSupportedOutside
          (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex ℤᵘᵖ).obj
            (ambientRationalInjectiveComplex X)))).homology n :=
  letI : ∀ W : Opens (ComplexPoint X), ParacompactSpace W :=
    openParacompactSpace X
  supportedSingularInjectiveHomologyIso (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X) U V n

end AlgebraicGeometry.ComplexPoint

end
