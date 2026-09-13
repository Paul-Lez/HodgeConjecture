/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.HypercohomologyShift

/-! # Support-forgetting in the actual rational injective model -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

instance ambientRationalInjectiveComplex_isKInjective :
    (ambientRationalInjectiveComplex X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- Ordinary rational cohomology computed by the actual ambient rational
injective resolution. This has the ordinary augmentation normalization. -/
def rationalCohomologyAddEquivAmbientInjectiveHomology (n : ℤ) :
    H^n(X; ℚ) ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (ambientRationalInjectiveComplex X)).homology n := by
  let e : H^n(X; ℚ) ≃+
      Hypercohomology X (ambientRationalInjectiveComplex X) n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv
        (ambientRationalInjectiveAugmentation X)
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      map_add' α β := (hypercohomologyMap X
        (ambientRationalInjectiveAugmentation X) n).map_add α β }
  exact e.trans (hypercohomologyAddEquivGlobalSectionsKInjective X _ n)

end AlgebraicGeometry.ComplexPoint
