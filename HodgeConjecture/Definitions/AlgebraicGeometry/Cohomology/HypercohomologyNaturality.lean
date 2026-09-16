/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.HomComplexPostcompNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportHypercohomology

/-! # Naturality of the hypercohomology/global-sections comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

variable (Y : TopCat.{0})

local instance derivedGlobalSectionsHasDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat Y)

/-- On a K-injective sheaf complex, derived morphisms from the integer
constant sheaf are computed by actual global sections, with no further
replacement complex. -/
def derivedHomAddEquivGlobalSectionsKInjective
    (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ) [K.IsKInjective] (n : ℤ) :
    ShiftedHom
      (DerivedCategory.Q.obj (integerConstantSingleComplex Y)) (DerivedCategory.Q.obj K) n ≃+
    (globalSectionsComplexInt Y K).homology n :=
  (AlgebraicGeometry.ComplexPoint.kInjectiveDerivedHomAddEquivCohomologyClass _ K n).trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ K n).symm.trans
      (HomologicalComplex.homologyMapIso
        (homComplexSingleIntegerIsoGlobalSections Y K) n).addCommGroupIsoToAddEquiv)

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyNaturalitySheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Hypercohomology of an actual K-injective complex is its global-section
cohomology. This direct form exposes naturality without choosing another
injective resolution. -/
def hypercohomologyAddEquivGlobalSectionsKInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ) :
    -- `ℍ^n(X(ℂ); K) ≅ H^n(Γ(X(ℂ), K))`.
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) K).homology n :=
  (hypercohomologyAddEquivDerived X K n).trans
    ((isoHomCongrAddEquiv
      (DerivedCategory.Q.mapIso (constantIntegerSheafComplexIntIsoSingle X))
      (Iso.refl _)).trans
      (TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective
        (TopCat.of (ComplexPoint X)) K n))

end AlgebraicGeometry.ComplexPoint
