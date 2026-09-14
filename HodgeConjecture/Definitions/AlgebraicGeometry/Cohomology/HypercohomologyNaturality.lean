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

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyNaturalitySheafDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X))) :=
  HasDerivedCategory.standard (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X)))

/-- On a K-injective sheaf complex, derived morphisms from the integer
constant sheaf are computed by actual global sections, with no further
replacement complex. -/
def derivedHomAddEquivGlobalSectionsKInjective
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X))) ℤ)
    [K.IsKInjective] (n : ℤ) :
    ShiftedHom
      (DerivedCategory.Q.obj (TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (Point ℂ X)))) (DerivedCategory.Q.obj K) n ≃+
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (Point ℂ X)) K).homology n :=
  (kInjectiveDerivedHomAddEquivCohomologyClass _ K n).trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ K n).symm.trans
      (HomologicalComplex.homologyMapIso
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
          (TopCat.of (Point ℂ X)) K) n).addCommGroupIsoToAddEquiv)

/-- Hypercohomology of an actual K-injective complex is its global-section
cohomology. This direct form exposes naturality without choosing another
injective resolution. -/
def hypercohomologyAddEquivGlobalSectionsKInjective
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X))) ℤ)
    [K.IsKInjective] (n : ℤ) :
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (Point ℂ X)) K).homology n :=
  (hypercohomologyAddEquivDerived X K n).trans
    ((isoHomCongrAddEquiv
      (DerivedCategory.Q.mapIso (constantIntegerSheafComplexIntIsoSingle X))
      (Iso.refl _)).trans
      (derivedHomAddEquivGlobalSectionsKInjective X K n))

end AlgebraicGeometry.ComplexPoint
