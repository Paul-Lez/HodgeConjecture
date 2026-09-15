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
open scoped TopCat.Sheaf

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
    (globalSectionsComplex AddCommGrpCat Y K).homology n :=
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

local instance hypercohomologyNaturalityAddCommGrpDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard AddCommGrpCat

/-- Hypercohomology of a bounded-below termwise-injective complex is the cohomology of its
complex of global sections. -/
def hypercohomologyAddEquivGlobalSectionsKInjective
    (K : CochainComplex.Plus (AnalyticAdditiveSheaf X))
    [∀ i, Injective (K.obj.X i)] (n : ℤ) :
    ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj K) ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X)) K.obj).homology n :=
  (TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat
    (TopCat.of (ComplexPoint X)) K n).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.ComplexPoint
