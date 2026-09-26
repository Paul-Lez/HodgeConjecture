/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.HomComplexPostcompNaturalityLemmas
public import Other.AlgebraicGeometry.Cohomology.SupportHypercohomologyLemmas

/-! # Naturality of the hypercohomology/global-sections comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

variable (Y : TopCat.{0})

local instance derivedGlobalSectionsHasDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat Y)

/-- Let `Y` be a topological space, `K` a K-injective complex of sheaves of abelian groups on `Y`,
and `n` an integer. This is the additive equivalence `Hom_D(ℤ[0], K[n]) ≃ H^n(Γ(Y, K))`. It
evaluates morphisms from the constant integer sheaf at the section `1`. -/
def derivedHomAddEquivGlobalSectionsKInjective
    (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ) [K.IsKInjective] (n : ℤ) :
    ShiftedHom
      (DerivedCategory.Q.obj (integerConstantSingleComplex Y)) (DerivedCategory.Q.obj K) n ≃+
    (globalSectionsComplex AddCommGrpCat Y K).homology n :=
  (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass _ K n).trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ K n).symm.trans
      (HomologicalComplex.homologyMapIso
        (homComplexSingleIntegerIsoGlobalSections Y K) n).addCommGroupIsoToAddEquiv)

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyNaturalitySheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Let `X` be a scheme over `ℂ`, `K` a K-injective complex of sheaves of abelian groups on its
analytic space, and `n` an integer. This additive equivalence identifies hypercohomology
`ℍ^n(X(ℂ); K)` with the degree-`n` cohomology of the complex of global sections `Γ(X(ℂ), K)`. -/
def hypercohomologyAddEquivGlobalSectionsKInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ) :
    -- `ℍ^n(X(ℂ); K) ≅ H^n(Γ(X(ℂ), K))`.
    ℍ^n(X; K) ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X)) K).homology n :=
  (hypercohomologyAddEquivDerived X K n).trans
    ((isoHomCongrAddEquiv
      (DerivedCategory.Q.mapIso (constantIntegerSheafComplexIntIsoSingle X))
      (Iso.refl _)).trans
      (TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective
        (TopCat.of (ComplexPoint X)) K n))

end AlgebraicGeometry.ComplexPoint
