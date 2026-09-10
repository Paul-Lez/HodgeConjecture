/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import Other.AlgebraicTopology.DerivedSheafSupportTruncation
public import Other.AlgebraicTopology.DerivedSheafSupportForget

/-!
# Filtered de Rham cohomology with closed support

This file packages the existing Hodge-filtered and full holomorphic de Rham
complexes as bounded-below derived objects and applies the genuine derived
closed-support functor to them.  It supplies the maps that a filtered Thom or
purity theorem must use: filtration inclusion, enlargement of support, and
forgetting support.

No purity or Thom-class assertion is made here.  In particular, constructing a
class in `SupportedFilteredDeRhamHypercohomology` and comparing it with the
normalized rational supported coclass remains geometric input.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance filteredDerivedSupportSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance filteredDerivedSupportGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- Termwise lower boundedness gives the homological lower bound required by
the bounded-below derived-support constructor. -/
theorem hodgeFilteredDeRhamComplex_isGE (p : ℤ) :
    (hodgeFilteredDeRhamComplex X p).IsGE p := by
  letI : (hodgeFilteredDeRhamComplex X p).IsStrictlyGE p := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact HomologicalComplex.ExactAt.of_isZero
    ((hodgeFilteredDeRhamComplex X p).isZero_of_isStrictlyGE p i hi)

/-- The full holomorphic de Rham complex is homologically bounded below in
degree zero. -/
theorem holomorphicDeRhamComplexInt_isGE :
    (holomorphicDeRhamComplexInt X).IsGE 0 := by
  letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
    unfold holomorphicDeRhamComplexInt
    infer_instance
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact HomologicalComplex.ExactAt.of_isZero
    ((holomorphicDeRhamComplexInt X).isZero_of_isStrictlyGE 0 i hi)

/-- The filtered holomorphic de Rham complex as an actual bounded-below
derived object. -/
def hodgeFilteredDeRhamPlusObject (p : ℤ) :
    DerivedCategory.Plus (AnalyticAdditiveSheaf X) := by
  letI : (hodgeFilteredDeRhamComplex X p).IsGE p :=
    hodgeFilteredDeRhamComplex_isGE X p
  exact TopCat.Sheaf.supportCoefficientPlus
    (TopCat.of (ComplexPoint X)) (hodgeFilteredDeRhamComplex X p) p

/-- The full holomorphic de Rham complex as an actual bounded-below derived
object. -/
def holomorphicDeRhamPlusObject :
    DerivedCategory.Plus (AnalyticAdditiveSheaf X) := by
  letI : (holomorphicDeRhamComplexInt X).IsGE 0 :=
    holomorphicDeRhamComplexInt_isGE X
  exact TopCat.Sheaf.supportCoefficientPlus
    (TopCat.of (ComplexPoint X)) (holomorphicDeRhamComplexInt X) 0

/-- Filtration inclusion in the bounded-below derived category. -/
def hodgeFilteredDeRhamPlusInclusion (p : ℤ) :
    hodgeFilteredDeRhamPlusObject X p ⟶ holomorphicDeRhamPlusObject X :=
  DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map (hodgeFilteredDeRhamInclusion X p))

/-- Closed-supported hypercohomology of the Hodge-filtered de Rham complex. -/
def SupportedFilteredDeRhamHypercohomology
    (Z : Closeds (ComplexPoint X)) (p n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj
        (hodgeFilteredDeRhamPlusObject X p))

/-- Closed-supported hypercohomology of the full holomorphic de Rham complex. -/
def SupportedDeRhamHypercohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj
        (holomorphicDeRhamPlusObject X))

/-- The map from filtered to full de Rham hypercohomology with a fixed closed
support. -/
def supportedFilteredToDeRhamCohomology
    (Z : Closeds (ComplexPoint X)) (p n : ℤ) :
    SupportedFilteredDeRhamHypercohomology X Z p n ⟶
      SupportedDeRhamHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (hodgeFilteredDeRhamPlusInclusion X p))

/-- Enlarge the closed support of a filtered de Rham class. -/
def supportedFilteredDeRhamSupportMap
    {Z W : Closeds (ComplexPoint X)} (h : Z ≤ W) (p n : ℤ) :
    SupportedFilteredDeRhamHypercohomology X Z p n ⟶
      SupportedFilteredDeRhamHypercohomology X W p n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSectionsMap
      (TopCat.of (ComplexPoint X)) h).app
        (hodgeFilteredDeRhamPlusObject X p))

/-- Enlarge the closed support of a full de Rham class. -/
def supportedDeRhamSupportMap
    {Z W : Closeds (ComplexPoint X)} (h : Z ≤ W) (n : ℤ) :
    SupportedDeRhamHypercohomology X Z n ⟶
      SupportedDeRhamHypercohomology X W n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSectionsMap
      (TopCat.of (ComplexPoint X)) h).app
        (holomorphicDeRhamPlusObject X))

/-- Derived global hypercohomology of the filtered de Rham complex.  A later
comparison identifies this presentation with the project's Ext-valued
`FilteredDeRhamHypercohomology`. -/
def DerivedGlobalFilteredDeRhamHypercohomology (p n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).obj
        (hodgeFilteredDeRhamPlusObject X p))

/-- Derived global hypercohomology of the full de Rham complex. -/
def DerivedGlobalDeRhamHypercohomology (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).obj
        (holomorphicDeRhamPlusObject X))

/-- Forget support on a filtered de Rham class. -/
def supportedFilteredDeRhamForgetSupport
    (Z : Closeds (ComplexPoint X)) (p n : ℤ) :
    SupportedFilteredDeRhamHypercohomology X Z p n ⟶
      DerivedGlobalFilteredDeRhamHypercohomology X p n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedForgetClosedSupport
      (TopCat.of (ComplexPoint X)) Z).app
        (hodgeFilteredDeRhamPlusObject X p))

/-- Forget support on a full de Rham class. -/
def supportedDeRhamForgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedDeRhamHypercohomology X Z n ⟶
      DerivedGlobalDeRhamHypercohomology X n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedForgetClosedSupport
      (TopCat.of (ComplexPoint X)) Z).app
        (holomorphicDeRhamPlusObject X))

/-- Filtration inclusion commutes with enlargement of closed support. -/
@[reassoc]
theorem supportedFilteredToDeRhamCohomology_naturality
    {Z W : Closeds (ComplexPoint X)} (h : Z ≤ W) (p n : ℤ) :
    supportedFilteredDeRhamSupportMap X h p n ≫
        supportedFilteredToDeRhamCohomology X W p n =
      supportedFilteredToDeRhamCohomology X Z p n ≫
        supportedDeRhamSupportMap X h n := by
  unfold supportedFilteredDeRhamSupportMap
    supportedFilteredToDeRhamCohomology supportedDeRhamSupportMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun f => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map f)
    ((TopCat.Sheaf.derivedClosedSupportSectionsMap
      (TopCat.of (ComplexPoint X)) h).naturality
        (hodgeFilteredDeRhamPlusInclusion X p)).symm

/-- Filtration inclusion commutes with forgetting closed support. -/
@[reassoc]
theorem supportedFilteredToDeRhamCohomology_forgetSupport
    (Z : Closeds (ComplexPoint X)) (p n : ℤ) :
    supportedFilteredToDeRhamCohomology X Z p n ≫
        supportedDeRhamForgetSupport X Z n =
      supportedFilteredDeRhamForgetSupport X Z p n ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
          ((TopCat.Sheaf.derivedGlobalSections
            (TopCat.of (ComplexPoint X))).map
              (hodgeFilteredDeRhamPlusInclusion X p)) := by
  unfold supportedFilteredToDeRhamCohomology
    supportedDeRhamForgetSupport supportedFilteredDeRhamForgetSupport
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun f => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map f)
    ((TopCat.Sheaf.derivedForgetClosedSupport
      (TopCat.of (ComplexPoint X)) Z).naturality
        (hodgeFilteredDeRhamPlusInclusion X p))

end AlgebraicGeometry.ComplexPoint
