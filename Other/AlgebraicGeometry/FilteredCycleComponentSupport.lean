/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentSheafClass
public import Other.AlgebraicGeometry.DerivedSupportRationalForget
public import Other.AlgebraicGeometry.FilteredDerivedSupport

/-!
# Cycle-component classes in supported de Rham cohomology

This file sends the already normalized rational class with support to actual
derived de Rham cohomology with the same support.  It also proves that both
coefficient comparison and the Hodge-filtration inclusion commute with
forgetting support.

Consequently, the remaining geometric construction for an algebraic component
can be made entirely with support: it is enough to lift the concrete class
`cycleComponentSupportedDeRhamClass` through
`supportedFilteredToDeRhamCohomology`.  No choice of a representative in the
ordinary cohomology group, and no injectivity assertion for forgetting support,
is involved in that target.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance filteredCycleSupportSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance filteredCycleSupportGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- Rational constants map to the holomorphic de Rham complex as a morphism in
the bounded-below derived category.  The source is the same canonical
degree-zero object used by `derivedRationalSupportAddEquiv`. -/
def rationalToHolomorphicDeRhamPlus :
    (DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constantFieldSheaf ℚ X) ⟶
      holomorphicDeRhamPlusObject X :=
  DerivedCategory.Plus.ι.preimage
    ((DerivedCategory.singleFunctorIsoCompQ (AnalyticAdditiveSheaf X) 0).hom.app _ ≫
      DerivedCategory.Q.map (constantRationalSheafComplexIntIsoSingleZero X).inv ≫
      DerivedCategory.Q.map (fieldToHolomorphicDeRhamComplexInt ℚ X))

/-- Coefficient comparison after applying actual derived sections with a fixed
closed support. -/
def derivedRationalToSupportedDeRhamCohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
        ((TopCat.Sheaf.derivedClosedSupportSections
          (TopCat.of (ComplexPoint X)) Z).obj
            ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
              (constantFieldSheaf ℚ X))) ⟶
      SupportedDeRhamHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (rationalToHolomorphicDeRhamPlus X))

/-- Coefficient comparison after applying actual derived global sections. -/
def derivedRationalToGlobalDeRhamCohomology (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).obj
            ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
              (constantFieldSheaf ℚ X))) ⟶
      DerivedGlobalDeRhamHypercohomology X n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).map
        (rationalToHolomorphicDeRhamPlus X))

/-- Forget support on derived rational cohomology, before applying any
coefficient comparison. -/
def derivedRationalForgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
        ((TopCat.Sheaf.derivedClosedSupportSections
          (TopCat.of (ComplexPoint X)) Z).obj
            ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
              (constantFieldSheaf ℚ X))) ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).obj
            ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
              (constantFieldSheaf ℚ X))) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedForgetClosedSupport
      (TopCat.of (ComplexPoint X)) Z).app
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X)))

/-- The rational-to-de Rham coefficient map commutes with forgetting closed
support at the level of the actual derived functors. -/
@[reassoc]
theorem derivedRationalToDeRhamCohomology_forgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    derivedRationalToSupportedDeRhamCohomology X Z n ≫
        supportedDeRhamForgetSupport X Z n =
      derivedRationalForgetSupport X Z n ≫
        derivedRationalToGlobalDeRhamCohomology X n := by
  unfold derivedRationalToSupportedDeRhamCohomology
    supportedDeRhamForgetSupport derivedRationalForgetSupport
    derivedRationalToGlobalDeRhamCohomology
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun f => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map f)
    ((TopCat.Sheaf.derivedForgetClosedSupport
      (TopCat.of (ComplexPoint X)) Z).naturality
        (rationalToHolomorphicDeRhamPlus X))

/-- The normalized rational support class, now viewed in full holomorphic de
Rham cohomology with the same support. -/
def rationalSupportedToDeRhamCohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    RationalCohomologyWithSupport X Z n →+
      SupportedDeRhamHypercohomology X Z n :=
  (derivedRationalToSupportedDeRhamCohomology X Z n).hom.comp
    (derivedRationalSupportAddEquiv X Z n).symm.toAddMonoidHom

/-- Forgetting support after supported coefficient comparison is the same as
first using the repository's sign-correct rational `forgetSupport` and then
applying the derived global coefficient comparison. -/
theorem rationalSupportedToDeRhamCohomology_forgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : RationalCohomologyWithSupport X Z n) :
    supportedDeRhamForgetSupport X Z n
        (rationalSupportedToDeRhamCohomology X Z n a) =
      derivedRationalToGlobalDeRhamCohomology X n
        ((derivedRationalCohomologyAddEquiv X n).symm
          (forgetSupport X Z n a)) := by
  let x := (derivedRationalSupportAddEquiv X Z n).symm a
  have hx : derivedRationalForgetSupport X Z n x =
      (derivedRationalCohomologyAddEquiv X n).symm
        (forgetSupport X Z n a) := by
    apply (derivedRationalCohomologyAddEquiv X n).injective
    rw [AddEquiv.apply_symm_apply]
    simpa only [derivedRationalForgetSupport, x,
      AddEquiv.apply_symm_apply] using
        derivedRationalSupportAddEquiv_forgetSupport X Z n x
  change supportedDeRhamForgetSupport X Z n
      (derivedRationalToSupportedDeRhamCohomology X Z n x) = _
  rw [← ConcreteCategory.comp_apply,
    derivedRationalToDeRhamCohomology_forgetSupport]
  change derivedRationalToGlobalDeRhamCohomology X n
      (derivedRationalForgetSupport X Z n x) = _
  rw [hx]

/-- The supported Hodge filtration: classes represented by the filtered de
Rham complex before support is forgotten. -/
def supportedHodgeFiltration
    (Z : Closeds (ComplexPoint X)) (p n : ℤ) :
    AddSubgroup (SupportedDeRhamHypercohomology X Z n) :=
  (supportedFilteredToDeRhamCohomology X Z p n).hom.range

/-- A supported filtered class remains filtered after support is forgotten.
This is the kernel-clean passage from a local Thom construction to the global
derived de Rham group. -/
theorem supportedHodgeFiltration_forgetSupport
    (Z : Closeds (ComplexPoint X)) (p n : ℤ)
    {a : SupportedDeRhamHypercohomology X Z n}
    (ha : a ∈ supportedHodgeFiltration X Z p n) :
    supportedDeRhamForgetSupport X Z n a ∈
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (hodgeFilteredDeRhamPlusInclusion X p))).hom.range := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨supportedFilteredDeRhamForgetSupport X Z p n b, ?_⟩
  exact (ConcreteCategory.congr_hom
    (supportedFilteredToDeRhamCohomology_forgetSupport X Z p n) b).symm

variable [IsProjective X.hom]
  (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
  (hx : Order.coheight x = p)

/-- The concrete normalized component class in supported full de Rham
cohomology. -/
def cycleComponentSupportedDeRhamClass :
    SupportedDeRhamHypercohomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * (p : ℤ)) :=
  rationalSupportedToDeRhamCohomology X
    (cycleComponentAnalyticClosedSupport X x) (2 * (p : ℤ))
      (cycleComponentSheafSupportedClass X x (d := d) hx)

/-- The exact remaining supported lifting target for a component.  Any lift
immediately gives a filtered class after forgetting support. -/
theorem cycleComponentSupportedDeRhamClass_forget_mem_globalFilteredRange
    (h : cycleComponentSupportedDeRhamClass X x (d := d) hx ∈
      supportedHodgeFiltration X (cycleComponentAnalyticClosedSupport X x)
        (p : ℤ) (2 * (p : ℤ))) :
    supportedDeRhamForgetSupport X (cycleComponentAnalyticClosedSupport X x)
        (2 * (p : ℤ))
        (cycleComponentSupportedDeRhamClass X x (d := d) hx) ∈
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat (2 * (p : ℤ))).map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (hodgeFilteredDeRhamPlusInclusion X (p : ℤ)))).hom.range :=
  supportedHodgeFiltration_forgetSupport X
    (cycleComponentAnalyticClosedSupport X x) (p : ℤ) (2 * (p : ℤ)) h

end AlgebraicGeometry.ComplexPoint
