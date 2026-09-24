/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernComponentSheafIsolation
public import Other.AlgebraicGeometry.ChernComponentSectionExtraction
public import Other.AlgebraicGeometry.ChernComponentNormalizationRestriction
public import Other.AlgebraicGeometry.ChernRelativeCanonicalLift
public import Other.AlgebraicGeometry.CartierWindingChartCoefficient

@[expose] public noncomputable section
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance recoveryTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

namespace ChernWindingChart

variable {c : Scheme.CartierData X.left} {x : X.left} {d : ℕ}
  [SmoothOfRelativeDimension d X.hom] {q : ComplexPoint X}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original local supported-class formula determines the component multiplicity. -/
theorem normalizedClass_restrict_eq_divisor_smul_of_original
    (ch : ChernWindingChart X c x d 1 q)
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    {s : Finset X.left} (hxS : x ∈ s)
    (hco : ∀ y ∈ s, coheight y = ((1 : ℕ) : ℕ∞))
    (hdiv : ∀ y ∈ s, c.divisor y ≠ 0)
    (b : SupportedInjectiveHomology X (componentsAnalyticClosedSupport X s) (2 : ℤ))
    (γ : ∀ y : X.left,
      SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X y) (2 : ℤ))
    (hγ : b = ∑ y ∈ s, componentContribution X s y (2 : ℤ) (γ y))
    (hbad : componentsAnalyticClosedSupport X s ≤ analyticClosedSupport X (badLocus c))
    (βbad : SupportedInjectiveHomology X (analyticClosedSupport X (badLocus c)) (2 : ℤ))
    (hβ : enlargeSupportedInjectiveHomology X hbad (2 : ℤ) b = βbad)
    (horig : supportedInjectiveLocalSection ch.carrier (2 : ℤ) βbad =
      (HomologicalComplex.homologyMap
        (supportedInjectiveComplexMap X
          (show cycleComponentAnalyticClosedSupport X x ≤
              analyticClosedSupport X (badLocus c) from
            fun _ hy => closure_subset_badLocus c x (hdiv x hxS) hy))
        (2 : ℤ)).hom.app (op ch.carrier)
        ((complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) 2).inv.hom.app (op ch.carrier)
          (ch.winding ch.cartierUnit)))
    (hb : ch.HasTrivialUnitWinding) (hc : ch.NormalizesCoclass hx) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE ch.le).op
      ((cycleComponentSupportedClassNormalizationIso X x hx).hom (γ x)) =
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE ch.le).op
        ((c.divisor x) • cycleComponentSmoothSupportCoclassSection X x hx) := by
  let hST : cycleComponentAnalyticClosedSupport X x ≤
      componentsAnalyticClosedSupport X s :=
    cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X hxS
  let hTB : componentsAnalyticClosedSupport X s ≤
      analyticClosedSupport X (badLocus c) := hbad
  let hSB : cycleComponentAnalyticClosedSupport X x ≤
      analyticClosedSupport X (badLocus c) := hST.trans hTB
  have hloc := ChernWindingChart.carrier_localSection_eq_component_of_componentContribution_sum
    (X := X) ch hx hxS hco hdiv b γ hγ
  have henlarge := supportedInjectiveLocalSection_enlarge (X := X) hTB ch.carrier
    (2 : ℤ) b
  have hmapcomp :
      supportedInjectiveComplexMap X hST ≫ supportedInjectiveComplexMap X hTB =
        supportedInjectiveComplexMap X hSB := by
    ext n
    exact NatTrans.congr_app
      (TopCat.Sheaf.sheafSectionsSupportedOutsideMap_comp
        (TopCat.of (ComplexPoint X))
        (show (componentsAnalyticClosedSupport X s).compl ≤
            (cycleComponentAnalyticClosedSupport X x).compl from
          fun _ hz hy => hz (hST hy))
        (show (analyticClosedSupport X (badLocus c)).compl ≤
            (componentsAnalyticClosedSupport X s).compl from
          fun _ hz hy => hz (hbad hy)))
      ((ambientRationalInjectiveComplex X).X n)
  have hhomcomp :
      (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ)).hom.app
          (op ch.carrier) ≫
        (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hTB) (2 : ℤ)).hom.app
          (op ch.carrier) =
      (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hSB) (2 : ℤ)).hom.app
          (op ch.carrier) := by
    have hnat :
        HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ) ≫
            HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hTB) (2 : ℤ) =
          HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hSB) (2 : ℤ) := by
      rw [← HomologicalComplex.homologyMap_comp, hmapcomp]
    exact congrArg (fun f => f.hom.app (op ch.carrier)) hnat
  have hleft : supportedInjectiveLocalSection ch.carrier (2 : ℤ) βbad =
      (HomologicalComplex.homologyMap
        (supportedInjectiveComplexMap X hSB) (2 : ℤ)).hom.app (op ch.carrier)
        (supportedInjectiveLocalSection ch.carrier (2 : ℤ) (γ x)) := by
    rw [← hβ, henlarge, hloc]
    rw [← ConcreteCategory.comp_apply, hhomcomp]
  have hmapiso : IsIso ((HomologicalComplex.homologyMap
      (supportedInjectiveComplexMap X hSB) (2 : ℤ)).hom.app (op ch.carrier)) := by
    exact supportedInjectiveHomologySheafMap_app_isIso (X := X) hSB ch.carrier
      (by simpa only [ChernWindingChart.punctured] using ch.punctured_le_goodComplement) (2 : ℤ)
  have hsection : supportedInjectiveLocalSection ch.carrier (2 : ℤ) (γ x) =
      (complexSupportInjectiveCohomologySheafIsoRelative X
        (cycleComponentAnalyticClosedSupport X x) 2).inv.hom.app (op ch.carrier)
        (ch.winding ch.cartierUnit) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((HomologicalComplex.homologyMap
        (supportedInjectiveComplexMap X hSB) (2 : ℤ)).hom.app (op ch.carrier))).1
    rw [← hleft, horig]
  rw [normalizedComponentSection_restrict (X := X) hx (γ x) (ch.le)]
  rw [hsection]
  rw [← ConcreteCategory.comp_apply]
  have hi :
      (ConcreteCategory.hom
        ((complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) 2).inv.hom.app (op ch.carrier) ≫
          (complexSupportInjectiveCohomologySheafIsoRelative X
            (cycleComponentAnalyticClosedSupport X x) 2).hom.hom.app (op ch.carrier)))
        (ch.winding ch.cartierUnit) = ch.winding ch.cartierUnit := by
    let e := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ch.carrier).mapIso
      (complexSupportInjectiveCohomologySheafIsoRelative X
        (cycleComponentAnalyticClosedSupport X x) 2)
    exact e.addCommGroupIsoToAddEquiv.apply_symm_apply (ch.winding ch.cartierUnit)
  rw [hi]
  have hz := map_zsmul
    (ConcreteCategory.hom ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE ch.le).op))
    (c.divisor x) (cycleComponentSmoothSupportCoclassSection X x hx)
  exact (ch.cartierUnit_winding_eq_divisor_smul_coclass hx hb hc).trans hz.symm

end ChernWindingChart

end AlgebraicGeometry.ComplexPoint
