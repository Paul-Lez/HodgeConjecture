/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization
public import Other.AlgebraicGeometry.ChernComponentSectionExtraction

set_option maxHeartbeats 1000000

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance ccrTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Component normalization commutes with restriction to an open in its smooth locus. -/
theorem normalizedComponentSection_restrict
    {x : X.left} (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (a : SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x) (2 : ℤ))
    {W : Opens (TopCat.of (ComplexPoint X))}
    (hWU : W ≤ cycleComponentSmoothSupportAmbientOpen X x) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE hWU).op
      ((cycleComponentSupportedClassNormalizationIso X x hx).hom a) =
      (complexSupportInjectiveCohomologySheafIsoRelative X
        (cycleComponentAnalyticClosedSupport X x) 2).hom.hom.app (op W)
        (supportedInjectiveLocalSection W (2 : ℤ) a) := by
  rw [cycleComponentSupportedClassNormalizationIso_hom,
    cycleComponentSmoothSupportLowestSectionCohomologyIso]
  change (ConcreteCategory.hom
      ((complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) 2).hom.hom.app
            (op (cycleComponentSmoothSupportAmbientOpen X x)) ≫
        (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
          (↑(cycleComponentAnalyticClosedSupport X x)) 2).obj.map (homOfLE hWU).op))
      ((ConcreteCategory.hom
        (cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom)
        ((ConcreteCategory.hom
          (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
            (2 * (1 : ℤ)))) a)) = _
  have hnat := ConcreteCategory.congr_hom
    ((complexSupportInjectiveCohomologySheafIsoRelative X
      (cycleComponentAnalyticClosedSupport X x) 2).hom.hom.naturality
      (homOfLE hWU).op)
      ((cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom
      ((HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
        (2 * (1 : ℤ))) a))
  have hopen :
      (cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom =
        TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
          (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
          (2 : ℤ) (cycleComponentSmoothSupportAmbientOpen X x) := by
    rw [cycleComponentSmoothSupportLowestSectionCohomologyIso,
      TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom]
    change TopCat.Sheaf.sectionCohomologyToSheafSection _ _ (2 * (1 : ℤ)) _ = _
    rfl
  have hs :
      (ConcreteCategory.hom
        (((complexSupportInjectiveComplex X
          (cycleComponentAnalyticClosedSupport X x)).homology (2 : ℤ)).obj.map
            (homOfLE hWU).op))
        ((ConcreteCategory.hom
          (cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom)
          ((ConcreteCategory.hom
            (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
              (2 * (1 : ℤ)))) a)) =
      supportedInjectiveLocalSection (X := X) W (2 : ℤ) a := by
    let Y := TopCat.of (ComplexPoint X)
    let K := complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)
    let rU := homOfLE (le_top : cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤)
    let rW := homOfLE (le_top : W ≤ ⊤)
    have hr := congrArg (fun f => HomologicalComplex.homologyMap f (2 : ℤ))
      (TopCat.Sheaf.sectionComplexRestriction_comp' Y (.up ℤ) K rU
        (homOfLE hWU) rW)
    rw [HomologicalComplex.homologyMap_comp] at hr
    have hn := TopCat.Sheaf.sectionCohomologyToSheafSection_restriction
      Y K (2 : ℤ) (homOfLE hWU)
    have he := congrArg (fun f => HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction Y (.up ℤ) K rU) (2 : ℤ) ≫ f) hn
    simp only [← Category.assoc, ← hr] at he
    have he' := ConcreteCategory.congr_hom he a
    simp only [ConcreteCategory.comp_apply] at he'
    rw [hopen]
    exact he'.symm
  exact hnat.symm.trans (congrArg
    (fun v => (complexSupportInjectiveCohomologySheafIsoRelative X
      (cycleComponentAnalyticClosedSupport X x) 2).hom.hom.app (op W) v) hs)

end AlgebraicGeometry.ComplexPoint
