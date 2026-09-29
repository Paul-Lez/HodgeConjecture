/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.GlobalRawOpenComplement
public import Other.AlgebraicGeometry.ComplementResolutionBoundaryComparison
public import Other.AlgebraicGeometry.ComplexSupportedOrdinaryComparison

/-!
# The literal raw complement and fixed resolution comparisons

Raw complement cochains map to the actual outside term of the supported singular
complex by sheafification. This map preserves restriction and agrees with the
fixed natural complement resolution map. The ambient-injective comparison has
the same map on cohomology by the proved complement homotopy.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

/-- The literal raw complement cochains mapped by the actual sheafification unit
to the complement term of the supported singular section complex. -/
def globalRawComplementToActualSingularOutside :
    globalRawPushforwardSingularCochainComplexInt ℚ (TopCat.of (ComplexPoint X)) Zᶜ ⟶
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₃ :=
  globalRawComplementToTopOpenCochains ℚ (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩ ≫
    HomologicalComplex.extendMap
      (openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))
        (⊤ ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩)) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
        (⊤ ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩))
      (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat).inv ≫
    (TopCat.Sheaf.supportRestrictionSectionsIntersectionIso (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).inv

/-- The actual raw-to-supported-singular comparison preserves ambient restriction. -/
lemma globalRawSingularRestrictionInt_comp_actualSingularOutside :
    globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X)) Zᶜ ≫
      globalRawComplementToActualSingularOutside X Z hZ =
    globalRawToSingularSheafInt X ≫
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let K := singularCochainSheafComplex ℚ Y
  let e := TopCat.Sheaf.supportRestrictionSectionsIntersectionIso Y U ⊤
    (rationalSingularCochainComplex Y)
  let eW := HomologicalComplex.mapExtendCanonicalIso
    (TopCat.Sheaf.supportEvaluation Y (⊤ ⊓ U)) K ComplexShape.embeddingUpNat
  let eTop := HomologicalComplex.mapExtendCanonicalIso
    (TopCat.Sheaf.supportEvaluation Y ⊤) K ComplexShape.embeddingUpNat
  let ρ := globalRawSingularRestrictionInt ℚ Y Zᶜ
  let t := globalRawComplementToTopOpenCochains ℚ Y U
  let a := HomologicalComplex.extendMap
    (openRawToSingularCochainSheafComplex ℚ Y ⊤) ComplexShape.embeddingUpNat
  let b := HomologicalComplex.extendMap
    (openRawToSingularCochainSheafComplex ℚ Y (⊤ ⊓ U)) ComplexShape.embeddingUpNat
  let r := HomologicalComplex.extendMap
    (openSingularSheafRestriction ℚ Y (Opens.infLELeft ⊤ U)) ComplexShape.embeddingUpNat
  let r' := TopCat.Sheaf.sectionComplexRestriction Y (.up ℤ)
    (rationalSingularCochainComplex Y) (Opens.infLELeft ⊤ U)
  let g := (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (rationalSingularCochainComplex Y)).g
  have hunit : (ρ ≫ t) ≫ b = a ≫ r := by
    have ht := globalRawSingularRestrictionInt_comp_topOpen ℚ Y U
    have hn := openSingularSheafRestrictionInt_naturality ℚ Y (Opens.infLELeft ⊤ U)
    exact (congrArg (fun k => k ≫ b) ht).trans hn
  have hgrade : r ≫ eW.inv = eTop.inv ≫ r' := by
    have hext : r' ≫ eW.hom = eTop.hom ≫ r :=
      TopCat.Sheaf.sectionComplexRestriction_extend Y K (Opens.infLELeft ⊤ U)
    apply (cancel_mono eW.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hext, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hrestr : g ≫ e.hom = r' :=
    TopCat.Sheaf.supportRestrictionSectionsIntersectionIso_restriction Y U ⊤
      (rationalSingularCochainComplex Y)
  have htop : a ≫ eTop.inv = globalRawToSingularSheafInt X :=
    complexOpenRawToSheafTop_eq_global X
  have hrestr' : r' ≫ e.inv = g := by
    rw [← hrestr]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change ρ ≫ (t ≫ b ≫ eW.inv ≫ e.inv) = globalRawToSingularSheafInt X ≫ g
  calc
    _ = ((ρ ≫ t) ≫ b) ≫ eW.inv ≫ e.inv := by simp only [Category.assoc]
    _ = (a ≫ r) ≫ eW.inv ≫ e.inv := congrArg (fun k => k ≫ eW.inv ≫ e.inv) hunit
    _ = (a ≫ eTop.inv) ≫ r' ≫ e.inv := by
      simpa only [Category.assoc] using congrArg (fun k => a ≫ k ≫ e.inv) hgrade
    _ = (a ≫ eTop.inv) ≫ g := congrArg (fun k => (a ≫ eTop.inv) ≫ k) hrestr'
    _ = _ := congrArg (fun k => k ≫ g) htop

variable [IsIntegral X.left] [Smooth X.hom]

/-- The literal complement comparison agrees strictly with the fixed natural
comparison. Epimorphism cancellation is performed on complex maps. -/
lemma globalRawComplementToActualSingularOutside_comp_natural :
    globalRawComplementToActualSingularOutside X Z hZ ≫
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (naturalSingularOutsideResolutionComparison X Z hZ)) =
    globalRawComplementToDerivedPushforwardInt X Z hZ := by
  let Γ := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)
  let := globalRawSingularRestrictionInt_epi ℚ (TopCat.of (ComplexPoint X)) Zᶜ
  apply (cancel_epi (globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X)) Zᶜ)).mp
  rw [← Category.assoc, globalRawSingularRestrictionInt_comp_actualSingularOutside,
    Category.assoc]
  change globalRawToSingularSheafInt X ≫
      (Γ.map (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
        ⟨Zᶜ, hZ.isOpen_compl⟩ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g ≫
        Γ.map (naturalSingularOutsideResolutionComparison X Z hZ)) = _
  rw [← Functor.map_comp, actualSingularRestriction_comp_naturalOutsideResolutionComparison]
  exact globalNaturalSingularResolutionRestrictionInt_naturality X Z hZ

/-- The ambient-injective complement comparison has the same map on cohomology
as the fixed natural comparison after the literal raw sheafification unit. -/
lemma globalRawComplementToActualSingularOutside_comp_ambient_homologyMap (n : ℤ) :
    HomologicalComplex.homologyMap
      (globalRawComplementToActualSingularOutside X Z hZ ≫
        (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
          (.up ℤ)).map (ambientSingularOutsideResolutionComparison X Z hZ))) n =
      HomologicalComplex.homologyMap (globalRawComplementToDerivedPushforwardInt X Z hZ) n := by
  rw [HomologicalComplex.homologyMap_comp,
    ← naturalSingularOutsideResolutionComparison_homologyMap,
    ← HomologicalComplex.homologyMap_comp,
    globalRawComplementToActualSingularOutside_comp_natural]

end AlgebraicGeometry.ComplexPoint
