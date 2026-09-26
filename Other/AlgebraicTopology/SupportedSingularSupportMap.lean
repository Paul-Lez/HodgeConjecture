/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation
public import Other.AlgebraicTopology.Support.RestrictionSupportMap
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainOpenConeNaturality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open HomologicalComplex
open AlgebraicTopology.Singular
open TopCat.Sheaf

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0}) [T2Space X]
set_option maxHeartbeats 1000000

omit [T2Space X] in
lemma openRawToSupportedSingularOutside_supportMap
    {U V : Opens X} (h : V ≤ U) (W : Opens X) :
    openRawToSupportedSingularOutside X U W ≫
        (TopCat.Sheaf.supportRestrictionSectionsSupportMap h
          (rationalSingularCochainComplex X) W).τ₃ =
      HomologicalComplex.extendMap
          (openRawSingularRestriction ℚ X (homOfLE (inf_le_inf_left W h)))
          ComplexShape.embeddingUpNat ≫
        openRawToSupportedSingularOutside X V W := by
  let K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
    (singularCochainSheafComplex ℚ X).extend ComplexShape.embeddingUpNat
  let j := homOfLE (inf_le_inf_left W h)
  let bU :
      (openRawSingularCochainComplex ℚ X (W ⊓ U)).extend ComplexShape.embeddingUpNat ⟶
        (((supportEvaluation X (W ⊓ U)).mapHomologicalComplex (.up ℕ)).obj
          (singularCochainSheafComplex ℚ X)).extend ComplexShape.embeddingUpNat := by
    simpa only [openSingularCochainSheafComplex] using
      (HomologicalComplex.extendMap
        (openRawToSingularCochainSheafComplex ℚ X (W ⊓ U)) ComplexShape.embeddingUpNat)
  let bV :
      (openRawSingularCochainComplex ℚ X (W ⊓ V)).extend ComplexShape.embeddingUpNat ⟶
        (((supportEvaluation X (W ⊓ V)).mapHomologicalComplex (.up ℕ)).obj
          (singularCochainSheafComplex ℚ X)).extend ComplexShape.embeddingUpNat := by
    simpa only [openSingularCochainSheafComplex] using
      (HomologicalComplex.extendMap
        (openRawToSingularCochainSheafComplex ℚ X (W ⊓ V)) ComplexShape.embeddingUpNat)
  let eU := HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X (W ⊓ U))
    (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat
  let eV := HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X (W ⊓ V))
    (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat
  let sV :
      (((supportEvaluation X (W ⊓ U)).mapHomologicalComplex (.up ℕ)).obj
          (singularCochainSheafComplex ℚ X)).extend ComplexShape.embeddingUpNat ⟶
        (((supportEvaluation X (W ⊓ V)).mapHomologicalComplex (.up ℕ)).obj
          (singularCochainSheafComplex ℚ X)).extend ComplexShape.embeddingUpNat := by
    simpa only [openSingularCochainSheafComplex] using
      (HomologicalComplex.extendMap (openSingularSheafRestriction ℚ X j)
        ComplexShape.embeddingUpNat)
  let qU := supportRestrictionSectionsIntersectionIso X U W K
  let qV := supportRestrictionSectionsIntersectionIso X V W K
  let r := HomologicalComplex.extendMap (openRawSingularRestriction ℚ X j)
    ComplexShape.embeddingUpNat
  have hq :
      (TopCat.Sheaf.supportRestrictionSectionsSupportMap h K W).τ₃ ≫ qV.hom =
        qU.hom ≫ sectionComplexRestriction X ℤᵘᵖ K j :=
    TopCat.Sheaf.supportIntersectionIso_supportMap h K W
  have hr : sectionComplexRestriction X ℤᵘᵖ K j ≫ eV.hom =
      eU.hom ≫ HomologicalComplex.extendMap
        (sectionComplexRestriction X (.up ℕ) (singularCochainSheafComplex ℚ X) j)
        ComplexShape.embeddingUpNat := by
    simpa only [K, rationalSingularCochainComplex] using
      (sectionComplexRestriction_extend X (singularCochainSheafComplex ℚ X) j)
  have hb :
      HomologicalComplex.extendMap (openRawSingularRestriction ℚ X j)
          ComplexShape.embeddingUpNat ≫ bV =
        bU ≫ sV := by
    simpa only [bU, bV, sV, openRawToSupportedSingularOutside,
      openSingularCochainSheafComplex] using
      (openSingularSheafRestrictionInt_naturality ℚ X j)
  have hq' : qU.inv ≫
      (TopCat.Sheaf.supportRestrictionSectionsSupportMap h K W).τ₃ =
      sectionComplexRestriction X ℤᵘᵖ K j ≫ qV.inv := by
    apply (cancel_mono qV.hom).1
    calc
      (qU.inv ≫ (TopCat.Sheaf.supportRestrictionSectionsSupportMap h K W).τ₃) ≫ qV.hom =
          qU.inv ≫ ((TopCat.Sheaf.supportRestrictionSectionsSupportMap h K W).τ₃ ≫ qV.hom) := by
            simp only [Category.assoc]
      _ = qU.inv ≫ (qU.hom ≫ sectionComplexRestriction X ℤᵘᵖ K j) := by rw [hq]
      _ = sectionComplexRestriction X ℤᵘᵖ K j := by
        exact qU.inv_hom_id_assoc _
      _ = (sectionComplexRestriction X ℤᵘᵖ K j ≫ qV.inv) ≫ qV.hom := by
        simp only [Category.assoc, qV.inv_hom_id, Category.comp_id]
  have hR : eU.inv ≫ sectionComplexRestriction X ℤᵘᵖ K j = sV ≫ eV.inv := by
    apply (cancel_mono eV.hom).1
    calc
      (eU.inv ≫ sectionComplexRestriction X ℤᵘᵖ K j) ≫ eV.hom =
          eU.inv ≫ (sectionComplexRestriction X ℤᵘᵖ K j ≫ eV.hom) := by
            simp only [Category.assoc]
      _ = eU.inv ≫ (eU.hom ≫ HomologicalComplex.extendMap
          (sectionComplexRestriction X (.up ℕ) (singularCochainSheafComplex ℚ X) j)
          ComplexShape.embeddingUpNat) := by rw [hr]
      _ = HomologicalComplex.extendMap
          (sectionComplexRestriction X (.up ℕ) (singularCochainSheafComplex ℚ X) j)
          ComplexShape.embeddingUpNat := by
        exact eU.inv_hom_id_assoc _
      _ = (sV ≫ eV.inv) ≫ eV.hom := by
        simp only [Category.assoc, eV.inv_hom_id, Category.comp_id]
        rfl
  dsimp only [openRawToSupportedSingularOutside]
  change (bU ≫ eU.inv ≫ qU.inv) ≫
      (TopCat.Sheaf.supportRestrictionSectionsSupportMap h K W).τ₃ =
    r ≫ bV ≫ eV.inv ≫ qV.inv
  have hR' : eU.inv ≫ sectionComplexRestriction X ℤᵘᵖ K j ≫ qV.inv =
      sV ≫ eV.inv ≫ qV.inv := by
    rw [← Category.assoc, hR]
    exact Category.assoc _ _ _
  simp only [Category.assoc]
  rw [hq']
  rw [hR']
  rw [← Category.assoc, ← hb]
  change (r ≫ bV) ≫ eV.inv ≫ qV.inv = _
  exact Category.assoc _ _ _

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
set_option maxHeartbeats 1000000

lemma supportedSingularKernelBoundary_supportMap_of_raw
    {U V : Opens X} (h : V ≤ U) (W : Opens X)
    (zU : ((openRawSingularCochainComplex ℚ X (W ⊓ U)).extend
      ComplexShape.embeddingUpNat).homology (1 : ℤ))
    (zV : ((openRawSingularCochainComplex ℚ X (W ⊓ V)).extend
      ComplexShape.embeddingUpNat).homology (1 : ℤ))
    (hraw : HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap
        (openRawSingularRestriction ℚ X (homOfLE (inf_le_inf_left W h)))
        ComplexShape.embeddingUpNat) 1 zU = zV) :
    (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsSupportMap h
          (rationalSingularCochainComplex X) W).τ₁ 2))
      ((supportedSingularKernelHomologyIsoCone X U W 2).inv
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U W
              (rationalSingularCochainComplex X)).g) 1
          (HomologicalComplex.homologyMap
            (openRawToSupportedSingularOutside X U W) 1 zU))) =
      (supportedSingularKernelHomologyIsoCone X V W 2).inv
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X V W
              (rationalSingularCochainComplex X)).g) 1
          (HomologicalComplex.homologyMap
            (openRawToSupportedSingularOutside X V W) 1 zV)) := by
  let f := TopCat.Sheaf.supportRestrictionSectionsSupportMap h
    (rationalSingularCochainComplex X) W
  let j := homOfLE (inf_le_inf_left W h)
  have hsq := openRawToSupportedSingularOutside_supportMap X h W
  have hsqH := congrArg (fun g => HomologicalComplex.homologyMap g 1) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsqH
  have hsqz := ConcreteCategory.congr_hom hsqH zU
  change
    (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside X U W) 1 ≫
          HomologicalComplex.homologyMap f.τ₃ 1)) zU =
      (ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X j)
            ComplexShape.embeddingUpNat) 1 ≫
          HomologicalComplex.homologyMap
            (openRawToSupportedSingularOutside X V W) 1)) zU at hsqz
  have hsqz' :
      (ConcreteCategory.hom
        (HomologicalComplex.homologyMap f.τ₃ 1))
        ((ConcreteCategory.hom
          (HomologicalComplex.homologyMap
            (openRawToSupportedSingularOutside X U W) 1)) zU) =
      (ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (openRawToSupportedSingularOutside X V W) 1))
        ((ConcreteCategory.hom
          (HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X j)
              ComplexShape.embeddingUpNat) 1)) zU) := by
    simpa only [ConcreteCategory.comp_apply] using hsqz
  rw [hraw] at hsqz'
  have hboundary := supportedSingularKernelBoundary_supportMap X h W 2
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside X U W) 1 zU)
  have hboundary' := congrArg (fun z =>
    (supportedSingularKernelHomologyIsoCone X V W 2).inv
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X V W
            (rationalSingularCochainComplex X)).g) 1 z)) hsqz'
  exact hboundary.trans hboundary'

end AlgebraicTopology.Singular
