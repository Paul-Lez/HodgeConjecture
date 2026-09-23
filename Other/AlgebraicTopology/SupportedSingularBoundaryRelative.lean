/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularSectionNaturality
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingConeMapNaturality

/-!
# Positive local normalization of supported-singular boundaries

On every actual open, the prescribed supported-singular section comparison sends
the positive kernel boundary to the positive raw relative-cone boundary. All
intersection, sheafification, and grading maps are the existing ones.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace CochainComplex.mappingCone
variable {C : Type*} [Category* C] [Abelian C]
  {K L K' L' : CochainComplex C ℤ}

/-- The literal arrow-isomorphism cone map preserves positive boundary inclusion. -/
@[reassoc]
lemma inr_mapArrowIso (f : K ⟶ L) (g : K' ⟶ L') (e : Arrow.mk f ≅ Arrow.mk g) :
    inr f ≫ (HomologicalComplex.homotopyCofiber.mapArrowIso f g
      (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩) e).hom =
    e.hom.right ≫ inr g := by
  simp [HomologicalComplex.homotopyCofiber.mapArrowIso,
    HomologicalComplex.homotopyCofiber.mapArrowHom, inr]
end CochainComplex.mappingCone

namespace TopCat.Sheaf
variable (X : TopCat.{0}) (U V : Opens X)
  (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ)

@[reassoc]
lemma supportRestrictionSectionsConeIso_inr :
    CochainComplex.mappingCone.inr (supportRestrictionSectionsComplexShortComplex X U V K).g ≫
      (supportRestrictionSectionsConeIso X U V K).hom =
    (supportRestrictionSectionsIntersectionIso X U V K).hom ≫
      CochainComplex.mappingCone.inr
        (sectionComplexRestriction X (.up ℤ) K (Opens.infLELeft V U)) :=
  CochainComplex.mappingCone.inr_mapArrowIso _ _ _

@[reassoc]
lemma sectionComplexRestrictionExtendConeIso_inr
    (K₀ : CochainComplex (Sheaf AddCommGrpCat X) ℕ) {V W : Opens X} (i : W ⟶ V) :
    CochainComplex.mappingCone.inr
      (sectionComplexRestriction X (.up ℤ) (K₀.extend ComplexShape.embeddingUpNat) i) ≫
      (sectionComplexRestrictionExtendConeIso X K₀ i).hom =
    (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X W) K₀
      ComplexShape.embeddingUpNat).hom ≫
      CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K₀ i)
          ComplexShape.embeddingUpNat) :=
  CochainComplex.mappingCone.inr_mapArrowIso _ _ _
end TopCat.Sheaf

namespace AlgebraicTopology.Singular
open TopCat.Sheaf
variable (X : TopCat.{0}) (U V : Opens X)

/-- Raw cochains on `V ∩ U` mapped to the actual outside term by sheafification. -/
def openRawToSupportedSingularOutside :
    (openRawSingularCochainComplex ℚ X (V ⊓ U)).extend ComplexShape.embeddingUpNat ⟶
    (supportRestrictionSectionsComplexShortComplex X U V (rationalSingularCochainComplex X)).X₃ :=
  HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X (V ⊓ U))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X (V ⊓ U))
      (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv ≫
    (supportRestrictionSectionsIntersectionIso X U V (rationalSingularCochainComplex X)).inv

/-- The actual outside-to-cone maps carry the literal raw positive boundary to
the sheafification of the same positive raw boundary. -/
lemma openRawToSupportedSingularOutside_boundary :
    openRawToSupportedSingularOutside X U V ≫
      (CochainComplex.mappingCone.inr
        (supportRestrictionSectionsComplexShortComplex X U V (rationalSingularCochainComplex X)).g ≫
        (supportRestrictionSectionsConeIso X U V (rationalSingularCochainComplex X)).hom ≫
        (sectionComplexRestrictionExtendConeIso X (singularCochainSheafComplex ℚ X)
          (Opens.infLELeft V U)).hom) =
    CochainComplex.mappingCone.inr
      (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X (Opens.infLELeft V U))
        ComplexShape.embeddingUpNat) ≫
      openRawToSingularSheafRestrictionCone ℚ X (Opens.infLELeft V U) := by
  let K := rationalSingularCochainComplex X
  let K₀ := singularCochainSheafComplex ℚ X
  let i := Opens.infLELeft V U
  let eO := supportRestrictionSectionsIntersectionIso X U V K
  let eI := supportRestrictionSectionsConeIso X U V K
  let eW := HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X (V ⊓ U))
    K₀ ComplexShape.embeddingUpNat
  let eG := sectionComplexRestrictionExtendConeIso X K₀ i
  let b := HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X (V ⊓ U))
    ComplexShape.embeddingUpNat
  let k := CochainComplex.mappingCone.inr (supportRestrictionSectionsComplexShortComplex X U V K).g
  let l := CochainComplex.mappingCone.inr (sectionComplexRestriction X (.up ℤ) K i)
  let r := CochainComplex.mappingCone.inr
    (HomologicalComplex.extendMap (openSingularSheafRestriction ℚ X i) ComplexShape.embeddingUpNat)
  have hI : k ≫ eI.hom = eO.hom ≫ l := supportRestrictionSectionsConeIso_inr X U V K
  have hG : l ≫ eG.hom = eW.hom ≫ r :=
    sectionComplexRestrictionExtendConeIso_inr X K₀ i
  have hIG : (k ≫ eI.hom) ≫ eG.hom = eO.hom ≫ eW.hom ≫ r := by
    rw [hI, Category.assoc, hG]
  have hR : CochainComplex.mappingCone.inr
      (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i) ComplexShape.embeddingUpNat) ≫
      openRawToSingularSheafRestrictionCone ℚ X i = b ≫ r := by
    simp [openRawToSingularSheafRestrictionCone, CochainComplex.mappingCone.map, b, r]
  change (b ≫ eW.inv ≫ eO.inv) ≫ (k ≫ eI.hom ≫ eG.hom) = _
  rw [← Category.assoc k, hIG, hR]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable [T2Space X] [∀ W : Opens X, ParacompactSpace W]

/-- The positive canonical kernel-to-cone comparison for supported singular sections. -/
def supportedSingularKernelHomologyIsoCone (n : ℤ) :
    (supportRestrictionSectionsComplexShortComplex X U V
      (rationalSingularCochainComplex X)).X₁.homology n ≅
    (CochainComplex.mappingCone (supportRestrictionSectionsComplexShortComplex X U V
      (rationalSingularCochainComplex X)).g).homology (n - 1) :=
  CochainComplex.mappingCocone.shortExactHomologyIsoCone _
    (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V _
      (fun _ => inferInstance)) (n - 1) n (by omega)

/-- The existing supported-singular relative comparison takes the positive actual
kernel boundary of a raw complement class to its positive raw relative boundary. -/
lemma supportedSingularSectionCohomologyEquivRelative_boundary (n : ℕ)
    (z : ((openRawSingularCochainComplex ℚ X (V ⊓ U)).extend
      ComplexShape.embeddingUpNat).homology ((n : ℤ) - 1)) :
    supportedRationalSingularSectionCohomologyEquivRelative X U V n
      ((supportedSingularKernelHomologyIsoCone X U V n).inv
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (supportRestrictionSectionsComplexShortComplex X U V
              (rationalSingularCochainComplex X)).g) ((n : ℤ) - 1)
          (HomologicalComplex.homologyMap
            (openRawToSupportedSingularOutside X U V) ((n : ℤ) - 1) z))) =
    openRawSingularRestrictionConeCohomologyEquivRelative ℚ X (Opens.infLELeft V U) n
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X (Opens.infLELeft V U))
            ComplexShape.embeddingUpNat)) ((n : ℤ) - 1) z) := by
  let eK := supportedSingularKernelHomologyIsoCone X U V n
  let eI := supportRestrictionSectionsConeIso X U V (rationalSingularCochainComplex X)
  let eG := sectionComplexRestrictionExtendConeIso X (singularCochainSheafComplex ℚ X)
    (Opens.infLELeft V U)
  let c := openRawToSingularSheafRestrictionCone ℚ X (Opens.infLELeft V U)
  let := openRawToSingularSheafRestrictionCone_quasiIso X (Opens.infLELeft V U)
  let eC := asIso (HomologicalComplex.homologyMap c ((n : ℤ) - 1))
  change openRawSingularRestrictionConeCohomologyEquivRelative ℚ X (Opens.infLELeft V U) n
    (eC.inv (HomologicalComplex.homologyMap eG.hom ((n : ℤ) - 1)
      (HomologicalComplex.homologyMap eI.hom ((n : ℤ) - 1)
        (eK.hom (eK.inv _))))) = _
  have hcancel (w) : eK.hom (eK.inv w) = w := eK.addCommGroupIsoToAddEquiv.apply_symm_apply w
  rw [hcancel]
  apply congrArg (openRawSingularRestrictionConeCohomologyEquivRelative ℚ X (Opens.infLELeft V U) n)
  apply eC.addCommGroupIsoToAddEquiv.symm_apply_eq.mpr
  have h := congrArg (fun f => HomologicalComplex.homologyMap f ((n : ℤ) - 1))
    (openRawToSupportedSingularOutside_boundary X U V)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h z

end AlgebraicTopology.Singular
