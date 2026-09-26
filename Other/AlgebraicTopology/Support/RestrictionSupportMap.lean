/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation
public import Other.AlgebraicTopology.SupportedSingularBoundaryRelative
public import Other.Algebra.Homology.DerivedCategory.MappingCoconeBoundaryNaturality
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsNaturality
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionConeNaturality

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open HomologicalComplex
open AlgebraicTopology.Singular
open TopCat.Sheaf

namespace TopCat.Sheaf

variable {X : TopCat.{0}} [T2Space X]
set_option maxHeartbeats 1000000

def supportRestrictionComplexSupportMap
    {U V : Opens X} (h : V ≤ U) (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) :
    supportRestrictionComplexShortComplex X U K ⟶
      supportRestrictionComplexShortComplex X V K where
  τ₁ := (sheafSectionsSupportedOutsideMap X h).mapHomologicalComplex ℤᵘᵖ |>.app K
  τ₂ := 𝟙 K
  τ₃ := (openRestrictionPushforwardMap X h).mapHomologicalComplex ℤᵘᵖ |>.app K
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (sheafSectionsSupportedOutsideMap X h).app (K.X n) ≫
        (sheafSectionsSupportedOutsideInclusion X V).app (K.X n) =
      (sheafSectionsSupportedOutsideInclusion X U).app (K.X n)
    exact NatTrans.congr_app (sheafSectionsSupportedOutsideMap_inclusion X h) _
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (toOpenRestrictionPushforward X V).app (K.X n) =
      (toOpenRestrictionPushforward X U).app (K.X n) ≫
        (openRestrictionPushforwardMap X h).app (K.X n)
    exact (NatTrans.congr_app (toOpenRestrictionPushforward_comp X h) _).symm

def supportRestrictionSectionsSupportMap
    {U V : Opens X} (h : V ≤ U) (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ)
    (W : Opens X) :
    supportRestrictionSectionsComplexShortComplex X U W K ⟶
      supportRestrictionSectionsComplexShortComplex X V W K := by
  let F := (supportEvaluation X W).mapHomologicalComplex ℤᵘᵖ
  let S := supportRestrictionComplexShortComplex X U K
  let T := supportRestrictionComplexShortComplex X V K
  change S.map F ⟶ T.map F
  let f := supportRestrictionComplexSupportMap h K
  exact
    { τ₁ := F.map f.τ₁
      τ₂ := F.map f.τ₂
      τ₃ := F.map f.τ₃
      comm₁₂ := congrArg F.map f.comm₁₂
      comm₂₃ := congrArg F.map f.comm₂₃ }

end TopCat.Sheaf

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
set_option maxHeartbeats 1000000

lemma supportedSingularKernelBoundary_supportMap
    {U V : Opens X} (h : V ≤ U) (W : Opens X) (n : ℕ)
    (z : (supportRestrictionSectionsComplexShortComplex X U W
      (rationalSingularCochainComplex X)).X₃.homology ((n : ℤ) - 1)) :
    (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsSupportMap h
          (rationalSingularCochainComplex X) W).τ₁ (n : ℤ)))
        ((supportedSingularKernelHomologyIsoCone X U W n).inv
          (HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.inr
              (supportRestrictionSectionsComplexShortComplex X U W
                (rationalSingularCochainComplex X)).g) ((n : ℤ) - 1) z)) =
      (supportedSingularKernelHomologyIsoCone X V W n).inv
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (supportRestrictionSectionsComplexShortComplex X V W
              (rationalSingularCochainComplex X)).g) ((n : ℤ) - 1))
          (HomologicalComplex.homologyMap
            (TopCat.Sheaf.supportRestrictionSectionsSupportMap h
              (rationalSingularCochainComplex X) W).τ₃ ((n : ℤ) - 1) z)) := by
  let S := supportRestrictionSectionsComplexShortComplex X U W
      (rationalSingularCochainComplex X)
  let T := supportRestrictionSectionsComplexShortComplex X V W
      (rationalSingularCochainComplex X)
  let f := TopCat.Sheaf.supportRestrictionSectionsSupportMap h
      (rationalSingularCochainComplex X) W
  have hf := _root_.CochainComplex.mappingCocone.shortExactHomologyIsoCone_inv_inr_naturality f
    (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U W
      (rationalSingularCochainComplex X) (fun _ => inferInstance))
    (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X V W
      (rationalSingularCochainComplex X) (fun _ => inferInstance))
    ((n : ℤ) - 1) (n : ℤ) (by omega)
  have hz := ConcreteCategory.congr_hom hf z
  change _ = _ at hz
  simpa only [supportedSingularKernelHomologyIsoCone, ConcreteCategory.comp_apply] using hz

end AlgebraicTopology.Singular

namespace TopCat.Sheaf

variable {X : TopCat.{0}} [T2Space X]
set_option maxHeartbeats 1000000

omit [T2Space X] in
lemma supportIntersectionIso_supportMap
    {U V : Opens X} (h : V ≤ U) (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ)
    (W : Opens X) :
    (TopCat.Sheaf.supportRestrictionSectionsSupportMap h K W).τ₃ ≫
      (supportRestrictionSectionsIntersectionIso X V W K).hom =
    (supportRestrictionSectionsIntersectionIso X U W K).hom ≫
      sectionComplexRestriction X ℤᵘᵖ K (homOfLE (inf_le_inf_left W h)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hτ3 : (TopCat.Sheaf.supportRestrictionSectionsSupportMap h K W).τ₃ =
      ((supportEvaluation X W).mapHomologicalComplex ℤᵘᵖ).map
        ((openRestrictionPushforwardMap X h).mapHomologicalComplex ℤᵘᵖ |>.app K) := by
    rfl
  rw [hτ3]
  rw [HomologicalComplex.comp_f]
  change (((supportEvaluation X W).mapHomologicalComplex ℤᵘᵖ).map
      ((openRestrictionPushforwardMap X h).mapHomologicalComplex ℤᵘᵖ |>.app K)).f n ≫ _ = _
  simp [supportRestrictionSectionsIntersectionIso, supportedOutsideIntersectionIso, Hom.isoOfComponents]
  change (K.X n).obj.map _ ≫ (K.X n).obj.map _ =
    (K.X n).obj.map _ ≫ (K.X n).obj.map _
  rw [← (K.X n).obj.map_comp, ← (K.X n).obj.map_comp]
  congr 1

end TopCat.Sheaf
