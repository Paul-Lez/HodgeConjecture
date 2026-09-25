/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Naturality of the injective model in the pair

For `U' ≤ U` and `V' ≤ V`, the identification `H^n(V, V ⊓ U; F) ≃ H^n(Γ_{X ∖ U}(V, I))` commutes
with the map of pairs on the left and with support enlargement followed by restriction on the
right.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

variable (X : TopCat.{0})

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable {U V W U' V' W' : Opens X} (hW : V ⊓ U = W) (hW' : V' ⊓ U' = W')
  (hU : U' ≤ U) (hV : V' ≤ V) (hWW : W' ≤ W)

lemma pairSheafHomEvaluation_restrict (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.map (CategoryTheory.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _)).op).app G ≫
        pairSheafHomEvaluation X U' V' W' hW' G =
      pairSheafHomEvaluation X U V W hW G ≫ G.obj.map (homOfLE hV).op := by
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext (fun φ => ?_)
  exact CategoryTheory.Sheaf.pairSheafHomAddEquiv_pairSheafMap_comp
    (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
    (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) G φ

lemma pairSheafHomIsoSupportedSections_restrict (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.map (CategoryTheory.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _)).op).app G ≫
        (pairSheafHomIsoSupportedSections X U' V' W' hW' G).hom =
      (pairSheafHomIsoSupportedSections X U V W hW G).hom ≫
        ((sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V) ≫
          ((sheafSectionsSupportedOutside X U').obj G).obj.map (homOfLE hV).op := by
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V'))).1
  have h1 : ((sheafSectionsSupportedOutside X U').obj G).obj.map (homOfLE hV).op ≫
      ((sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V') =
      ((sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V) ≫
        G.obj.map (homOfLE hV).op :=
    ((sheafSectionsSupportedOutsideInclusion X U').app G).hom.naturality (homOfLE hV).op
  have h2 : ((sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V) ≫
      ((sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V) =
      ((sheafSectionsSupportedOutsideInclusion X U).app G).hom.app (op V) := by
    change (((sheafSectionsSupportedOutsideMap X hU).app G ≫
      (sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V)) = _
    rw [← NatTrans.comp_app, sheafSectionsSupportedOutsideMap_inclusion]
  rw [Category.assoc, pairSheafHomIsoSupportedSections_hom_inclusion,
    pairSheafHomEvaluation_restrict X hW hW' hV hWW, Category.assoc, Category.assoc, h1,
    ← Category.assoc (((sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V)), h2,
    ← Category.assoc, pairSheafHomIsoSupportedSections_hom_inclusion]

lemma homComplexPairSheafIsoSupportedSections_restrict
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ) :
    CochainComplex.HomComplex.precompMap ((CochainComplex.singleFunctor _ 0).map
        (CategoryTheory.Sheaf.pairSheafMap
          (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
          (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _))) K ≫
        (homComplexPairSheafIsoSupportedSections X U' V' W' hW' K).hom =
      (homComplexPairSheafIsoSupportedSections X U V W hW K).hom ≫
        supportedSectionsRestriction X hU hV K := by
  dsimp only [homComplexPairSheafIsoSupportedSections, Iso.trans_hom]
  rw [← Category.assoc,
    CochainComplex.HomComplex.precompMap_single_fromSingleZeroIsoPreadditiveCoyoneda,
    Category.assoc, Category.assoc]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  exact pairSheafHomIsoSupportedSections_restrict X hW hW' hU hV hWW (K.X n)

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

local instance :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
  HasDerivedCategory.standard _

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The injective model is natural in the pair. -/
theorem relHAddEquivSupportedSectionsHomology_restrict
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (x : CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    relHAddEquivSupportedSectionsHomology X U' V' W' hW' F I ι n
        (CategoryTheory.Sheaf.relH.restrict F _ _ (homOfLE hWW) (homOfLE hV)
          (Subsingleton.elim _ _) n x) =
      HomologicalComplex.homologyMap (supportedSectionsRestriction X hU hV I) n
        (relHAddEquivSupportedSectionsHomology X U V W hW F I ι n x) := by
  obtain ⟨g, hg⟩ : ∃ g : pairSheaf' X U' V' W' hW' ⟶ pairSheaf' X U V W hW,
      g = CategoryTheory.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) := ⟨_, rfl⟩
  have hA : Ext.homAddEquiv (CategoryTheory.Sheaf.relH.restrict F
      (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
      (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g) ≫ Ext.homAddEquiv x := by
    rw [hg]
    simp only [CategoryTheory.Sheaf.relH.restrict, Ext.homAddEquiv_apply,
      Ext.bilinearComp_apply_apply, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
    rfl
  have hB (y : ShiftedHom
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)))
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) (n : ℤ)) :
      isoHomCongrAddEquiv (Iso.refl (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U' V' W' hW'))))
        ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι)))
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g) ≫ y) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g) ≫
        isoHomCongrAddEquiv (Iso.refl (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW))))
        ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι))) y := by
    simp [isoHomCongrAddEquiv_apply]
  have hD (c : CochainComplex.HomComplex.CohomologyClass
      ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)) I n) :
      (CochainComplex.HomComplex.homologyAddEquiv _ I n).symm
        (CochainComplex.HomComplex.precompClass ((CochainComplex.singleFunctor _ 0).map g) I n c) =
      HomologicalComplex.homologyMap (CochainComplex.HomComplex.precompMap
        ((CochainComplex.singleFunctor _ 0).map g) I) n
        ((CochainComplex.HomComplex.homologyAddEquiv _ I n).symm c) := by
    apply (CochainComplex.HomComplex.homologyAddEquiv _ I n).injective
    rw [CochainComplex.HomComplex.homologyAddEquiv_precompMap, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
  have hE : HomologicalComplex.homologyMap (CochainComplex.HomComplex.precompMap
        ((CochainComplex.singleFunctor _ 0).map g) I) n ≫
        HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections X U' V' W' hW' I).hom n =
      HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections X U V W hW I).hom n ≫
        HomologicalComplex.homologyMap (supportedSectionsRestriction X hU hV I) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hg,
      homComplexPairSheafIsoSupportedSections_restrict X hW hW' hU hV hWW I]
  have hF (z : (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)) I).homology n) :
      (HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections X U' V' W' hW' I).hom
        n).hom ((HomologicalComplex.homologyMap (CochainComplex.HomComplex.precompMap
          ((CochainComplex.singleFunctor _ 0).map g) I) n).hom z) =
      (HomologicalComplex.homologyMap (supportedSectionsRestriction X hU hV I) n).hom
        ((HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections X U V W hW I).hom
          n).hom z) := by
    have := congrArg AddCommGrpCat.Hom.hom hE
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at this
    exact DFunLike.congr_fun this z
  dsimp only [relHAddEquivSupportedSectionsHomology, AddEquiv.trans_apply]
  rw [hA]
  erw [hB]
  rw [CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_precomp, hD]
  rw [Iso.addCommGroupIsoToAddEquiv_apply, Iso.addCommGroupIsoToAddEquiv_apply,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_hom, hF]
  rfl

end TopCat.Sheaf

end
