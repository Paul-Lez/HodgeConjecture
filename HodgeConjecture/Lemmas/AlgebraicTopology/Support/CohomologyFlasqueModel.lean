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

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyFlasqueModel
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.CohomologyStalkVanishing
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.FlasqueLowestCohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyInjectiveModel

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Naturality of the flasque model in the pair

The identification `H^n(V, V ⊓ U; F) ≃ H^n(Γ_{X ∖ U}(V, K))` commutes with the map of pairs and
with support enlargement followed by restriction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

variable (X : TopCat.{0})

variable {U V U' V' : Opens X} (hU : U' ≤ U) (hV : V' ≤ V)

lemma supportedSectionsRestriction_naturality
    {K L : CochainComplex (Sheaf AddCommGrpCat X) ℤ} (φ : K ⟶ L) :
    supportedSectionsRestriction X hU hV K ≫
        ((supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
          (((sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map φ) =
      ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
          (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map φ) ≫
        supportedSectionsRestriction X hU hV L := by
  have h1 := (NatTrans.mapHomologicalComplex (supportEvaluationRestriction X (homOfLE hV))
    ℤᵘᵖ).naturality (((sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map φ)
  have h2 := (NatTrans.mapHomologicalComplex (sheafSectionsSupportedOutsideMap X hU)
    ℤᵘᵖ).naturality φ
  dsimp only [supportedSectionsRestriction, sectionComplexRestriction]
  simp only [Category.assoc]
  rw [← h1]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← h2]

variable {W W' : Opens X} (hW : V ⊓ U = W) (hW' : V' ⊓ U' = W') (hWW : W' ≤ W)
  (F : Sheaf AddCommGrpCat X) (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
  (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]
  (hK : ∀ n, IsFlasque (K.X n))

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The flasque model is natural in the pair. -/
theorem relHAddEquivSupportedSectionsHomologyOfFlasque_restrict (n : ℕ)
    (x : CategoryTheory.Sheaf.relH F n
      (homOfLE (hW ▸ (inf_le_left : V ⊓ U ≤ V) : W ≤ V))) :
    relHAddEquivSupportedSectionsHomologyOfFlasque X F K ι U' V' W' hW' hK n
        (CategoryTheory.Sheaf.relH.restrict F _ _ (homOfLE hWW) (homOfLE hV)
          (Subsingleton.elim _ _) n x) =
      HomologicalComplex.homologyMap (supportedSectionsRestriction X hU hV K) n
        (relHAddEquivSupportedSectionsHomologyOfFlasque X F K ι U V W hW hK n x) := by
  have := supportedSections_map_resolutionToInjective_quasiIso X F K ι U V hK
  have := supportedSections_map_resolutionToInjective_quasiIso X F K ι U' V' hK
  have hnat : HomologicalComplex.homologyMap (supportedSectionsRestriction X hU hV K) n ≫
      HomologicalComplex.homologyMap (((supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
        (((sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map
          (resolutionToInjective X F K ι))) n =
      HomologicalComplex.homologyMap (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
          (resolutionToInjective X F K ι))) n ≫
        HomologicalComplex.homologyMap
          (supportedSectionsRestriction X hU hV (injectiveResolutionComplex X F)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      supportedSectionsRestriction_naturality]
  have hinv : inv (HomologicalComplex.homologyMap
        (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
          (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
            (resolutionToInjective X F K ι))) n) ≫
        HomologicalComplex.homologyMap (supportedSectionsRestriction X hU hV K) n =
      HomologicalComplex.homologyMap
          (supportedSectionsRestriction X hU hV (injectiveResolutionComplex X F)) n ≫
        inv (HomologicalComplex.homologyMap
          (((supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
            (((sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map
              (resolutionToInjective X F K ι))) n) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hF (z : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
        (injectiveResolutionComplex X F))).homology n) :
      (inv (HomologicalComplex.homologyMap
          (((supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
            (((sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map
              (resolutionToInjective X F K ι))) n)).hom
        ((HomologicalComplex.homologyMap
          (supportedSectionsRestriction X hU hV (injectiveResolutionComplex X F)) n).hom z) =
      (HomologicalComplex.homologyMap (supportedSectionsRestriction X hU hV K) n).hom
        ((inv (HomologicalComplex.homologyMap
          (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
            (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
              (resolutionToInjective X F K ι))) n)).hom z) := by
    have := congrArg AddCommGrpCat.Hom.hom hinv
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at this
    exact (DFunLike.congr_fun this z).symm
  dsimp only [relHAddEquivSupportedSectionsHomologyOfFlasque, AddEquiv.trans_apply]
  rw [@relHAddEquivSupportedSectionsHomology_restrict X U V W U' V' W' hW hW' hU hV hWW _ F
    (injectiveResolutionComplex X F) (injectiveResolutionComplex_isKInjective X F)
    (injectiveResolutionAugmentation X F) (injectiveResolutionAugmentation_quasiIso X F) n x,
    Iso.addCommGroupIsoToAddEquiv_apply, Iso.addCommGroupIsoToAddEquiv_apply, Iso.symm_hom,
    Iso.symm_hom, asIso_inv, asIso_inv, hF]

set_option maxHeartbeats 800000 in
/-- If `F[0] → K` is a quasi-isomorphism to a bounded-below termwise-flasque complex, this
identifies the presheaf `V ↦ H^n(V, V \ Z; F)` with the cohomology presheaf of its supported
sections. -/
def supportHOnOpenPresheafIsoOfFlasque
    (Z : Closeds X) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Sheaf AddCommGrpCat X) 0).obj F ⟶ K) [Mono ι]
      [QuasiIso ι]
    (hK : ∀ n, IsFlasque (K.X n)) (n : ℕ) :
    supportHOnOpenPresheaf (Z := Z) F n ≅
      sectionCohomologyPresheaf X
        (((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K) (n : ℤ) :=
  let K' := ((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K
  NatIso.ofComponents
    (fun V => by
      let e := @relHAddEquivSupportedSectionsHomologyOfFlasque X F K (inferInstance : K.IsStrictlyGE 0) ι
        (inferInstance : Mono ι) (inferInstance : QuasiIso ι) Z.compl V.unop
        (V.unop ⊓ Z.compl) rfl hK inferInstance n
      exact e.toAddCommGrpIso ≪≫ sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) V.unop)
    (by
      intro U V f
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro z
      let hV : V.unop ≤ U.unop := leOfHom f.unop
      let hW : V.unop ⊓ Z.compl ≤ U.unop ⊓ Z.compl := inf_le_inf_right Z.compl hV
      change CategoryTheory.Sheaf.relH F n
        (homOfLE (inf_le_left : U.unop ⊓ Z.compl ≤ U.unop)) at z
      let eV := @relHAddEquivSupportedSectionsHomologyOfFlasque X F K (inferInstance : K.IsStrictlyGE 0) ι
        (inferInstance : Mono ι) (inferInstance : QuasiIso ι) Z.compl V.unop
        (V.unop ⊓ Z.compl) rfl hK inferInstance n
      let eU := @relHAddEquivSupportedSectionsHomologyOfFlasque X F K (inferInstance : K.IsStrictlyGE 0) ι
        (inferInstance : Mono ι) (inferInstance : QuasiIso ι) Z.compl U.unop
        (U.unop ⊓ Z.compl) rfl hK inferInstance n
      have hrestrict := relHAddEquivSupportedSectionsHomologyOfFlasque_restrict X
        (U := Z.compl) (V := U.unop) (W := U.unop ⊓ Z.compl)
        (U' := Z.compl) (V' := V.unop) (W' := V.unop ⊓ Z.compl)
        (hU := le_rfl) (hV := hV) (hW := rfl) (hW' := rfl) (hWW := hW) F K ι hK n z
      change (sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) V.unop).hom
        (eV (CategoryTheory.Sheaf.relH.restrict F
          (homOfLE (inf_le_left : U.unop ⊓ Z.compl ≤ U.unop))
          (homOfLE (inf_le_left : V.unop ⊓ Z.compl ≤ V.unop))
          (homOfLE (inf_le_inf_right Z.compl hV)) (homOfLE hV)
          (Subsingleton.elim _ _) n z)) =
        (sectionCohomologyPresheaf X K' (n : ℤ)).map f.unop.op
          ((sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) U.unop).hom (eU z))
      rw [hrestrict, supportedSectionsRestriction_refl]
      change (sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) V.unop).hom
          ((HomologicalComplex.homologyMap
            (sectionComplexRestriction X ℤᵘᵖ K' (homOfLE hV)) n).hom (eU z)) = _
      have hf : homOfLE hV = f.unop := Subsingleton.elim _ _
      rw [hf]
      have h := ConcreteCategory.congr_hom
        (sectionCohomologyPresheafOnOpenIso_inv_naturality X K' (n : ℤ) f.unop)
        ((sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) U.unop).hom (eU z))
      have hiso :
          (sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) U.unop).inv
              ((sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) U.unop).hom (eU z)) = eU z := by
        rw [← ConcreteCategory.comp_apply]
        simp
      simp only [ConcreteCategory.comp_apply] at h
      rw [hiso] at h
      rw [← h]
      simp)

set_option maxHeartbeats 800000 in
/-- If `H^j = 0` for `j < n`, this identifies global supported Ext `H_[Z]^n(X;F)` with global
sections of the supplied degree-`n` cohomology sheaf `H n`. -/
def supportHCohomologySheafSectionAddEquivOfFlasque
    (Z : Closeds X) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Sheaf AddCommGrpCat X) 0).obj F ⟶ K) [Mono ι]
      [QuasiIso ι]
    (hK : ∀ n, IsFlasque (K.X n))
    (H : ℕ → Sheaf AddCommGrpCat X)
    (e : ∀ n : ℕ, (((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K).homology
      (n : ℤ) ≅ H n)
    (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero (H j)) :
    H_[Z]^n(X; F) ≃+
      (supportHCohomologySheaf (Z := Z) F n).presheaf.obj (op ⊤) :=
  let K' := ((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K
  let p := supportHOnOpenPresheafIsoOfFlasque X Z F K ι hK n
  let s := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso p ≪≫
    sectionCohomologyPresheafSheafificationIso X K' (n : ℤ) ≪≫ e n
  let b := @relHAddEquivSupportedSectionsHomologyOfFlasque X F K (inferInstance : K.IsStrictlyGE 0) ι
    (inferInstance : Mono ι) (inferInstance : QuasiIso ι) Z.compl ⊤ Z.compl
    (top_inf_eq _) hK inferInstance n
  let hK' : ∀ j, (K'.X j).IsFlasque := fun j =>
    letI := hK j
    sheafSectionsSupportedOutside_isFlasque X Z.compl (K.X j)
  let l := lowestSectionCohomologyIsoOfNat X K'
    (fun j => H j) (fun j => e j) n hH hK'
  b.trans (l.addCommGroupIsoToAddEquiv.trans <|
    (asIso (s.symm.hom.hom.app (op ⊤))).addCommGroupIsoToAddEquiv)

set_option maxHeartbeats 800000 in
/-- The flasque comparison sends a global supported class to its canonical cohomology-sheaf class.
-/
theorem supportHCohomologySheafSectionAddEquivOfFlasque_apply
    (Z : Closeds X) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Sheaf AddCommGrpCat X) 0).obj F ⟶ K) [Mono ι]
      [QuasiIso ι]
    (hK : ∀ n, IsFlasque (K.X n))
    (H : ℕ → Sheaf AddCommGrpCat X)
    (e : ∀ n : ℕ, (((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K).homology
      (n : ℤ) ≅ H n)
    (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero (H j))
    (z : H_[Z]^n(X; F)) :
    supportHCohomologySheafSectionAddEquivOfFlasque X Z F K ι hK H e n hH z =
      supportHToSupportHCohomologySheafSection (Z := Z) F n z := by
  let K' := ((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K
  let p := supportHOnOpenPresheafIsoOfFlasque X Z F K ι hK n
  let s := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso p ≪≫
    sectionCohomologyPresheafSheafificationIso X K' (n : ℤ) ≪≫ e n
  let b := @relHAddEquivSupportedSectionsHomologyOfFlasque X F K (inferInstance : K.IsStrictlyGE 0) ι
    (inferInstance : Mono ι) (inferInstance : QuasiIso ι) Z.compl ⊤ Z.compl
    (top_inf_eq _) hK inferInstance n
  let hK' : ∀ j, (K'.X j).IsFlasque := fun j =>
    letI := hK j
    sheafSectionsSupportedOutside_isFlasque X Z.compl (K.X j)
  let l := lowestSectionCohomologyIsoOfNat X K' (fun j => H j) (fun j => e j) n hH hK'
  let r := CategoryTheory.Sheaf.relH.restrict F
    (homOfLE (le_top : Z.compl ≤ ⊤))
    (homOfLE (inf_le_left : (⊤ : Opens X) ⊓ Z.compl ≤ ⊤))
    (homOfLE (inf_le_right : (⊤ : Opens X) ⊓ Z.compl ≤ Z.compl))
    (homOfLE (le_rfl : (⊤ : Opens X) ≤ ⊤)) (Subsingleton.elim _ _) n
  have hp : (p.hom.app (op ⊤)).hom (r z) =
      (sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) ⊤).hom (b z) := by
    change (sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) ⊤).hom
        ((@relHAddEquivSupportedSectionsHomologyOfFlasque X F K
          (inferInstance : K.IsStrictlyGE 0) ι (inferInstance : Mono ι) (inferInstance : QuasiIso ι)
          Z.compl ⊤ (⊤ ⊓ Z.compl) rfl hK inferInstance n) (r z)) = _
    have hrestrict := relHAddEquivSupportedSectionsHomologyOfFlasque_restrict X
      (U := Z.compl) (V := ⊤) (W := Z.compl)
      (U' := Z.compl) (V' := ⊤) (W' := ⊤ ⊓ Z.compl)
      (hU := le_rfl) (hV := le_rfl) (hW := top_inf_eq _) (hW' := rfl)
      (hWW := inf_le_right) F K ι hK n z
    rw [hrestrict, supportedSectionsRestriction_refl]
    have hsection :
        sectionComplexRestriction X ℤᵘᵖ K'
            (homOfLE (le_rfl : (⊤ : Opens X) ≤ ⊤)) = 𝟙 _ := by
      have h : homOfLE (le_rfl : (⊤ : Opens X) ≤ ⊤) = 𝟙 (⊤ : Opens X) :=
        Subsingleton.elim _ _
      have hnat : supportEvaluationRestriction X (𝟙 (⊤ : Opens X)) =
          𝟙 (supportEvaluation X ⊤) := by
        ext G x
        dsimp [supportEvaluationRestriction]
        have hmap := congrArg AddCommGrpCat.Hom.hom (G.obj.map_id (op ⊤))
        exact (DFunLike.congr_fun hmap x).trans (AddMonoidHom.id_apply _ x)
      rw [h, sectionComplexRestriction, hnat]
      rfl
    rw [hsection, HomologicalComplex.homologyMap_id]
    rfl
  change (s.symm.hom.hom.app (op ⊤)).hom (l.hom (b z)) =
    supportHToSupportHCohomologySheafSection (Z := Z) F n z
  apply (ConcreteCategory.bijective_of_isIso (s.hom.hom.app (op ⊤))).1
  change (s.hom.hom.app (op ⊤)).hom
      ((s.symm.hom.hom.app (op ⊤)).hom (l.hom (b z))) =
    (s.hom.hom.app (op ⊤)).hom
      (((cohomologySheafOfOpensToSheaf X (supportHOnOpenFunctor (Z := Z) F n)).app (op ⊤)).hom
        ((CategoryTheory.Sheaf.relH.restrict F
          (homOfLE (le_top : Z.compl ≤ ⊤))
          (homOfLE (inf_le_left : (⊤ : Opens X) ⊓ Z.compl ≤ ⊤))
          (homOfLE (inf_le_right : (⊤ : Opens X) ⊓ Z.compl ≤ Z.compl))
          (homOfLE (le_rfl : (⊤ : Opens X) ≤ ⊤)) (Subsingleton.elim _ _) n) z))
  rw [← ConcreteCategory.comp_apply]
  simp [s, l, b, K',
    sectionCohomologyToSheafSection, sectionCohomologyPresheafToSheaf,
    lowestSectionCohomologyIsoOfNat,
    Category.assoc, NatTrans.comp_app]
  change (e n).hom.hom.app (op ⊤)
      ((sectionCohomologyPresheafSheafificationIso X K' (n : ℤ)).hom.hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology X)
          (sectionCohomologyPresheaf X K' (n : ℤ))).app (op ⊤)
          ((sectionCohomologyPresheafOnOpenIso X K' (n : ℤ) ⊤).hom (b z)))) =
    (e n).hom.hom.app (op ⊤)
      ((sectionCohomologyPresheafSheafificationIso X K' (n : ℤ)).hom.hom.app (op ⊤)
        (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map p.hom).hom.app
          (op ⊤)
          (((cohomologySheafOfOpensToSheaf X (supportHOnOpenFunctor (Z := Z) F n)).app
            (op ⊤)).hom (r z))))
  congr 1
  congr 1
  have hn := congrArg AddCommGrpCat.Hom.hom
    (congr_app (toSheafify_naturality (Opens.grothendieckTopology X) p.hom) (op ⊤))
  exact (congrArg (fun x =>
    (toSheafify (Opens.grothendieckTopology X)
      (sectionCohomologyPresheaf X K' (n : ℤ))).app (op ⊤) x) hp).symm.trans
    (DFunLike.congr_fun hn (r z))

set_option maxHeartbeats 800000 in
/-- If the restrictions of `H^j` to `V` vanish for `j < n`, this identifies
`H^n(V, V \ Z; F)` with sections on `V` of the supplied degree-`n` cohomology sheaf `H n`. -/
def supportHCohomologySheafSectionAddEquivOfFlasqueOnOpen
    (Z : Closeds X) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor (Sheaf AddCommGrpCat X) 0).obj F ⟶ K) [Mono ι]
      [QuasiIso ι]
    (hK : ∀ n, IsFlasque (K.X n))
    (H : ℕ → Sheaf AddCommGrpCat X)
    (e : ∀ n : ℕ, (((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K).homology
      (n : ℤ) ≅ H n)
    (V W : Opens X) (hW : V ⊓ Z.compl = W) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      ((V.isOpenEmbedding.sheafPullback AddCommGrpCat).obj (H j))) :
    CategoryTheory.Sheaf.relH F n
      (homOfLE (hW ▸ (inf_le_left : V ⊓ Z.compl ≤ V) : W ≤ V)) ≃+
      (supportHCohomologySheaf (Z := Z) F n).presheaf.obj (op V) :=
  let K' := ((sheafSectionsSupportedOutside X Z.compl).mapHomologicalComplex ℤᵘᵖ).obj K
  let p := supportHOnOpenPresheafIsoOfFlasque X Z F K ι hK n
  let s := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso p ≪≫
    sectionCohomologyPresheafSheafificationIso X K' (n : ℤ) ≪≫ e n
  let b := @relHAddEquivSupportedSectionsHomologyOfFlasque X F K (inferInstance : K.IsStrictlyGE 0) ι
    (inferInstance : Mono ι) (inferInstance : QuasiIso ι) Z.compl V W hW hK inferInstance n
  let hK' : ∀ j, (K'.X j).IsFlasque := fun j =>
    letI := hK j
    sheafSectionsSupportedOutside_isFlasque X Z.compl (K.X j)
  let l := openRestrictedLowestSectionCohomologyIsoOfNat X V K'
    (fun j => H j) (fun j => e j) n hH hK'
  b.trans (l.addCommGroupIsoToAddEquiv.trans <|
    (asIso (s.symm.hom.hom.app (op V))).addCommGroupIsoToAddEquiv)

end TopCat.Sheaf

end
