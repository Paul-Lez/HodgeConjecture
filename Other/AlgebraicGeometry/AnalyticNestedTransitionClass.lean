/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticTransitionCoboundary

/-!
# Nested analytic transition classes

Two successive two-open Mayer--Vietoris extensions produce an actual degree-two sheaf
cohomology class.  This is the four-open Cech construction written intrinsically in the
abelian category of analytic sheaves, so no acyclicity hypothesis on the opens is hidden in
the definition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 5000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance nestedTransitionSheafAbelian : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance nestedTransitionHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

/-- The Mayer--Vietoris square for two opens whose union is a specified ambient open. -/
def analyticRelativeCoverMayerVietorisSquare
    (U V W : Opens (TopCat.of (ComplexPoint X))) (hU : U ≤ W) (hV : V ≤ W)
    (hcover : U ⊔ V = W) :
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := U ⊓ V
      X₂ := U
      X₃ := V
      X₄ := W
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE hU
      f₃₄ := homOfLE hV
      fac := Subsingleton.elim _ _ } hcover.symm rfl

/-- The degree-one class on a specified open obtained from a two-open cover of that open. -/
def analyticRelativeTransitionExtClass (F : AnalyticAdditiveSheaf X)
    (A B W : Opens (TopCat.of (ComplexPoint X))) (hA : A ≤ W) (hB : B ≤ W)
    (hcover : A ⊔ B = W) (c : F.obj.obj (.op (A ⊓ B))) :
    Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X W) F 1 :=
  let δ₁ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X W)
      (analyticOpenFreeAbelianSheaf X (A ⊓ B)) 1 :=
    ((analyticRelativeCoverMayerVietorisSquare X A B W hA hB hcover).shortComplex_shortExact).extClass
      (C := AnalyticAdditiveSheaf X)
  let a₁ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (A ⊓ B)) F 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom X F (A ⊓ B) c)
  δ₁.comp a₁ (show 1 + 0 = 1 from rfl)

@[simp]
theorem analyticRelativeTransitionExtClass_zero (F : AnalyticAdditiveSheaf X)
    (A B W : Opens (TopCat.of (ComplexPoint X))) (hA : A ≤ W) (hB : B ≤ W)
    (hcover : A ⊔ B = W) :
    analyticRelativeTransitionExtClass X F A B W hA hB hcover 0 = 0 := by
  simp [analyticRelativeTransitionExtClass]

/-- The overlap difference formula for a two-open cover of an arbitrary ambient open. -/
theorem analyticRelativeMayerVietoris_difference (F : AnalyticAdditiveSheaf X)
    (A B W : Opens (TopCat.of (ComplexPoint X))) (hA : A ≤ W) (hB : B ≤ W)
    (hcover : A ⊔ B = W)
    (a : F.obj.obj (.op A)) (b : F.obj.obj (.op B)) :
    (analyticRelativeCoverMayerVietorisSquare X A B W hA hB hcover).shortComplex.f ≫
      biprod.desc (analyticSectionSheafHom X F A a) (analyticSectionSheafHom X F B b) =
    analyticSectionSheafHom X F (A ⊓ B)
      (F.obj.map (homOfLE inf_le_left).op a -
        F.obj.map (homOfLE inf_le_right).op b) := by
  change biprod.lift (analyticOpenFreeAbelianMap X (homOfLE inf_le_left))
    (-analyticOpenFreeAbelianMap X (homOfLE inf_le_right)) ≫
      biprod.desc (analyticSectionSheafHom X F A a)
        (analyticSectionSheafHom X F B b) = _
  rw [biprod.lift_desc, Preadditive.neg_comp,
    analyticOpenFreeAbelianMap_comp_section,
    analyticOpenFreeAbelianMap_comp_section]
  simpa only [analyticSectionSheafHomAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sub_eq_add_neg] using
      (map_sub (analyticSectionSheafHomAddHom X F (A ⊓ B))
        (F.obj.map (homOfLE inf_le_left).op a)
        (F.obj.map (homOfLE inf_le_right).op b)).symm

/-- A relative transition class vanishes on every actual Cech coboundary. -/
theorem analyticRelativeTransitionExtClass_coboundary (F : AnalyticAdditiveSheaf X)
    (A B W : Opens (TopCat.of (ComplexPoint X))) (hA : A ≤ W) (hB : B ≤ W)
    (hcover : A ⊔ B = W)
    (a : F.obj.obj (.op A)) (b : F.obj.obj (.op B)) :
    analyticRelativeTransitionExtClass X F A B W hA hB hcover
      (F.obj.map (homOfLE inf_le_left).op a -
        F.obj.map (homOfLE inf_le_right).op b) = 0 := by
  unfold analyticRelativeTransitionExtClass
  dsimp only
  rw [← analyticRelativeMayerVietoris_difference X F A B W hA hB hcover a b,
    ← Abelian.Ext.mk₀_comp_mk₀]
  let γ : Abelian.Ext.{1} (C := AnalyticAdditiveSheaf X)
      (analyticRelativeCoverMayerVietorisSquare X A B W hA hB hcover).shortComplex.X₂ F 0 :=
    Abelian.Ext.mk₀ (biprod.desc (analyticSectionSheafHom X F A a)
      (analyticSectionSheafHom X F B b))
  have h :=
    (analyticRelativeCoverMayerVietorisSquare X A B W hA hB hcover).shortComplex_shortExact
      |>.extClass_comp_assoc (C := AnalyticAdditiveSheaf X) γ
        (h := show 1 + 0 = 1 from rfl)
  exact h

/-- A section on the double overlap has zero relative transition class exactly when it is a
difference of restrictions from the two members of the inner cover. -/
theorem analyticRelativeTransitionExtClass_eq_zero_iff (F : AnalyticAdditiveSheaf X)
    (A B W : Opens (TopCat.of (ComplexPoint X))) (hA : A ≤ W) (hB : B ≤ W)
    (hcover : A ⊔ B = W) (c : F.obj.obj (.op (A ⊓ B))) :
    analyticRelativeTransitionExtClass X F A B W hA hB hcover c = 0 ↔
      ∃ (a : F.obj.obj (.op A)) (b : F.obj.obj (.op B)),
        F.obj.map (homOfLE inf_le_left).op a -
          F.obj.map (homOfLE inf_le_right).op b = c := by
  constructor
  · intro hc
    let T : ShortComplex (AnalyticAdditiveSheaf X) :=
      (analyticRelativeCoverMayerVietorisSquare X A B W hA hB hcover).shortComplex
    have hT : T.ShortExact :=
      (analyticRelativeCoverMayerVietorisSquare X A B W hA hB hcover).shortComplex_shortExact
    let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X W)
        (analyticOpenFreeAbelianSheaf X (A ⊓ B)) 1 := hT.extClass
    let γ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (A ⊓ B)) F 0 :=
      Abelian.Ext.mk₀ (analyticSectionSheafHom X F (A ⊓ B) c)
    have hc' : δ.comp γ (show 1 + 0 = 1 from rfl) = 0 := hc
    obtain ⟨γ₂, hγ₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hT F γ
      (show 1 + 0 = 1 from rfl) hc'
    obtain ⟨η, rfl⟩ :=
      (Abelian.Ext.mk₀_bijective (C := AnalyticAdditiveSheaf X) T.X₂ F).surjective γ₂
    have hη : T.f ≫ η = analyticSectionSheafHom X F (A ⊓ B) c := by
      apply (Abelian.Ext.mk₀_bijective
        (C := AnalyticAdditiveSheaf X) T.X₁ F).injective
      simpa only [Abelian.Ext.mk₀_comp_mk₀] using hγ₂
    obtain ⟨a, ha⟩ :=
      (analyticSectionSheafHomEquiv X F A).surjective (biprod.inl ≫ η)
    obtain ⟨b, hb⟩ :=
      (analyticSectionSheafHomEquiv X F B).surjective (biprod.inr ≫ η)
    have hab : biprod.desc (analyticSectionSheafHom X F A a)
        (analyticSectionSheafHom X F B b) = η := by
      apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
      · exact ha
      · exact hb
    refine ⟨a, b, (analyticSectionSheafHomEquiv X F (A ⊓ B)).injective ?_⟩
    change analyticSectionSheafHom X F (A ⊓ B) _ =
      analyticSectionSheafHom X F (A ⊓ B) c
    exact (analyticRelativeMayerVietoris_difference X F A B W hA hB hcover a b).symm.trans
      ((congrArg (fun z : T.X₂ ⟶ F => T.f ≫ z) hab).trans hη)
  · rintro ⟨a, b, rfl⟩
    exact analyticRelativeTransitionExtClass_coboundary X F A B W hA hB hcover a b

/-- A functional on the deepest intersection detects a nonzero relative transition class as
soon as it kills all inner Cech coboundaries. This is the abstract double-residue test. -/
theorem analyticRelativeTransitionExtClass_ne_zero_of_functional
    (F : AnalyticAdditiveSheaf X)
    (A B W : Opens (TopCat.of (ComplexPoint X))) (hA : A ≤ W) (hB : B ≤ W)
    (hcover : A ⊔ B = W) (c : F.obj.obj (.op (A ⊓ B)))
    {G : Type*} [AddCommGroup G]
    (residue : F.obj.obj (.op (A ⊓ B)) →+ G)
    (residue_coboundary : ∀ (a : F.obj.obj (.op A)) (b : F.obj.obj (.op B)),
      residue (F.obj.map (homOfLE inf_le_left).op a -
        F.obj.map (homOfLE inf_le_right).op b) = 0)
    (residue_c : residue c ≠ 0) :
    analyticRelativeTransitionExtClass X F A B W hA hB hcover c ≠ 0 := by
  intro hc
  obtain ⟨a, b, hab⟩ :=
    (analyticRelativeTransitionExtClass_eq_zero_iff X F A B W hA hB hcover c).mp hc
  apply residue_c
  rw [← hab]
  exact residue_coboundary a b

/-- The degree-two extension obtained by covering the whole space by `U,V`, covering their
overlap by `A,B`, and evaluating a target-sheaf section on the double overlap. -/
def analyticNestedTransitionExtClass (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B))) :
    Abelian.Ext.{1} (constantIntegerSheaf X) F 2 :=
  let δ₀ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤)
      (analyticOpenFreeAbelianSheaf X (U ⊓ V)) 1 :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact.extClass
      (C := AnalyticAdditiveSheaf X)
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X)
      (analyticOpenFreeAbelianSheaf X ⊤) 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv
  let β := analyticRelativeTransitionExtClass X F A B (U ⊓ V) hA hB hoverlap c
  a₀.comp (δ₀.comp β
    (show 1 + 1 = 2 from rfl)) (show 0 + 2 = 2 from rfl)

@[simp]
theorem analyticNestedTransitionExtClass_zero (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V) :
    analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap 0 = 0 := by
  simp [analyticNestedTransitionExtClass]

/-- Restriction in degree-one Ext from the two outer opens to their overlap. This is the map
immediately preceding the outer connecting morphism in Mayer--Vietoris. -/
def analyticOuterExtRestriction (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤) :
    Abelian.Ext.{1}
        (analyticOpenFreeAbelianSheaf X U ⊞ analyticOpenFreeAbelianSheaf X V) F 1 →+
      Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1 :=
  (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex.f).precomp F
      (show 0 + 1 = 1 from rfl)

/-- The universal target for a double-residue functional: overlap cohomology modulo classes
which extend from the two outer opens. -/
abbrev analyticOuterExtQuotient (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤) :=
  Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1 ⧸
    (analyticOuterExtRestriction X F U V hcover).range

/-- The canonical universal double residue is the quotient by the outer restriction image. -/
def analyticUniversalDoubleResidue (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤) :
    Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1 →+
      analyticOuterExtQuotient X F U V hcover :=
  QuotientAddGroup.mk' (analyticOuterExtRestriction X F U V hcover).range

/-- The universal double residue vanishes precisely on classes extending from the outer
opens. -/
theorem analyticUniversalDoubleResidue_eq_zero_iff (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (β : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1) :
    analyticUniversalDoubleResidue X F U V hcover β = 0 ↔
      ∃ γ : Abelian.Ext.{1}
          (analyticOpenFreeAbelianSheaf X U ⊞ analyticOpenFreeAbelianSheaf X V) F 1,
        analyticOuterExtRestriction X F U V hcover γ = β := by
  change QuotientAddGroup.mk β = 0 ↔ ∃ γ, analyticOuterExtRestriction X F U V hcover γ = β
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- The nested degree-two class vanishes exactly when its inner transition class comes by
restriction from degree-one classes on the two outer opens.  Thus a four-open Cech
coboundary criterion needs either outer degree-one acyclicity or a functional annihilating
this precise restriction image. -/
theorem analyticNestedTransitionExtClass_eq_zero_iff (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B))) :
    analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap c = 0 ↔
      ∃ γ : Abelian.Ext.{1}
          (analyticOpenFreeAbelianSheaf X U ⊞ analyticOpenFreeAbelianSheaf X V) F 1,
        analyticOuterExtRestriction X F U V hcover γ =
          analyticRelativeTransitionExtClass X F A B (U ⊓ V)
            hA hB hoverlap c := by
  let T : ShortComplex (AnalyticAdditiveSheaf X) :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex
  have hT : T.ShortExact :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact
  let δ : Abelian.Ext.{1} T.X₃ T.X₁ 1 := hT.extClass
  let β : Abelian.Ext.{1} T.X₁ F 1 :=
    analyticRelativeTransitionExtClass X F A B (U ⊓ V) hA hB hoverlap c
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X) T.X₃ 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv
  constructor
  · intro hnested
    have hδβ : δ.comp β (show 1 + 1 = 2 from rfl) = 0 := by
      let z : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤) F 2 :=
        δ.comp β (show 1 + 1 = 2 from rfl)
      have hz : (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
          (analyticTopFreeAbelianSheafIso X).inv).comp z
          (show 0 + 2 = 2 from rfl) = 0 := hnested
      have h := congrArg
        (fun z : Abelian.Ext.{1} (constantIntegerSheaf X) F 2 ↦
          (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
            (analyticTopFreeAbelianSheafIso X).hom).comp z
            (show 0 + 2 = 2 from rfl)) hz
      have hz' : z = 0 := by
        simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
          Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_zero] using h
      change z = 0
      exact hz'
    obtain ⟨γ, hγ⟩ := Abelian.Ext.contravariant_sequence_exact₁ hT F β
      (show 1 + 1 = 2 from rfl) hδβ
    exact ⟨γ, hγ⟩
  · rintro ⟨γ, hγ⟩
    let γ' : Abelian.Ext.{1} T.X₂ F 1 := γ
    have hγ' : (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) T.f).comp γ'
        (show 0 + 1 = 1 from rfl) = β := by
      exact hγ
    unfold analyticNestedTransitionExtClass
    dsimp only
    change a₀.comp (δ.comp β (show 1 + 1 = 2 from rfl))
      (show 0 + 2 = 2 from rfl) = 0
    rw [← hγ']
    rw [hT.extClass_comp_assoc, Abelian.Ext.comp_zero]

/-- The nested class is nonzero exactly when the universal double residue detects its inner
transition class. -/
theorem analyticNestedTransitionExtClass_ne_zero_iff_universalDoubleResidue
    (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B))) :
    analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap c ≠ 0 ↔
      analyticUniversalDoubleResidue X F U V hcover
        (analyticRelativeTransitionExtClass X F A B (U ⊓ V)
          hA hB hoverlap c) ≠ 0 := by
  apply not_congr
  exact (analyticNestedTransitionExtClass_eq_zero_iff X F U V A B
    hcover hA hB hoverlap c).trans
      (analyticUniversalDoubleResidue_eq_zero_iff X F U V hcover _).symm

/-- A functional on the overlap cohomology detects the nested class if it annihilates the
restriction image from the two outer opens and is nonzero on the inner transition class. This
is the long-exact-sequence form of an iterated residue argument. -/
theorem analyticNestedTransitionExtClass_ne_zero_of_ext_functional
    (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B)))
    {G : Type*} [AddCommGroup G]
    (residue :
      Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1 →+ G)
    (residue_outer :
      ∀ γ : Abelian.Ext.{1}
          (analyticOpenFreeAbelianSheaf X U ⊞ analyticOpenFreeAbelianSheaf X V) F 1,
        residue (analyticOuterExtRestriction X F U V hcover γ) = 0)
    (residue_inner : residue
      (analyticRelativeTransitionExtClass X F A B (U ⊓ V) hA hB hoverlap c) ≠ 0) :
    analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap c ≠ 0 := by
  intro hnested
  let T : ShortComplex (AnalyticAdditiveSheaf X) :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex
  have hT : T.ShortExact :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact
  let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤)
      (analyticOpenFreeAbelianSheaf X (U ⊓ V)) 1 := hT.extClass
  let β : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1 :=
    analyticRelativeTransitionExtClass X F A B (U ⊓ V) hA hB hoverlap c
  have hδβ : δ.comp β (show 1 + 1 = 2 from rfl) = 0 := by
    have h := congrArg
      (fun z : Abelian.Ext.{1} (constantIntegerSheaf X) F 2 =>
        (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
          (analyticTopFreeAbelianSheafIso X).hom).comp z
          (show 0 + 2 = 2 from rfl)) hnested
    change (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
      (analyticTopFreeAbelianSheafIso X).hom).comp
      ((Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
        (analyticTopFreeAbelianSheafIso X).inv).comp
        (δ.comp β (show 1 + 1 = 2 from rfl))
        (show 0 + 2 = 2 from rfl)) (show 0 + 2 = 2 from rfl) = _ at h
    simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
      Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_zero] using h
  obtain ⟨γ, hγ⟩ := Abelian.Ext.contravariant_sequence_exact₁ hT F β
    (show 1 + 1 = 2 from rfl) hδβ
  apply residue_inner
  change residue β = 0
  rw [← hγ]
  exact residue_outer γ

/-- Vanishing of degree-one cohomology on each outer open makes the outer connecting map
injective. Hence any nonzero inner transition class gives a nonzero nested degree-two class. -/
theorem analyticNestedTransitionExtClass_ne_zero_of_outer_ext_vanishing
    (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B)))
    (hU : ∀ γ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X U) F 1, γ = 0)
    (hV : ∀ γ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X V) F 1, γ = 0)
    (hinner : analyticRelativeTransitionExtClass X F A B (U ⊓ V)
      hA hB hoverlap c ≠ 0) :
    analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap c ≠ 0 := by
  apply analyticNestedTransitionExtClass_ne_zero_of_ext_functional X F U V A B
    hcover hA hB hoverlap c
    (residue := AddMonoidHom.id
      (Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1))
  · intro γ
    change analyticOuterExtRestriction X F U V hcover γ = 0
    have hγ : γ = 0 := by
      apply Abelian.Ext.biprod_ext
      · simpa using hU ((Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) biprod.inl).comp γ
          (show 0 + 1 = 1 from rfl))
      · simpa using hV ((Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) biprod.inr).comp γ
          (show 0 + 1 = 1 from rfl))
    rw [hγ, map_zero]
  · exact hinner

/-- A concrete deepest-intersection functional, together with degree-one acyclicity of the two
outer opens, is sufficient to prove nonvanishing of the nested degree-two class. -/
theorem analyticNestedTransitionExtClass_ne_zero_of_section_functional
    (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B)))
    {G : Type*} [AddCommGroup G]
    (residue : F.obj.obj (.op (A ⊓ B)) →+ G)
    (residue_coboundary : ∀ (a : F.obj.obj (.op A)) (b : F.obj.obj (.op B)),
      residue (F.obj.map (homOfLE inf_le_left).op a -
        F.obj.map (homOfLE inf_le_right).op b) = 0)
    (residue_c : residue c ≠ 0)
    (hU : ∀ γ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X U) F 1, γ = 0)
    (hV : ∀ γ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X V) F 1, γ = 0) :
    analyticNestedTransitionExtClass X F U V A B hcover hA hB hoverlap c ≠ 0 := by
  apply analyticNestedTransitionExtClass_ne_zero_of_outer_ext_vanishing X F U V A B
    hcover hA hB hoverlap c hU hV
  exact analyticRelativeTransitionExtClass_ne_zero_of_functional X F A B (U ⊓ V)
    hA hB hoverlap c residue residue_coboundary residue_c

end AlgebraicGeometry.ComplexPoint
