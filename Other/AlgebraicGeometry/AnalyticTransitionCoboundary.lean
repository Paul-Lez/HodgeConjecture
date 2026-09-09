/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicTransitionClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Independence of holomorphic transition classes under trivialization

The actual Mayer–Vietoris class of a difference of restrictions vanishes. Consequently a
holomorphic transition function obtained from units on the two opens has zero exponential
class. All maps are maps of the analytic sheaves of the variety.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 5000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance transitionCoboundarySheafAbelian : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance transitionCoboundaryHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) :=
  analyticHasExt X

/-- Inclusion of opens induces the corresponding morphism of free abelian sheaves. -/
def analyticOpenFreeAbelianMap {U V : Opens (TopCat.of (ComplexPoint X))} (i : U ⟶ V) :
    analyticOpenFreeAbelianSheaf X U ⟶ analyticOpenFreeAbelianSheaf X V :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    AddCommGrpCat).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

/-- The represented presheaf morphism is additive in its section. -/
theorem analyticSectionPresheafHom_add (F : AnalyticAdditiveSheaf X)
    (U : Opens (TopCat.of (ComplexPoint X))) (a b : F.obj.obj (.op U)) :
    analyticSectionPresheafHom X F U (a + b) =
      analyticSectionPresheafHom X F U a + analyticSectionPresheafHom X F U b := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro f
  change FreeAbelianGroup.lift (fun g : V.unop ⟶ U => F.obj.map g.op (a + b))
      (FreeAbelianGroup.of f) =
    FreeAbelianGroup.lift (fun g : V.unop ⟶ U => F.obj.map g.op a) (FreeAbelianGroup.of f) +
      FreeAbelianGroup.lift (fun g : V.unop ⟶ U => F.obj.map g.op b) (FreeAbelianGroup.of f)
  simp

/-- The represented sheaf morphism is additive in its section. -/
theorem analyticSectionSheafHom_add (F : AnalyticAdditiveSheaf X)
    (U : Opens (TopCat.of (ComplexPoint X))) (a b : F.obj.obj (.op U)) :
    analyticSectionSheafHom X F U (a + b) =
      analyticSectionSheafHom X F U a + analyticSectionSheafHom X F U b := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) _ _ F.property
  change toSheafify _ _ ≫ sheafifyLift _ (analyticSectionPresheafHom X F U (a + b)) F.property =
    toSheafify _ _ ≫ (sheafifyLift _ (analyticSectionPresheafHom X F U a) F.property +
      sheafifyLift _ (analyticSectionPresheafHom X F U b) F.property)
  rw [Preadditive.comp_add, toSheafify_sheafifyLift, toSheafify_sheafifyLift,
    toSheafify_sheafifyLift, analyticSectionPresheafHom_add]

/-- Sections identify additively with represented maps into the sheaf. -/
def analyticSectionSheafHomAddHom (F : AnalyticAdditiveSheaf X)
    (U : Opens (TopCat.of (ComplexPoint X))) :
    F.obj.obj (.op U) →+ (analyticOpenFreeAbelianSheaf X U ⟶ F) where
  toFun := analyticSectionSheafHom X F U
  map_zero' := analyticSectionSheafHom_zero X F U
  map_add' := analyticSectionSheafHom_add X F U

/-- A morphism from the free presheaf is determined by its value on the identity generator. -/
theorem analyticSectionPresheafHom_of_generator (F : AnalyticAdditiveSheaf X)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (η : analyticOpenFreeAbelianPresheaf X U ⟶ F.obj) :
    analyticSectionPresheafHom X F U (η.app (.op U) (FreeAbelianGroup.of (𝟙 U))) = η := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro g
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of g) = η.app V (FreeAbelianGroup.of g)
  rw [FreeAbelianGroup.lift_apply_of]
  have h := congrArg (fun k => k (FreeAbelianGroup.of (𝟙 U))) (η.naturality g.op)
  change η.app V (FreeAbelianGroup.map (fun f : U ⟶ U => g ≫ f)
      (FreeAbelianGroup.of (𝟙 U))) =
    F.obj.map g.op (η.app (.op U) (FreeAbelianGroup.of (𝟙 U))) at h
  simpa only [FreeAbelianGroup.map, FreeAbelianGroup.lift_apply_of, Function.comp_apply,
    Category.comp_id] using h.symm

/-- Every morphism from the free sheaf is represented by its actual generator section. -/
theorem analyticSectionSheafHom_of_generator (F : AnalyticAdditiveSheaf X)
    (U : Opens (TopCat.of (ComplexPoint X))) (η : analyticOpenFreeAbelianSheaf X U ⟶ F) :
    analyticSectionSheafHom X F U
      (η.hom.app (.op U) ((toSheafify (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (analyticOpenFreeAbelianPresheaf X U)).app (.op U)
          (FreeAbelianGroup.of (𝟙 U)))) = η := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) _ _ F.property
  change toSheafify _ _ ≫ sheafifyLift _ _ F.property = toSheafify _ _ ≫ η.hom
  rw [toSheafify_sheafifyLift]
  exact analyticSectionPresheafHom_of_generator X F U (toSheafify _ _ ≫ η.hom)

/-- The actual sections of a sheaf are additively equivalent to maps from the free open sheaf. -/
def analyticSectionSheafHomEquiv (F : AnalyticAdditiveSheaf X)
    (U : Opens (TopCat.of (ComplexPoint X))) :
    F.obj.obj (.op U) ≃+ (analyticOpenFreeAbelianSheaf X U ⟶ F) :=
  AddEquiv.ofBijective (analyticSectionSheafHomAddHom X F U) ⟨by
    intro a b h
    have h' := congrArg (fun η : analyticOpenFreeAbelianSheaf X U ⟶ F =>
      η.hom.app (.op U) ((toSheafify (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (analyticOpenFreeAbelianPresheaf X U)).app (.op U)
          (FreeAbelianGroup.of (𝟙 U)))) h
    exact (analyticSectionSheafHom_generator X F U a).symm.trans
      (h'.trans (analyticSectionSheafHom_generator X F U b)), by
    intro η
    exact ⟨_, analyticSectionSheafHom_of_generator X F U η⟩⟩

/-- Applying a sheaf morphism to a section is postcomposition of its represented map. -/
theorem analyticSectionSheafHom_postcomp (F G : AnalyticAdditiveSheaf X) (f : F ⟶ G)
    (U : Opens (TopCat.of (ComplexPoint X))) (a : F.obj.obj (.op U)) :
    analyticSectionSheafHom X F U a ≫ f =
      analyticSectionSheafHom X G U (f.hom.app (.op U) a) := by
  exact (analyticSectionSheafHom_of_generator X G U
    (analyticSectionSheafHom X F U a ≫ f)).symm.trans
      (congrArg (analyticSectionSheafHom X G U)
        (congrArg (fun x => f.hom.app (.op U) x) (analyticSectionSheafHom_generator X F U a)))

/-- Restricting a section is precomposition with the actual map of free sheaves. -/
theorem analyticOpenFreeAbelianMap_comp_section (F : AnalyticAdditiveSheaf X)
    {U V : Opens (TopCat.of (ComplexPoint X))} (i : U ⟶ V) (a : F.obj.obj (.op V)) :
    analyticOpenFreeAbelianMap X i ≫ analyticSectionSheafHom X F V a =
      analyticSectionSheafHom X F U (F.obj.map i.op a) := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  change sheafifyMap _ _ ≫ sheafifyLift _ _ F.property = sheafifyLift _ _ F.property
  rw [sheafifyMap_sheafifyLift]
  congr 1
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro f
  change FreeAbelianGroup.lift (fun g : W.unop ⟶ V => F.obj.map g.op a)
    (FreeAbelianGroup.map (fun g : W.unop ⟶ U => g ≫ i) (FreeAbelianGroup.of f)) =
      FreeAbelianGroup.lift (fun g : W.unop ⟶ U => F.obj.map g.op (F.obj.map i.op a))
        (FreeAbelianGroup.of f)
  simp only [FreeAbelianGroup.map, FreeAbelianGroup.lift_apply_of, Function.comp_apply]
  exact congrArg (fun h => h a) (F.obj.map_comp i.op f.op)

/-- The overlap difference of two sections factors through the Mayer–Vietoris boundary. -/
theorem analyticMayerVietoris_difference (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)) :
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex.f ≫
      biprod.desc (analyticSectionSheafHom X F U a) (analyticSectionSheafHom X F V b) =
    analyticSectionSheafHom X F (U ⊓ V)
      (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b) := by
  change biprod.lift (analyticOpenFreeAbelianMap X (homOfLE inf_le_left))
    (-analyticOpenFreeAbelianMap X (homOfLE inf_le_right)) ≫
      biprod.desc (analyticSectionSheafHom X F U a) (analyticSectionSheafHom X F V b) = _
  rw [biprod.lift_desc, Preadditive.neg_comp, analyticOpenFreeAbelianMap_comp_section,
    analyticOpenFreeAbelianMap_comp_section]
  simpa only [analyticSectionSheafHomAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sub_eq_add_neg] using
      (map_sub (analyticSectionSheafHomAddHom X F (U ⊓ V))
        (F.obj.map (homOfLE inf_le_left).op a) (F.obj.map (homOfLE inf_le_right).op b)).symm

/-- The actual extension class of an overlap coboundary is zero. -/
theorem analyticTransitionExtClass_coboundary (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)) :
    analyticTransitionExtClass X F U V hcover
      (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b) = 0 := by
  unfold analyticTransitionExtClass
  dsimp only
  rw [← analyticMayerVietoris_difference X F U V hcover a b,
    ← Abelian.Ext.mk₀_comp_mk₀]
  let γ : Abelian.Ext.{1} (C := AnalyticAdditiveSheaf X)
      (analyticCoverMayerVietorisSquare X U V hcover).shortComplex.X₂ F 0 :=
    Abelian.Ext.mk₀ (biprod.desc (analyticSectionSheafHom X F U a)
      (analyticSectionSheafHom X F V b))
  have h := (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact.extClass_comp_assoc
    (C := AnalyticAdditiveSheaf X) γ (h := show 1 + 0 = 1 from rfl)
  rw [h, Abelian.Ext.comp_zero]

/-- Addition of overlap sections is addition of their actual extension classes. -/
theorem analyticTransitionExtClass_add (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (a b : F.obj.obj (.op (U ⊓ V))) :
    analyticTransitionExtClass X F U V hcover (a + b) =
      analyticTransitionExtClass X F U V hcover a +
        analyticTransitionExtClass X F U V hcover b := by
  let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤)
      (analyticOpenFreeAbelianSheaf X (U ⊓ V)) 1 :=
    (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact.extClass
      (C := AnalyticAdditiveSheaf X)
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf X) (analyticOpenFreeAbelianSheaf X ⊤) 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv
  change a₀.comp (δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom X F (U ⊓ V) (a + b)))
    (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl) =
    a₀.comp (δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom X F (U ⊓ V) a))
      (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl) +
    a₀.comp (δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom X F (U ⊓ V) b))
      (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl)
  rw [analyticSectionSheafHom_add, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add,
    Abelian.Ext.comp_add]

/-- Adding an actual overlap coboundary does not change the extension class. -/
theorem analyticTransitionExtClass_add_coboundary (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (c : F.obj.obj (.op (U ⊓ V))) (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)) :
    analyticTransitionExtClass X F U V hcover
      (c + (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b)) =
        analyticTransitionExtClass X F U V hcover c := by
  rw [analyticTransitionExtClass_add, analyticTransitionExtClass_coboundary, add_zero]

/-- An actual overlap section has zero Mayer–Vietoris class exactly when it is a difference
of actual sections on the two opens. This does not require acyclicity of the cover. -/
theorem analyticTransitionExtClass_eq_zero_iff (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (c : F.obj.obj (.op (U ⊓ V))) :
    analyticTransitionExtClass X F U V hcover c = 0 ↔
      ∃ (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)),
        F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b = c := by
  constructor
  · intro hc
    let T : ShortComplex (AnalyticAdditiveSheaf X) :=
      (analyticCoverMayerVietorisSquare X U V hcover).shortComplex
    have hT : T.ShortExact :=
      (analyticCoverMayerVietorisSquare X U V hcover).shortComplex_shortExact
    let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X ⊤)
        (analyticOpenFreeAbelianSheaf X (U ⊓ V)) 1 := hT.extClass
    let γ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 0 :=
      Abelian.Ext.mk₀ (analyticSectionSheafHom X F (U ⊓ V) c)
    have hc' : δ.comp γ (show 1 + 0 = 1 from rfl) = 0 := by
      have h := congrArg (fun z : Abelian.Ext.{1} (constantIntegerSheaf X) F 1 =>
        (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).hom).comp z (show 0 + 1 = 1 from rfl)) hc
      change (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).hom).comp
        ((Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso X).inv).comp (δ.comp γ
          (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl))
            (show 0 + 1 = 1 from rfl) = _ at h
      simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Abelian.Ext.mk₀_id_comp,
        Abelian.Ext.comp_zero] using h
    obtain ⟨γ₂, hγ₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hT F γ
      (show 1 + 0 = 1 from rfl) hc'
    obtain ⟨η, rfl⟩ := (Abelian.Ext.mk₀_bijective (C := AnalyticAdditiveSheaf X) T.X₂ F).surjective γ₂
    have hη : T.f ≫ η = analyticSectionSheafHom X F (U ⊓ V) c := by
      apply (Abelian.Ext.mk₀_bijective (C := AnalyticAdditiveSheaf X) T.X₁ F).injective
      simpa only [Abelian.Ext.mk₀_comp_mk₀] using hγ₂
    obtain ⟨a, ha⟩ := (analyticSectionSheafHomEquiv X F U).surjective (biprod.inl ≫ η)
    obtain ⟨b, hb⟩ := (analyticSectionSheafHomEquiv X F V).surjective (biprod.inr ≫ η)
    have hab : biprod.desc (analyticSectionSheafHom X F U a)
        (analyticSectionSheafHom X F V b) = η := by
      apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
      · exact ha
      · exact hb
    refine ⟨a, b, (analyticSectionSheafHomEquiv X F (U ⊓ V)).injective ?_⟩
    change analyticSectionSheafHom X F (U ⊓ V) _ = analyticSectionSheafHom X F (U ⊓ V) c
    exact (analyticMayerVietoris_difference X F U V hcover a b).symm.trans
      ((congrArg (fun z : T.X₂ ⟶ F => T.f ≫ z) hab).trans hη)
  · rintro ⟨a, b, rfl⟩
    exact analyticTransitionExtClass_coboundary X F U V hcover a b

variable [IsIntegral X.left] [Smooth X.hom]

/-- A transition function has zero units cohomology class exactly when actual units on the
two opens trivialize it. The criterion refers to the variety's actual analytic sheaf. -/
theorem holomorphicTransitionUnitsClass_eq_zero_iff
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ) :
    holomorphicTransitionUnitsClass X U V hcover u = 0 ↔
      ∃ (a : (OpenHolomorphicFunctions X (dim X.left) (.op U))ˣ)
        (b : (OpenHolomorphicFunctions X (dim X.left) (.op V))ˣ),
        Units.map (holomorphicRestrictionAlgHom X (dim X.left)
          (homOfLE inf_le_left).op).toMonoidHom a /
            Units.map (holomorphicRestrictionAlgHom X (dim X.left)
              (homOfLE inf_le_right).op).toMonoidHom b = u := by
  unfold holomorphicTransitionUnitsClass
  rw [← sheafExtHypercohomologyEquiv_zero X (holomorphicUnitsSheaf X (dim X.left)) 1 1,
    (sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 1 1).injective.eq_iff]
  exact analyticTransitionExtClass_eq_zero_iff X (holomorphicUnitsSheaf X (dim X.left))
    U V hcover (Additive.ofMul u)

/-- Changing trivializations on the two opens leaves the actual units class unchanged. -/
theorem holomorphicTransitionUnitsClass_changeTrivialization
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ)
    (a : (OpenHolomorphicFunctions X (dim X.left) (.op U))ˣ)
    (b : (OpenHolomorphicFunctions X (dim X.left) (.op V))ˣ) :
    holomorphicTransitionUnitsClass X U V hcover
      (u * (Units.map (holomorphicRestrictionAlgHom X (dim X.left)
        (homOfLE inf_le_left).op).toMonoidHom a /
          Units.map (holomorphicRestrictionAlgHom X (dim X.left)
            (homOfLE inf_le_right).op).toMonoidHom b)) =
      holomorphicTransitionUnitsClass X U V hcover u := by
  unfold holomorphicTransitionUnitsClass
  congr 1
  exact analyticTransitionExtClass_add_coboundary X (holomorphicUnitsSheaf X (dim X.left))
    U V hcover (Additive.ofMul u) (Additive.ofMul a) (Additive.ofMul b)

/-- Changing local trivializations leaves the integral exponential class unchanged. -/
theorem integralHolomorphicTransitionClass_changeTrivialization
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ)
    (a : (OpenHolomorphicFunctions X (dim X.left) (.op U))ˣ)
    (b : (OpenHolomorphicFunctions X (dim X.left) (.op V))ˣ) :
    integralHolomorphicTransitionClass X U V hcover
      (u * (Units.map (holomorphicRestrictionAlgHom X (dim X.left)
        (homOfLE inf_le_left).op).toMonoidHom a /
          Units.map (holomorphicRestrictionAlgHom X (dim X.left)
            (homOfLE inf_le_right).op).toMonoidHom b)) =
      integralHolomorphicTransitionClass X U V hcover u := by
  unfold integralHolomorphicTransitionClass
  rw [holomorphicTransitionUnitsClass_changeTrivialization]

/-- Changing local trivializations leaves the rational Hodge class unchanged. -/
theorem rationalHolomorphicTransitionClass_changeTrivialization
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions X (dim X.left) (.op (U ⊓ V)))ˣ)
    (a : (OpenHolomorphicFunctions X (dim X.left) (.op U))ˣ)
    (b : (OpenHolomorphicFunctions X (dim X.left) (.op V))ˣ) :
    rationalHolomorphicTransitionClass X U V hcover
      (u * (Units.map (holomorphicRestrictionAlgHom X (dim X.left)
        (homOfLE inf_le_left).op).toMonoidHom a /
          Units.map (holomorphicRestrictionAlgHom X (dim X.left)
            (homOfLE inf_le_right).op).toMonoidHom b)) =
      rationalHolomorphicTransitionClass X U V hcover u := by
  unfold rationalHolomorphicTransitionClass
  rw [holomorphicTransitionUnitsClass_changeTrivialization]

end AlgebraicGeometry.ComplexPoint
