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

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

local instance transitionCoboundarySheafAbelian : Abelian (AnalyticAdditiveSheaf s) :=
  CategoryTheory.sheafIsAbelian

local instance transitionCoboundaryHasExt : HasExt.{1} (AnalyticAdditiveSheaf s) :=
  analyticHasExt s

/-- Inclusion of opens induces the corresponding morphism of free abelian sheaves. -/
def analyticOpenFreeAbelianMap {U V : Opens (TopCat.of (ComplexPoint X s))} (i : U ⟶ V) :
    analyticOpenFreeAbelianSheaf s U ⟶ analyticOpenFreeAbelianSheaf s V :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
    AddCommGrpCat).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

/-- The represented presheaf morphism is additive in its section. -/
theorem analyticSectionPresheafHom_add (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) (a b : F.obj.obj (.op U)) :
    analyticSectionPresheafHom s F U (a + b) =
      analyticSectionPresheafHom s F U a + analyticSectionPresheafHom s F U b := by
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
theorem analyticSectionSheafHom_add (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) (a b : F.obj.obj (.op U)) :
    analyticSectionSheafHom s F U (a + b) =
      analyticSectionSheafHom s F U a + analyticSectionSheafHom s F U b := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) _ _ F.property
  change toSheafify _ _ ≫ sheafifyLift _ (analyticSectionPresheafHom s F U (a + b)) F.property =
    toSheafify _ _ ≫ (sheafifyLift _ (analyticSectionPresheafHom s F U a) F.property +
      sheafifyLift _ (analyticSectionPresheafHom s F U b) F.property)
  rw [Preadditive.comp_add, toSheafify_sheafifyLift, toSheafify_sheafifyLift,
    toSheafify_sheafifyLift, analyticSectionPresheafHom_add]

/-- Sections identify additively with represented maps into the sheaf. -/
def analyticSectionSheafHomAddHom (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) :
    F.obj.obj (.op U) →+ (analyticOpenFreeAbelianSheaf s U ⟶ F) where
  toFun := analyticSectionSheafHom s F U
  map_zero' := analyticSectionSheafHom_zero s F U
  map_add' := analyticSectionSheafHom_add s F U

/-- A morphism from the free presheaf is determined by its value on the identity generator. -/
theorem analyticSectionPresheafHom_of_generator (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s)))
    (η : analyticOpenFreeAbelianPresheaf s U ⟶ F.obj) :
    analyticSectionPresheafHom s F U (η.app (.op U) (FreeAbelianGroup.of (𝟙 U))) = η := by
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
theorem analyticSectionSheafHom_of_generator (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) (η : analyticOpenFreeAbelianSheaf s U ⟶ F) :
    analyticSectionSheafHom s F U
      (η.hom.app (.op U) ((toSheafify (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X s))) (analyticOpenFreeAbelianPresheaf s U)).app (.op U)
          (FreeAbelianGroup.of (𝟙 U)))) = η := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) _ _ F.property
  change toSheafify _ _ ≫ sheafifyLift _ _ F.property = toSheafify _ _ ≫ η.hom
  rw [toSheafify_sheafifyLift]
  exact analyticSectionPresheafHom_of_generator s F U (toSheafify _ _ ≫ η.hom)

/-- The actual sections of a sheaf are additively equivalent to maps from the free open sheaf. -/
def analyticSectionSheafHomEquiv (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) :
    F.obj.obj (.op U) ≃+ (analyticOpenFreeAbelianSheaf s U ⟶ F) :=
  AddEquiv.ofBijective (analyticSectionSheafHomAddHom s F U) ⟨by
    intro a b h
    have h' := congrArg (fun η : analyticOpenFreeAbelianSheaf s U ⟶ F =>
      η.hom.app (.op U) ((toSheafify (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X s))) (analyticOpenFreeAbelianPresheaf s U)).app (.op U)
          (FreeAbelianGroup.of (𝟙 U)))) h
    exact (analyticSectionSheafHom_generator s F U a).symm.trans
      (h'.trans (analyticSectionSheafHom_generator s F U b)), by
    intro η
    exact ⟨_, analyticSectionSheafHom_of_generator s F U η⟩⟩

/-- Applying a sheaf morphism to a section is postcomposition of its represented map. -/
theorem analyticSectionSheafHom_postcomp (F G : AnalyticAdditiveSheaf s) (f : F ⟶ G)
    (U : Opens (TopCat.of (ComplexPoint X s))) (a : F.obj.obj (.op U)) :
    analyticSectionSheafHom s F U a ≫ f =
      analyticSectionSheafHom s G U (f.hom.app (.op U) a) := by
  exact (analyticSectionSheafHom_of_generator s G U
    (analyticSectionSheafHom s F U a ≫ f)).symm.trans
      (congrArg (analyticSectionSheafHom s G U)
        (congrArg (fun x => f.hom.app (.op U) x) (analyticSectionSheafHom_generator s F U a)))

/-- Restricting a section is precomposition with the actual map of free sheaves. -/
theorem analyticOpenFreeAbelianMap_comp_section (F : AnalyticAdditiveSheaf s)
    {U V : Opens (TopCat.of (ComplexPoint X s))} (i : U ⟶ V) (a : F.obj.obj (.op V)) :
    analyticOpenFreeAbelianMap s i ≫ analyticSectionSheafHom s F V a =
      analyticSectionSheafHom s F U (F.obj.map i.op a) := by
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
theorem analyticMayerVietoris_difference (F : AnalyticAdditiveSheaf s)
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)) :
    (analyticCoverMayerVietorisSquare s U V hcover).shortComplex.f ≫
      biprod.desc (analyticSectionSheafHom s F U a) (analyticSectionSheafHom s F V b) =
    analyticSectionSheafHom s F (U ⊓ V)
      (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b) := by
  change biprod.lift (analyticOpenFreeAbelianMap s (homOfLE inf_le_left))
    (-analyticOpenFreeAbelianMap s (homOfLE inf_le_right)) ≫
      biprod.desc (analyticSectionSheafHom s F U a) (analyticSectionSheafHom s F V b) = _
  rw [biprod.lift_desc, Preadditive.neg_comp, analyticOpenFreeAbelianMap_comp_section,
    analyticOpenFreeAbelianMap_comp_section]
  simpa only [analyticSectionSheafHomAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sub_eq_add_neg] using
      (map_sub (analyticSectionSheafHomAddHom s F (U ⊓ V))
        (F.obj.map (homOfLE inf_le_left).op a) (F.obj.map (homOfLE inf_le_right).op b)).symm

/-- The actual extension class of an overlap coboundary is zero. -/
theorem analyticTransitionExtClass_coboundary (F : AnalyticAdditiveSheaf s)
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)) :
    analyticTransitionExtClass s F U V hcover
      (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b) = 0 := by
  unfold analyticTransitionExtClass
  dsimp only
  rw [← analyticMayerVietoris_difference s F U V hcover a b,
    ← Abelian.Ext.mk₀_comp_mk₀]
  let γ : Abelian.Ext.{1} (C := AnalyticAdditiveSheaf s)
      (analyticCoverMayerVietorisSquare s U V hcover).shortComplex.X₂ F 0 :=
    Abelian.Ext.mk₀ (biprod.desc (analyticSectionSheafHom s F U a)
      (analyticSectionSheafHom s F V b))
  have h := (analyticCoverMayerVietorisSquare s U V hcover).shortComplex_shortExact.extClass_comp_assoc
    (C := AnalyticAdditiveSheaf s) γ (h := show 1 + 0 = 1 from rfl)
  rw [h, Abelian.Ext.comp_zero]

/-- Addition of overlap sections is addition of their actual extension classes. -/
theorem analyticTransitionExtClass_add (F : AnalyticAdditiveSheaf s)
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (a b : F.obj.obj (.op (U ⊓ V))) :
    analyticTransitionExtClass s F U V hcover (a + b) =
      analyticTransitionExtClass s F U V hcover a +
        analyticTransitionExtClass s F U V hcover b := by
  let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s ⊤)
      (analyticOpenFreeAbelianSheaf s (U ⊓ V)) 1 :=
    (analyticCoverMayerVietorisSquare s U V hcover).shortComplex_shortExact.extClass
      (C := AnalyticAdditiveSheaf s)
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf s) (analyticOpenFreeAbelianSheaf s ⊤) 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso s).inv
  change a₀.comp (δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom s F (U ⊓ V) (a + b)))
    (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl) =
    a₀.comp (δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom s F (U ⊓ V) a))
      (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl) +
    a₀.comp (δ.comp (Abelian.Ext.mk₀ (analyticSectionSheafHom s F (U ⊓ V) b))
      (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl)
  rw [analyticSectionSheafHom_add, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add,
    Abelian.Ext.comp_add]

/-- Adding an actual overlap coboundary does not change the extension class. -/
theorem analyticTransitionExtClass_add_coboundary (F : AnalyticAdditiveSheaf s)
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (c : F.obj.obj (.op (U ⊓ V))) (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)) :
    analyticTransitionExtClass s F U V hcover
      (c + (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b)) =
        analyticTransitionExtClass s F U V hcover c := by
  rw [analyticTransitionExtClass_add, analyticTransitionExtClass_coboundary, add_zero]

/-- An actual overlap section has zero Mayer–Vietoris class exactly when it is a difference
of actual sections on the two opens. This does not require acyclicity of the cover. -/
theorem analyticTransitionExtClass_eq_zero_iff (F : AnalyticAdditiveSheaf s)
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (c : F.obj.obj (.op (U ⊓ V))) :
    analyticTransitionExtClass s F U V hcover c = 0 ↔
      ∃ (a : F.obj.obj (.op U)) (b : F.obj.obj (.op V)),
        F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b = c := by
  constructor
  · intro hc
    let T : ShortComplex (AnalyticAdditiveSheaf s) :=
      (analyticCoverMayerVietorisSquare s U V hcover).shortComplex
    have hT : T.ShortExact :=
      (analyticCoverMayerVietorisSquare s U V hcover).shortComplex_shortExact
    let δ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s ⊤)
        (analyticOpenFreeAbelianSheaf s (U ⊓ V)) 1 := hT.extClass
    let γ : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf s (U ⊓ V)) F 0 :=
      Abelian.Ext.mk₀ (analyticSectionSheafHom s F (U ⊓ V) c)
    have hc' : δ.comp γ (show 1 + 0 = 1 from rfl) = 0 := by
      have h := congrArg (fun z : Abelian.Ext.{1} (constantIntegerSheaf s) F 1 =>
        (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso s).hom).comp z (show 0 + 1 = 1 from rfl)) hc
      change (Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso s).hom).comp
        ((Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso s).inv).comp (δ.comp γ
          (show 1 + 0 = 1 from rfl)) (show 0 + 1 = 1 from rfl))
            (show 0 + 1 = 1 from rfl) = _ at h
      simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Abelian.Ext.mk₀_id_comp,
        Abelian.Ext.comp_zero] using h
    obtain ⟨γ₂, hγ₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hT F γ
      (show 1 + 0 = 1 from rfl) hc'
    obtain ⟨η, rfl⟩ := (Abelian.Ext.mk₀_bijective (C := AnalyticAdditiveSheaf s) T.X₂ F).surjective γ₂
    have hη : T.f ≫ η = analyticSectionSheafHom s F (U ⊓ V) c := by
      apply (Abelian.Ext.mk₀_bijective (C := AnalyticAdditiveSheaf s) T.X₁ F).injective
      simpa only [Abelian.Ext.mk₀_comp_mk₀] using hγ₂
    obtain ⟨a, ha⟩ := (analyticSectionSheafHomEquiv s F U).surjective (biprod.inl ≫ η)
    obtain ⟨b, hb⟩ := (analyticSectionSheafHomEquiv s F V).surjective (biprod.inr ≫ η)
    have hab : biprod.desc (analyticSectionSheafHom s F U a)
        (analyticSectionSheafHom s F V b) = η := by
      apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
      · exact ha
      · exact hb
    refine ⟨a, b, (analyticSectionSheafHomEquiv s F (U ⊓ V)).injective ?_⟩
    change analyticSectionSheafHom s F (U ⊓ V) _ = analyticSectionSheafHom s F (U ⊓ V) c
    exact (analyticMayerVietoris_difference s F U V hcover a b).symm.trans
      ((congrArg (fun z : T.X₂ ⟶ F => T.f ≫ z) hab).trans hη)
  · rintro ⟨a, b, rfl⟩
    exact analyticTransitionExtClass_coboundary s F U V hcover a b

variable [IsIntegral X] [Smooth s]

/-- A transition function has zero units cohomology class exactly when actual units on the
two opens trivialize it. The criterion refers to the variety's actual analytic sheaf. -/
theorem holomorphicTransitionUnitsClass_eq_zero_iff
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions s (dim X) (.op (U ⊓ V)))ˣ) :
    holomorphicTransitionUnitsClass s U V hcover u = 0 ↔
      ∃ (a : (OpenHolomorphicFunctions s (dim X) (.op U))ˣ)
        (b : (OpenHolomorphicFunctions s (dim X) (.op V))ˣ),
        Units.map (holomorphicRestrictionAlgHom s (dim X)
          (homOfLE inf_le_left).op).toMonoidHom a /
            Units.map (holomorphicRestrictionAlgHom s (dim X)
              (homOfLE inf_le_right).op).toMonoidHom b = u := by
  unfold holomorphicTransitionUnitsClass
  rw [← sheafExtHypercohomologyEquiv_zero s (holomorphicUnitsSheaf s (dim X)) 1 1,
    (sheafExtHypercohomologyEquiv s (holomorphicUnitsSheaf s (dim X)) 1 1).injective.eq_iff]
  exact analyticTransitionExtClass_eq_zero_iff s (holomorphicUnitsSheaf s (dim X))
    U V hcover (Additive.ofMul u)

/-- Changing trivializations on the two opens leaves the actual units class unchanged. -/
theorem holomorphicTransitionUnitsClass_changeTrivialization
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions s (dim X) (.op (U ⊓ V)))ˣ)
    (a : (OpenHolomorphicFunctions s (dim X) (.op U))ˣ)
    (b : (OpenHolomorphicFunctions s (dim X) (.op V))ˣ) :
    holomorphicTransitionUnitsClass s U V hcover
      (u * (Units.map (holomorphicRestrictionAlgHom s (dim X)
        (homOfLE inf_le_left).op).toMonoidHom a /
          Units.map (holomorphicRestrictionAlgHom s (dim X)
            (homOfLE inf_le_right).op).toMonoidHom b)) =
      holomorphicTransitionUnitsClass s U V hcover u := by
  unfold holomorphicTransitionUnitsClass
  congr 1
  exact analyticTransitionExtClass_add_coboundary s (holomorphicUnitsSheaf s (dim X))
    U V hcover (Additive.ofMul u) (Additive.ofMul a) (Additive.ofMul b)

/-- Changing local trivializations leaves the integral exponential class unchanged. -/
theorem integralHolomorphicTransitionClass_changeTrivialization
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions s (dim X) (.op (U ⊓ V)))ˣ)
    (a : (OpenHolomorphicFunctions s (dim X) (.op U))ˣ)
    (b : (OpenHolomorphicFunctions s (dim X) (.op V))ˣ) :
    integralHolomorphicTransitionClass s U V hcover
      (u * (Units.map (holomorphicRestrictionAlgHom s (dim X)
        (homOfLE inf_le_left).op).toMonoidHom a /
          Units.map (holomorphicRestrictionAlgHom s (dim X)
            (homOfLE inf_le_right).op).toMonoidHom b)) =
      integralHolomorphicTransitionClass s U V hcover u := by
  unfold integralHolomorphicTransitionClass
  rw [holomorphicTransitionUnitsClass_changeTrivialization]

/-- Changing local trivializations leaves the rational Hodge class unchanged. -/
theorem rationalHolomorphicTransitionClass_changeTrivialization
    (U V : Opens (TopCat.of (ComplexPoint X s))) (hcover : U ⊔ V = ⊤)
    (u : (OpenHolomorphicFunctions s (dim X) (.op (U ⊓ V)))ˣ)
    (a : (OpenHolomorphicFunctions s (dim X) (.op U))ˣ)
    (b : (OpenHolomorphicFunctions s (dim X) (.op V))ˣ) :
    rationalHolomorphicTransitionClass s U V hcover
      (u * (Units.map (holomorphicRestrictionAlgHom s (dim X)
        (homOfLE inf_le_left).op).toMonoidHom a /
          Units.map (holomorphicRestrictionAlgHom s (dim X)
            (homOfLE inf_le_right).op).toMonoidHom b)) =
      rationalHolomorphicTransitionClass s U V hcover u := by
  unfold rationalHolomorphicTransitionClass
  rw [holomorphicTransitionUnitsClass_changeTrivialization]

end AlgebraicGeometry.ComplexPoint
