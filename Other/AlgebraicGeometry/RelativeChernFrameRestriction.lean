/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernFrameVariation
/-!
# Restricting the actual relative frame cone map

The canonical splitting retraction commutes with restriction of its defining
frame. Consequently the actual relative cone map of a restricted frame factors
through the relative unit cone for the larger open where the frame is defined.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
set_option autoImplicit false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ))

/-- The top-evaluation inverse commutes with further restriction of the open. -/
lemma openRestrictionTopEval_inv_naturality_open
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U) (F : AnalyticAdditiveSheaf X) :
    (openRestrictionTopEval U).inv.app F ≫
      ((TopCat.Sheaf.openRestrictionPushforwardMap (TopCat.of (ComplexPoint X)) h).app F).hom.app
        (op ⊤) =
      F.obj.map (homOfLE h).op ≫ (openRestrictionTopEval V).inv.app F := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1

variable {d : ℕ} [SmoothOfRelativeDimension d X.hom]
  (E : HolomorphicUnitExtension X d)
  {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
  (ℓ : E.middle.obj.obj (op U))

/-- The integer-input morphism of a restricted frame is its literal pushforward restriction. -/
lemma HolomorphicUnitExtension.liftHom_restrict :
    E.liftHom U ℓ ≫
      (TopCat.Sheaf.openRestrictionPushforwardMap (TopCat.of (ComplexPoint X)) h).app E.middle =
    E.liftHom V (E.middle.obj.map (homOfLE h).op ℓ) := by
  unfold HolomorphicUnitExtension.liftHom
  rw [TopCat.Sheaf.constHomOfSection_comp]
  apply congrArg (TopCat.Sheaf.constHomOfSection _)
  exact ConcreteCategory.congr_hom (openRestrictionTopEval_inv_naturality_open X h E.middle) ℓ

/-- The frame condition is preserved by restriction. -/
lemma HolomorphicUnitExtension.projection_restrict_lift
    (hℓ : E.projection.hom.app (op U) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : U ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    E.projection.hom.app (op V) (E.middle.obj.map (homOfLE h).op ℓ) =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : V ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection := by
  have hn := ConcreteCategory.congr_hom (E.projection.hom.naturality (homOfLE h).op) ℓ
  change E.projection.hom.app (op V) (E.middle.obj.map (homOfLE h).op ℓ) =
    (constantIntegerSheaf X).obj.map (homOfLE h).op (E.projection.hom.app (op U) ℓ) at hn
  rw [hn, hℓ]
  change ((constantIntegerSheaf X).obj.map _ ≫ (constantIntegerSheaf X).obj.map _) _ = _
  rw [← (constantIntegerSheaf X).obj.map_comp]
  rfl

/-- The actual splitting retraction commutes with restriction of its defining frame. -/
lemma HolomorphicUnitExtension.restrictionFactorisation_restrict
    (hℓ : E.projection.hom.app (op U) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : U ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    E.restrictionFactorisation U ℓ hℓ ≫
      (TopCat.Sheaf.openRestrictionPushforwardMap (TopCat.of (ComplexPoint X)) h).app
        (holomorphicUnitSheaf X d) =
    E.restrictionFactorisation V (E.middle.obj.map (homOfLE h).op ℓ)
      (E.projection_restrict_lift X h ℓ hℓ) := by
  have : Mono ((restrictToOpen X V).map E.inclusion) := (E.shortExact_map_restrictToOpen V).mono_f
  have : Mono ((openRestrictionFunctor V).map E.inclusion) := by
    change Mono ((TopCat.Sheaf.pushforward AddCommGrpCat V.inclusion').map
      ((restrictToOpen X V).map E.inclusion))
    infer_instance
  apply (cancel_mono ((openRestrictionFunctor V).map E.inclusion)).mp
  rw [Category.assoc,
    ← (TopCat.Sheaf.openRestrictionPushforwardMap (TopCat.of (ComplexPoint X)) h).naturality,
    ← Category.assoc, E.restrictionFactorisation_comp_inclusion,
    E.restrictionFactorisation_comp_inclusion]
  rw [Preadditive.sub_comp, Category.assoc, E.liftHom_restrict X h ℓ]
  congr 1
  exact NatTrans.congr_app (TopCat.Sheaf.toOpenRestrictionPushforward_comp
    (TopCat.of (ComplexPoint X)) h) E.middle
/-- Further restriction of the actual relative unit cones. -/
def relativeUnitConeRestriction : relativeUnitCone X d U ⟶ relativeUnitCone X d V :=
  CochainComplex.mappingCone.map _ _ (𝟙 _)
    ((analyticSingleFunctor X).map
      ((TopCat.Sheaf.openRestrictionPushforwardMap (TopCat.of (ComplexPoint X)) h).app
        (holomorphicUnitSheaf X d))) (by
    rw [Category.id_comp, ← (analyticSingleFunctor X).map_comp]
    exact congrArg (analyticSingleFunctor X).map
      (NatTrans.congr_app (TopCat.Sheaf.toOpenRestrictionPushforward_comp
        (TopCat.of (ComplexPoint X)) h) (holomorphicUnitSheaf X d)))

/-- The actual cone map of a restricted frame factors through the larger-open cone. -/
lemma HolomorphicUnitExtension.relativeConeMap_restrict
    (hℓ : E.projection.hom.app (op U) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : U ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    E.relativeConeMap U ℓ hℓ ≫ relativeUnitConeRestriction X h =
      E.relativeConeMap V (E.middle.obj.map (homOfLE h).op ℓ)
        (E.projection_restrict_lift X h ℓ hℓ) := by
  unfold HolomorphicUnitExtension.relativeConeMap relativeUnitConeRestriction
  rw [← CochainComplex.mappingCone.map_comp]
  simp only [Category.comp_id, ← (analyticSingleFunctor X).map_comp,
    E.restrictionFactorisation_restrict X h ℓ hℓ]

end AlgebraicGeometry.ComplexPoint
