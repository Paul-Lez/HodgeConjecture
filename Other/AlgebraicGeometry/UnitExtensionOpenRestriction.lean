/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicUnitExtension
public import Other.AlgebraicTopology.ConstantSheafGlobalSection
public import Other.AlgebraicTopology.NestedSheafSupportOnOpen

/-!
# Unit-sheaf extensions that split on an open set

Let `E` be an extension `0 → 𝒪ˣ → E.middle → ℤ → 0` of analytic sheaves and let `Ω` be an open
subset of the analytic space. A section `ℓ` of `E.middle` over `Ω` lifting the constant integer
section `1` is exactly a splitting of the restriction of `E` to `Ω`.

This file proves that such a splitting kills the class of `E` after restriction to `Ω`:

`cohomologyClass_comp_restrictionUnit_eq_zero` states that the image of `E.cohomologyClass` under
the map `Ext¹(ℤ, 𝒪ˣ) → Ext¹(ℤ, j_* (𝒪ˣ|_Ω))` induced by the canonical restriction morphism
`j_*j^*` vanishes.

The argument does not use short exactness of the pushed-forward sequence, only that the
restriction morphism `𝒪ˣ → j_*(𝒪ˣ|_Ω)` factors through the inclusion `𝒪ˣ → E.middle`; the class
of an extension dies against any morphism factoring through its own inclusion
(`ShortComplex.ShortExact.extClass_comp`). The factorisation is produced from `ℓ` by:

* `constHomOfSection` turns `ℓ` into a morphism `ℤ → j_*(E.middle|_Ω)` from the constant integer
  sheaf (`Other/AlgebraicTopology/ConstantSheafGlobalSection.lean`);
* adjunction turns that into a section of `E.projection|_Ω` over `Ω`;
* exactness of open restriction turns the section into a retraction of `E.inclusion|_Ω`, whose
  adjoint is the required factorisation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance unitExtensionOpenRestrictionTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable {X}

/-- Restriction of an analytic sheaf to an open subset, pushed back to the whole space. -/
abbrev openRestrictionFunctor (Ω : Opens (TopCat.of (ComplexPoint X))) :
    AnalyticAdditiveSheaf X ⥤ AnalyticAdditiveSheaf X :=
  TopCat.Sheaf.openRestrictionPushforward (TopCat.of (ComplexPoint X)) Ω

/-- The canonical morphism from a sheaf to the direct image of its restriction to `Ω`. -/
abbrev restrictionUnit (Ω : Opens (TopCat.of (ComplexPoint X))) (F : AnalyticAdditiveSheaf X) :
    F ⟶ (openRestrictionFunctor Ω).obj F :=
  (TopCat.Sheaf.toOpenRestrictionPushforward (TopCat.of (ComplexPoint X)) Ω).app F

/-- Global sections of the restriction-pushforward are sections on `Ω`. -/
abbrev openRestrictionTopEval (Ω : Opens (TopCat.of (ComplexPoint X))) :
    openRestrictionFunctor Ω ⋙ TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤ ≅
      TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) Ω :=
  TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso (TopCat.of (ComplexPoint X)) Ω

set_option backward.isDefEq.respectTransparency false in
/-- The canonical restriction morphism, read on global sections through the identification of
global sections of the restriction-pushforward with sections on `Ω`, is restriction of sections
from the whole space to `Ω`. -/
lemma openRestrictionTopEval_restrictionUnit (Ω : Opens (TopCat.of (ComplexPoint X)))
    (F : AnalyticAdditiveSheaf X) (t : F.obj.obj (op (⊤ : Opens (TopCat.of (ComplexPoint X))))) :
    (openRestrictionTopEval Ω).hom.app F ((restrictionUnit Ω F).hom.app (op ⊤) t) =
      F.obj.map (homOfLE (le_top : Ω ≤ ⊤)).op t := by
  have h : (restrictionUnit Ω F).hom.app (op (⊤ : Opens (TopCat.of (ComplexPoint X)))) ≫
      (openRestrictionTopEval Ω).hom.app F =
      F.obj.map (homOfLE (le_top : Ω ≤ ⊤)).op := by
    change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
    rw [← F.obj.map_comp]
    congr 1
  exact (CategoryTheory.comp_apply _ _ t).symm.trans (CategoryTheory.congr_fun h t)

variable (X)

/-- The constant integer sheaf of the analytic space is the constant integer sheaf of its
underlying topological space. -/
lemma constantIntegerSheaf_eq :
    constantIntegerSheaf X = TopCat.Sheaf.integerConstantSheaf (TopCat.of (ComplexPoint X)) := rfl

/-- The global section `1` of the constant integer sheaf determines the identity. -/
lemma constHomOfSection_integerOneSection :
    TopCat.Sheaf.constHomOfSection (constantIntegerSheaf X)
        (HolomorphicUnitExtension.integerOneSection (X := X)) = 𝟙 (constantIntegerSheaf X) :=
  TopCat.Sheaf.constHomOfSection_integerOne

/-- Restriction of analytic sheaves to an open subset. -/
abbrev restrictToOpen (Ω : Opens (TopCat.of (ComplexPoint X))) :
    AnalyticAdditiveSheaf X ⥤ TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of ↥Ω) :=
  Ω.isOpenEmbedding.sheafPullback AddCommGrpCat

instance restrictToOpenAdditive (Ω : Opens (TopCat.of (ComplexPoint X))) :
    (restrictToOpen X Ω).Additive :=
  TopCat.Sheaf.openSheafRestriction_additive (TopCat.of (ComplexPoint X)) Ω

instance restrictToOpenPreservesFiniteLimits (Ω : Opens (TopCat.of (ComplexPoint X))) :
    Limits.PreservesFiniteLimits (restrictToOpen X Ω) :=
  TopCat.Sheaf.openSheafRestriction_preservesFiniteLimits (TopCat.of (ComplexPoint X)) Ω

instance restrictToOpenPreservesFiniteColimits (Ω : Opens (TopCat.of (ComplexPoint X))) :
    Limits.PreservesFiniteColimits (restrictToOpen X Ω) :=
  TopCat.Sheaf.openSheafRestriction_preservesFiniteColimits (TopCat.of (ComplexPoint X)) Ω

variable {X}

/-- The adjunction between restriction to an open subset and direct image. -/
abbrev openRestrictionAdjunction (Ω : Opens (TopCat.of (ComplexPoint X))) :
    restrictToOpen X Ω ⊣ TopCat.Sheaf.pushforward AddCommGrpCat Ω.inclusion' :=
  TopCat.Sheaf.openSheafRestrictionAdjunction (TopCat.of (ComplexPoint X)) Ω

/-- The unit of the open-restriction adjunction is the canonical restriction morphism. -/
lemma openRestrictionAdjunction_unit_app (Ω : Opens (TopCat.of (ComplexPoint X)))
    (F : AnalyticAdditiveSheaf X) :
    (openRestrictionAdjunction Ω).unit.app F = restrictionUnit Ω F := rfl

namespace HolomorphicUnitExtension

variable (E : HolomorphicUnitExtension X d) (Ω : Opens (TopCat.of (ComplexPoint X)))

/-- The morphism from the constant integer sheaf determined by a section of the middle sheaf on
`Ω`. -/
def liftHom (ℓ : E.middle.obj.obj (op Ω)) :
    constantIntegerSheaf X ⟶ (openRestrictionFunctor Ω).obj E.middle :=
  TopCat.Sheaf.constHomOfSection _ ((openRestrictionTopEval Ω).inv.app E.middle ℓ)

set_option backward.isDefEq.respectTransparency false in
/-- A lift of the constant section `1` over `Ω` is carried by the projection to the restriction of
the constant section `1`. -/
lemma projection_liftSection (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    ((openRestrictionFunctor Ω).map E.projection).hom.app (op ⊤)
        ((openRestrictionTopEval Ω).inv.app E.middle ℓ) =
      (restrictionUnit Ω (constantIntegerSheaf X)).hom.app (op ⊤) (integerOneSection (X := X)) := by
  have hnat := (openRestrictionTopEval Ω).inv.naturality E.projection
  have hleft : ((openRestrictionFunctor Ω).map E.projection).hom.app (op ⊤)
      ((openRestrictionTopEval Ω).inv.app E.middle ℓ) =
      (openRestrictionTopEval Ω).inv.app (constantIntegerSheaf X)
        (E.projection.hom.app (op Ω) ℓ) :=
    (CategoryTheory.comp_apply _ _ ℓ).symm.trans
      ((CategoryTheory.congr_fun hnat.symm ℓ).trans (CategoryTheory.comp_apply _ _ ℓ))
  have h2 : (openRestrictionTopEval Ω).hom.app (constantIntegerSheaf X) ≫
      (openRestrictionTopEval Ω).inv.app (constantIntegerSheaf X) = 𝟙 _ :=
    (openRestrictionTopEval Ω).hom_inv_id_app (constantIntegerSheaf X)
  have hu : (openRestrictionTopEval Ω).hom.app (constantIntegerSheaf X)
      ((restrictionUnit Ω (constantIntegerSheaf X)).hom.app (op ⊤)
        (integerOneSection (X := X))) =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
        (integerOneSection (X := X)) :=
    openRestrictionTopEval_restrictionUnit Ω _ _
  rw [hleft, hℓ, ← hu]
  exact (((CategoryTheory.comp_apply _ _ _).symm.trans
    (CategoryTheory.congr_fun h2 _)).trans (CategoryTheory.id_apply _))

set_option backward.isDefEq.respectTransparency false in
/-- A lift of the constant section `1` over `Ω` splits the projection after restriction to `Ω`. -/
lemma liftHom_comp_projection (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    E.liftHom Ω ℓ ≫ (openRestrictionFunctor Ω).map E.projection =
      restrictionUnit Ω (constantIntegerSheaf X) := by
  rw [liftHom, TopCat.Sheaf.constHomOfSection_comp, E.projection_liftSection Ω ℓ hℓ,
    ← TopCat.Sheaf.constHomOfSection_comp, constHomOfSection_integerOneSection]
  exact Category.id_comp _

/-- The section of the restricted projection determined by a lift of `1` over `Ω`. -/
def restrictedSection (ℓ : E.middle.obj.obj (op Ω)) :
    (restrictToOpen X Ω).obj (constantIntegerSheaf X) ⟶ (restrictToOpen X Ω).obj E.middle :=
  ((openRestrictionAdjunction Ω).homEquiv _ _).symm (E.liftHom Ω ℓ)

set_option backward.isDefEq.respectTransparency false in
/-- The restricted section really is a section of the restricted projection. -/
lemma restrictedSection_comp_projection (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    E.restrictedSection Ω ℓ ≫ (restrictToOpen X Ω).map E.projection = 𝟙 _ := by
  apply ((openRestrictionAdjunction Ω).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_id, restrictedSection,
    Equiv.apply_symm_apply]
  exact E.liftHom_comp_projection Ω ℓ hℓ

/-- The restriction of the extension to an open subset is again short exact, because open
restriction is exact. -/
lemma shortExact_map_restrictToOpen :
    (E.shortComplex.map (restrictToOpen X Ω)).ShortExact :=
  ShortComplex.ShortExact.map_of_exact E.shortExact _

/-- The splitting of the restricted extension determined by a lift of `1` over `Ω`. -/
def restrictedSplitting (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    (E.shortComplex.map (restrictToOpen X Ω)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (E.shortExact_map_restrictToOpen Ω).exact
    (E.restrictedSection Ω ℓ) (E.restrictedSection_comp_projection Ω ℓ hℓ)
    (E.shortExact_map_restrictToOpen Ω).mono_f

/-- The factorisation of the canonical restriction morphism of the unit sheaf through the
inclusion of the unit sheaf into the middle term. -/
def restrictionFactorisation (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    E.middle ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d) :=
  (openRestrictionAdjunction Ω).homEquiv _ _ (E.restrictedSplitting Ω ℓ hℓ).r

set_option backward.isDefEq.respectTransparency false in
/-- The factorisation really factors the canonical restriction morphism. -/
lemma inclusion_comp_restrictionFactorisation (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    E.inclusion ≫ E.restrictionFactorisation Ω ℓ hℓ =
      restrictionUnit Ω (holomorphicUnitSheaf X d) := by
  rw [restrictionFactorisation, ← Adjunction.homEquiv_naturality_left]
  rw [show (restrictToOpen X Ω).map E.inclusion ≫ (E.restrictedSplitting Ω ℓ hℓ).r = 𝟙 _ from
    (E.restrictedSplitting Ω ℓ hℓ).f_r]
  exact Adjunction.homEquiv_id _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The class of an extension splitting on `Ω` dies after restriction to `Ω`.** -/
theorem cohomologyClass_comp_restrictionUnit_eq_zero (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    E.cohomologyClass.comp
        (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1) = 0 := by
  rw [cohomologyClass, ← E.inclusion_comp_restrictionFactorisation Ω ℓ hℓ,
    ← Abelian.Ext.mk₀_comp_mk₀]
  exact E.shortExact.extClass_comp_assoc _

end HolomorphicUnitExtension

end AlgebraicGeometry.ComplexPoint
