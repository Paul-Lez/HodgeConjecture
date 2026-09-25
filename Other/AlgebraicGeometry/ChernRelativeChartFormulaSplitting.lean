/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeClass
public import Other.Algebra.Homology.MappingConeDifference
public import Other.AlgebraicTopology.SingularChainSheafPushforward

/-!
# How the canonical relative class depends on the splitting

The relative first Chern class of `ChernRelativeClass.lean` is built from a lift `ℓ`
of the constant integer section `1` over an open set `Ω`. This file proves that the
change between two splitting-induced cone maps factors through the integer quotient
and the inclusion of the complement units into the relative unit cone.

The quotient morphism is supplied by the cokernel property. Its composite with the
unit inclusion is proved to be the difference of the lifted frames in the opposite
order: increasing a frame decreases the splitting retraction. Identifying this
morphism on sections with the inverse Cartier equation and transporting it to
supported cohomology on a smaller chart remain to be done.

Everything here happens at the level of *morphisms of complexes*, where sums and differences are
available, so no group structure on `SmallShiftedHom` is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf
variable {Y : TopCat.{0}}
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluating the constant-sheaf morphism at one recovers its defining section. -/
theorem constHomOfSection_integerOne_apply (F : Sheaf AddCommGrpCat.{0} Y) (t : F.obj.obj (op ⊤)) :
    (constHomOfSection F t).hom.app (op ⊤) (integerOne (Y := Y)) = t := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (op ⊤)) (toSheafify_constHomOfSection F t)) (1 : ℤ)
  change _ = (constPresheafHomOfSection F t).app (op ⊤) (1 : ℤ) at h
  change (constHomOfSection F t).hom.app (op ⊤) (integerOne (Y := Y)) = _ at h
  refine h.trans ((constPresheafHomOfSection_app_one F t (op ⊤)).trans ?_)
  change F.obj.map (𝟙 (op (⊤ : Opens Y))) t = t
  erw [F.obj.map_id]
  rfl
end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance chernRelativeSplittingTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable {X d}

namespace HolomorphicUnitExtension

variable (E : HolomorphicUnitExtension X d) (Ω : Opens (TopCat.of (ComplexPoint X)))
  (ℓ₁ ℓ₂ : E.middle.obj.obj (op Ω))
  (hℓ₁ : E.projection.hom.app (op Ω) ℓ₁ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection)
  (hℓ₂ : E.projection.hom.app (op Ω) ℓ₂ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection)

/-- The two factorisations of the restriction morphism attached to two lifts of `1` over `Ω`
differ by a morphism factoring through the projection: their difference kills the inclusion of the
unit sheaf, and the projection is a cokernel of that inclusion. -/
theorem exists_restrictionFactorisation_eq_add :
    ∃ s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d),
      E.restrictionFactorisation Ω ℓ₂ hℓ₂ =
        E.restrictionFactorisation Ω ℓ₁ hℓ₁ + E.projection ≫ s := by
  have hzero : E.inclusion ≫
      (E.restrictionFactorisation Ω ℓ₂ hℓ₂ - E.restrictionFactorisation Ω ℓ₁ hℓ₁) = 0 := by
    rw [Preadditive.comp_sub, E.inclusion_comp_restrictionFactorisation Ω ℓ₂ hℓ₂,
      E.inclusion_comp_restrictionFactorisation Ω ℓ₁ hℓ₁, sub_self]
  have := E.shortExact.epi_g
  obtain ⟨s, hs⟩ := Cofork.IsColimit.desc' E.shortExact.exact.gIsCokernel
    (E.restrictionFactorisation Ω ℓ₂ hℓ₂ - E.restrictionFactorisation Ω ℓ₁ hℓ₁)
    (by simpa using hzero)
  exact ⟨s, by rw [show E.projection ≫ s = _ from hs]; abel⟩

/-- The change of splitting changes the map of cones by a morphism through the integer
quotient and the inclusion into the relative unit cone. This is the chain-level boundary
term that survives when a unit on the complement does not extend across the divisor. -/
theorem exists_relativeConeMap_sub_eq :
    ∃ s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d),
      E.relativeConeMap Ω ℓ₂ hℓ₂ - E.relativeConeMap Ω ℓ₁ hℓ₁ =
        E.coneToInteger ≫ (analyticSingleFunctor X).map s ≫
          CochainComplex.mappingCone.inr
            ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))) := by
  obtain ⟨s, hs⟩ := E.exists_restrictionFactorisation_eq_add Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂
  refine ⟨s, ?_⟩
  apply CochainComplex.mappingCone.map_sub_map_of_eq_add
  change (analyticSingleFunctor X).map (E.restrictionFactorisation Ω ℓ₂ hℓ₂) = _
  rw [hs, Functor.map_add, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The splitting retraction subtracts the chosen lifted frame. -/
theorem restrictionFactorisation_comp_inclusion
    (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    E.restrictionFactorisation Ω ℓ hℓ ≫ (openRestrictionFunctor Ω).map E.inclusion =
      restrictionUnit Ω E.middle - E.projection ≫ E.liftHom Ω ℓ := by
  have hr := (E.restrictedSplitting Ω ℓ hℓ).r_f
  change (E.restrictedSplitting Ω ℓ hℓ).r ≫ (restrictToOpen X Ω).map E.inclusion =
    𝟙 ((restrictToOpen X Ω).obj E.middle) - (restrictToOpen X Ω).map E.projection ≫ E.restrictedSection Ω ℓ at hr
  rw [restrictionFactorisation]
  change (openRestrictionAdjunction Ω).homEquiv _ _ (E.restrictedSplitting Ω ℓ hℓ).r ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat Ω.inclusion').map
      ((restrictToOpen X Ω).map E.inclusion) = _
  erw [← Adjunction.homEquiv_naturality_right, hr]
  have hsub (a b : (restrictToOpen X Ω).obj E.middle ⟶ (restrictToOpen X Ω).obj E.middle) :
      (openRestrictionAdjunction Ω).homEquiv _ _ (a - b) =
        (openRestrictionAdjunction Ω).homEquiv _ _ a -
          (openRestrictionAdjunction Ω).homEquiv _ _ b := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    erw [Functor.map_sub, Preadditive.comp_sub]
  rw [hsub, Adjunction.homEquiv_id, Adjunction.homEquiv_naturality_left,
    restrictedSection, Equiv.apply_symm_apply]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Increasing the frame changes the retraction by the negative frame difference. -/
theorem restrictionFactorisation_sub_comp_inclusion :
    (E.restrictionFactorisation Ω ℓ₂ hℓ₂ - E.restrictionFactorisation Ω ℓ₁ hℓ₁) ≫
      (openRestrictionFunctor Ω).map E.inclusion =
    E.projection ≫ (E.liftHom Ω ℓ₁ - E.liftHom Ω ℓ₂) := by
  rw [Preadditive.sub_comp, restrictionFactorisation_comp_inclusion, restrictionFactorisation_comp_inclusion, Preadditive.comp_sub]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- The cone difference factors through the frame difference in the opposite order.
This records the frame sign explicitly at the level of sheaf morphisms. -/
theorem exists_relativeConeMap_sub_eq_with_liftHom :
    ∃ s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d),
      s ≫ (openRestrictionFunctor Ω).map E.inclusion = E.liftHom Ω ℓ₁ - E.liftHom Ω ℓ₂ ∧
      E.relativeConeMap Ω ℓ₂ hℓ₂ - E.relativeConeMap Ω ℓ₁ hℓ₁ =
        E.coneToInteger ≫ (analyticSingleFunctor X).map s ≫
          CochainComplex.mappingCone.inr
            ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))) := by
  obtain ⟨s, hs⟩ := E.exists_restrictionFactorisation_eq_add Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂
  refine ⟨s, ?_, ?_⟩
  · have := E.shortExact.epi_g
    apply (cancel_epi E.projection).1
    have hs' : E.projection ≫ s =
        E.restrictionFactorisation Ω ℓ₂ hℓ₂ - E.restrictionFactorisation Ω ℓ₁ hℓ₁ := by
      rw [hs]
      abel
    rw [← Category.assoc, hs']
    exact E.restrictionFactorisation_sub_comp_inclusion Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂
  · apply CochainComplex.mappingCone.map_sub_map_of_eq_add
    change (analyticSingleFunctor X).map (E.restrictionFactorisation Ω ℓ₂ hℓ₂) = _
    rw [hs, Functor.map_add, Functor.map_comp]
    rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The lifted integer morphism recovers the chosen frame on the open complement. -/
theorem liftHom_integerOneSection (ℓ : E.middle.obj.obj (op Ω)) :
    (openRestrictionTopEval Ω).hom.app E.middle
      ((E.liftHom Ω ℓ).hom.app (op ⊤) integerOneSection) = ℓ := by
  rw [liftHom]
  erw [TopCat.Sheaf.constHomOfSection_integerOne_apply]
  exact ConcreteCategory.congr_hom ((openRestrictionTopEval Ω).inv_hom_id_app E.middle) ℓ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On sections, the quotient morphism records the frame difference in reverse order. -/
theorem liftHom_difference_section
    (s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
    (hs : s ≫ (openRestrictionFunctor Ω).map E.inclusion = E.liftHom Ω ℓ₁ - E.liftHom Ω ℓ₂) :
    E.inclusion.hom.app (op Ω)
      ((openRestrictionTopEval Ω).hom.app (holomorphicUnitSheaf X d)
        (s.hom.app (op ⊤) integerOneSection)) = ℓ₁ - ℓ₂ := by
  have hn := ConcreteCategory.congr_hom ((openRestrictionTopEval Ω).hom.naturality E.inclusion)
    (s.hom.app (op ⊤) integerOneSection)
  change (openRestrictionTopEval Ω).hom.app E.middle
      (((openRestrictionFunctor Ω).map E.inclusion).hom.app (op ⊤)
        (s.hom.app (op ⊤) integerOneSection)) = _ at hn
  refine hn.symm.trans ?_
  have he := congrArg (fun f : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj E.middle =>
    (openRestrictionTopEval Ω).hom.app E.middle (f.hom.app (op ⊤) integerOneSection)) hs
  change (openRestrictionTopEval Ω).hom.app E.middle
      (((openRestrictionFunctor Ω).map E.inclusion).hom.app (op ⊤)
        (s.hom.app (op ⊤) integerOneSection)) = _ at he
  rw [he]
  change (openRestrictionTopEval Ω).hom.app E.middle
    ((E.liftHom Ω ℓ₁).hom.app (op ⊤) integerOneSection -
      (E.liftHom Ω ℓ₂).hom.app (op ⊤) integerOneSection) = _
  rw [map_sub, liftHom_integerOneSection, liftHom_integerOneSection]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If the new frame differs by the unit `w`, the cone quotient section is `-w`. -/
theorem liftHom_difference_section_eq_neg_unit
    (s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
    (hs : s ≫ (openRestrictionFunctor Ω).map E.inclusion = E.liftHom Ω ℓ₁ - E.liftHom Ω ℓ₂)
    (w : (holomorphicUnitSheaf X d).obj.obj (op Ω))
    (hw : E.inclusion.hom.app (op Ω) w = ℓ₂ - ℓ₁) :
    (openRestrictionTopEval Ω).hom.app (holomorphicUnitSheaf X d)
      (s.hom.app (op ⊤) integerOneSection) = -w := by
  apply TopCat.Sheaf.sections_injective E.shortComplex E.shortExact Ω
  change E.inclusion.hom.app (op Ω) _ = E.inclusion.hom.app (op Ω) (-w)
  rw [E.liftHom_difference_section Ω ℓ₁ ℓ₂ s hs, map_neg, hw]
  abel


end HolomorphicUnitExtension

end AlgebraicGeometry.ComplexPoint
