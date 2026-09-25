/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernSectionBoundary

/-!
# Changing the frame of the actual relative first Chern class

The difference of two existing relative Chern classes is the boundary of the
actual restricted singular cocycle evaluated on the quotient unit section.
That section maps under the extension inclusion to the old frame minus the new
frame. The result follows from the proved difference of the literal cone maps,
with the original quasi-isomorphism and constant-complex normalization retained.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization TopologicalSpace Opposite
open CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ))
local instance frameVariationDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
lemma hypercohomologyEquiv_sub (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (a b : Hypercohomology X K n) :
    SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q (a - b) =
      SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q a -
        SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q b := by
  let e : Hypercohomology X K n ≃+ _ :=
    { toEquiv := SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      map_add' := hypercohomologyEquiv_add X K n }
  exact e.map_sub a b
/-- A morphism from the integer constant sheaf is determined by its value on one. -/
lemma constantIntegerMorphism_eq_constHomOfSection
    (F : AnalyticAdditiveSheaf X) (s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ F) :
    s = TopCat.Sheaf.constHomOfSection F
      (s.hom.app (op ⊤) HolomorphicUnitExtension.integerOneSection) := by
  have h := TopCat.Sheaf.constHomOfSection_comp
    (TopCat.Sheaf.integerOne (Y := TopCat.of (ComplexPoint X))) s
  rw [TopCat.Sheaf.constHomOfSection_integerOne, Category.id_comp] at h
  exact h

/-- Reading a restricted integer-input morphism as a section on the open and
then reconstructing the constant morphism returns the original morphism. -/
lemma restrictedIntegerMorphism_eq_constHomOfSection
    (Ω : Opens (TopCat.of (ComplexPoint X))) (F : AnalyticAdditiveSheaf X)
    (s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj F) :
    s = TopCat.Sheaf.constHomOfSection ((openRestrictionFunctor Ω).obj F)
      ((openRestrictionTopEval Ω).inv.app F
        ((openRestrictionTopEval Ω).hom.app F
          (s.hom.app (op ⊤) HolomorphicUnitExtension.integerOneSection))) := by
  have hc := ((openRestrictionTopEval Ω).app F).addCommGroupIsoToAddEquiv.symm_apply_apply
    (s.hom.app (op ⊤) HolomorphicUnitExtension.integerOneSection)
  exact (constantIntegerMorphism_eq_constHomOfSection X _ s).trans
    (congrArg (TopCat.Sheaf.constHomOfSection ((openRestrictionFunctor Ω).obj F)) hc.symm)

variable {d : ℕ} [SmoothOfRelativeDimension d X.hom]
  (E : HolomorphicUnitExtension X d) (Ω : Opens (TopCat.of (ComplexPoint X)))
  (ℓ : E.middle.obj.obj (op Ω))
  (hℓ : E.projection.hom.app (op Ω) ℓ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

/-- The existing relative Chern class under the actual derived-category comparison. -/
lemma HolomorphicUnitExtension.relativeChernClass_equiv
    (cmp : RelativeChernComparison X d Ω) :
    SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (E.relativeChernClass Ω ℓ hℓ cmp) =
    DerivedCategory.Q.map (analyticSheafComplexIntIsoSingle X (𝓒(↧(ComplexPoint X); ℤ))).hom ≫
      (isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X) E.coneToInteger
        (by change QuasiIso _; exact E.quasiIso_coneToInteger)).inv ≫
      DerivedCategory.Q.map (E.relativeConeMap Ω ℓ hℓ) ≫
        SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q cmp.hom := by
  simp only [HolomorphicUnitExtension.relativeChernClass,
    HolomorphicUnitExtension.relativeCohomologyClass', HolomorphicUnitExtension.relativeCohomologyClass,
    SmallShiftedHom.precompEquiv_symm_apply, SmallShiftedHom.equiv_comp,
    SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk₀Inv]
  simp only [ShiftedHom.mk₀_comp_mk₀]
  simp only [ShiftedHom.mk₀_comp, Category.assoc]

variable (ℓ₁ ℓ₂ : E.middle.obj.obj (op Ω))
  (hℓ₁ : E.projection.hom.app (op Ω) ℓ₁ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (hℓ₂ : E.projection.hom.app (op Ω) ℓ₂ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

set_option maxHeartbeats 2000000 in
/-- The literal difference of cone maps determines the difference of relative Chern classes. -/
lemma HolomorphicUnitExtension.relativeChernClass_sub_of_cone_difference
    (cmp : RelativeChernComparison X d Ω)
    (s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
    (hs : E.relativeConeMap Ω ℓ₂ hℓ₂ - E.relativeConeMap Ω ℓ₁ hℓ₁ =
      E.coneToInteger ≫ (analyticSingleFunctor X).map s ≫
        CochainComplex.mappingCone.inr
          ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))) :
    E.relativeChernClass Ω ℓ₂ hℓ₂ cmp - E.relativeChernClass Ω ℓ₁ hℓ₁ cmp =
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
        (analyticSingleFunctor X).map s ≫
        CochainComplex.mappingCone.inr
          ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))))).comp
      cmp.hom (add_zero (1 : ℤ)) := by
  apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [hypercohomologyEquiv_sub, E.relativeChernClass_equiv X Ω ℓ₂ hℓ₂,
    E.relativeChernClass_equiv X Ω ℓ₁ hℓ₁]
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp]
  rw [← Preadditive.comp_sub, ← Preadditive.comp_sub, ← Preadditive.sub_comp,
    ← CategoryTheory.Functor.map_sub, hs]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  let e := isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X) E.coneToInteger
    (by change QuasiIso _; exact E.quasiIso_coneToInteger)
  change DerivedCategory.Q.map (analyticSheafComplexIntIsoSingle X (𝓒(↧(ComplexPoint X); ℤ))).hom ≫
    e.inv ≫ e.hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

variable [IsIntegral X.left] [Smooth X.hom]
/-- A frame change is the actual singular boundary of the quotient integer-input morphism. -/
lemma HolomorphicUnitExtension.exists_relativeChernClass_sub_eq_singular_boundary
    (cmp : RelativeChernComparison X d Ω) :
    ∃ s : 𝓒(↧(ComplexPoint X); ℤ) ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d),
      s ≫ (openRestrictionFunctor Ω).map E.inclusion = E.liftHom Ω ℓ₁ - E.liftHom Ω ℓ₂ ∧
      E.relativeChernClass Ω ℓ₂ hℓ₂ cmp - E.relativeChernClass Ω ℓ₁ hℓ₁ cmp =
        hypercohomologyMap X
          (CochainComplex.mappingCone.inr
            (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) 1
          (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
            ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
              Cocycle.equivHomShift.symm
                ((restrictedSingularOneCocycle X d Ω).precomp ((analyticSingleFunctor X).map s)))) := by
  obtain ⟨s, hs, hc⟩ := E.exists_relativeConeMap_sub_eq_with_liftHom Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂
  exact ⟨s, hs, (E.relativeChernClass_sub_of_cone_difference X Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂ cmp s hc).trans
    (cmp.boundary_eq_singular_on_section X d Ω s)⟩

/-- The quotient morphism's concrete unit section computes the actual change
of the relative first Chern class. -/
lemma HolomorphicUnitExtension.exists_relativeChernClass_sub_eq_unit_boundary
    (cmp : RelativeChernComparison X d Ω) :
    ∃ u : (holomorphicUnitSheaf X d).obj.obj (op Ω),
      E.inclusion.hom.app (op Ω) u = ℓ₁ - ℓ₂ ∧
      E.relativeChernClass Ω ℓ₂ hℓ₂ cmp - E.relativeChernClass Ω ℓ₁ hℓ₁ cmp =
        hypercohomologyMap X
          (CochainComplex.mappingCone.inr
            (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) 1
          (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
            ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
              Cocycle.equivHomShift.symm
                ((restrictedSingularOneCocycle X d Ω).precomp
                  ((analyticSingleFunctor X).map
                    (TopCat.Sheaf.constHomOfSection
                      ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
                      ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))))) := by
  obtain ⟨s, hs, hc⟩ := E.exists_relativeChernClass_sub_eq_singular_boundary X Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂ cmp
  let u := (openRestrictionTopEval Ω).hom.app (holomorphicUnitSheaf X d)
    (s.hom.app (op ⊤) HolomorphicUnitExtension.integerOneSection)
  refine ⟨u, E.liftHom_difference_section Ω ℓ₁ ℓ₂ s hs, ?_⟩
  have he := restrictedIntegerMorphism_eq_constHomOfSection X Ω (holomorphicUnitSheaf X d) s
  exact hc.trans (congrArg (fun t =>
    hypercohomologyMap X
      (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) 1
      (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
          Cocycle.equivHomShift.symm
            ((restrictedSingularOneCocycle X d Ω).precomp ((analyticSingleFunctor X).map t))))) he)
/-- If the new frame differs by inclusion of `w`, the actual relative Chern
class changes by the singular boundary of the negative unit `-w`. -/
lemma HolomorphicUnitExtension.relativeChernClass_sub_eq_neg_unit_boundary
    (cmp : RelativeChernComparison X d Ω)
    (w : (holomorphicUnitSheaf X d).obj.obj (op Ω))
    (hw : E.inclusion.hom.app (op Ω) w = ℓ₂ - ℓ₁) :
    E.relativeChernClass Ω ℓ₂ hℓ₂ cmp - E.relativeChernClass Ω ℓ₁ hℓ₁ cmp =
      hypercohomologyMap X
        (CochainComplex.mappingCone.inr
          (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) 1
        (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
            Cocycle.equivHomShift.symm
              ((restrictedSingularOneCocycle X d Ω).precomp
                ((analyticSingleFunctor X).map
                  (TopCat.Sheaf.constHomOfSection
                    ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
                    ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) (-w))))))) := by
  obtain ⟨u, hu, hc⟩ := E.exists_relativeChernClass_sub_eq_unit_boundary X Ω ℓ₁ ℓ₂ hℓ₁ hℓ₂ cmp
  have he : u = -w := by
    apply TopCat.Sheaf.sections_injective E.shortComplex E.shortExact Ω
    change E.inclusion.hom.app (op Ω) u = E.inclusion.hom.app (op Ω) (-w)
    rw [hu, map_neg, hw]
    abel
  simpa only [he] using hc

end AlgebraicGeometry.ComplexPoint
