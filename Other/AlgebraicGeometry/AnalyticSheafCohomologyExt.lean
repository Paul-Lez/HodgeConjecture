/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.IntegralCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Analytic sheaf cohomology and Ext

Hypercohomology of a degree-zero sheaf agrees with ordinary sheaf cohomology and Ext.
These comparisons respect maps of coefficient sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance analyticSheafExtHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- A sheaf concentrated in degree zero and then extended to integer degrees. -/
abbrev analyticSheafComplexInt (F : AnalyticAdditiveSheaf X) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj F).extend
    ComplexShape.embeddingUpNat

/-- Extension of a degree-zero sheaf complex agrees with the single complex in integer degrees. -/
def analyticSheafComplexIntIsoSingle (F : AnalyticAdditiveSheaf X) :
    analyticSheafComplexInt X F ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj F :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl

/-- A map of sheaves as a map of the extended degree-zero complexes. -/
def analyticSheafComplexIntMap {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) :
    analyticSheafComplexInt X F ⟶ analyticSheafComplexInt X G :=
  HomologicalComplex.extendMap ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map f)
    ComplexShape.embeddingUpNat

/-- Maps of extended sheaf complexes preserve composition. -/
theorem analyticSheafComplexIntMap_comp
    {F G H : AnalyticAdditiveSheaf X} (f : F ⟶ G) (g : G ⟶ H) :
    analyticSheafComplexIntMap X (f ≫ g) =
      analyticSheafComplexIntMap X f ≫ analyticSheafComplexIntMap X g := by
  simp only [analyticSheafComplexIntMap, Functor.map_comp, HomologicalComplex.extendMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The extension/single comparison is natural in the coefficient sheaf. -/
theorem analyticSheafComplexIntIsoSingle_naturality
    {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) :
    analyticSheafComplexIntMap X f ≫ (analyticSheafComplexIntIsoSingle X G).hom =
      (analyticSheafComplexIntIsoSingle X F).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f := by
  apply HomologicalComplex.to_single_hom_ext
  dsimp only [analyticSheafComplexIntMap, analyticSheafComplexIntIsoSingle,
    HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ _
    (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))]
  simp [HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.single_map_f_self,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors]

/-- Sheaf cohomology in a nonnegative degree agrees with Ext from the constant integer sheaf. -/
def analyticSheafCohomologyEquivExt (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Hypercohomology X (analyticSheafComplexInt X F) n ≃
      Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) F n :=
  (Localization.SmallShiftedHom.precompEquiv
      (analyticSheafComplexIntIsoSingle X (𝓒(↧(ComplexPoint X); ℤ))).inv
      (by change QuasiIso _; infer_instance)).trans
    (Localization.SmallShiftedHom.postcompEquiv
      (analyticSheafComplexIntIsoSingle X F).hom
      (by change QuasiIso _; infer_instance))

/-- The map induced on hypercohomology is composition with the coefficient map. -/
theorem hypercohomologyMap_apply
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X f n α = α.comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f)
      (zero_add n) := rfl

/-- An isomorphism of complexes induces an injective map on hypercohomology. -/
theorem hypercohomologyMap_injective_of_isIso
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) [IsIso f]
    (n : ℤ) : Function.Injective (hypercohomologyMap X f n) := by
  intro α β h
  have h' := congrArg (hypercohomologyMap X (inv f) n) h
  simpa only [← hypercohomologyMap_comp_apply, IsIso.hom_inv_id,
    hypercohomologyMap_id, AddMonoidHom.id_apply] using h'

/-- The comparison is precomposition and postcomposition by the canonical complex isomorphisms. -/
theorem analyticSheafCohomologyEquivExt_apply (F : AnalyticAdditiveSheaf X) (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X F) n) :
    analyticSheafCohomologyEquivExt X F n α =
      ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X (𝓒(↧(ComplexPoint X); ℤ))).inv).comp α
          (add_zero (n : ℤ))).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (analyticSheafComplexIntIsoSingle X F).hom) (zero_add (n : ℤ)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The cohomology/Ext comparison respects maps of coefficient sheaves. -/
theorem analyticSheafCohomologyEquivExt_naturality
    {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X F) n) :
    analyticSheafCohomologyEquivExt X G n
        (hypercohomologyMap X (analyticSheafComplexIntMap X f) n α) =
      (analyticSheafCohomologyEquivExt X F n α).comp (Abelian.Ext.mk₀ f) (add_zero n) := by
  rw [analyticSheafCohomologyEquivExt_apply, analyticSheafCohomologyEquivExt_apply]
  rw [hypercohomologyMap_apply]
  dsimp only [Abelian.Ext.comp, Abelian.Ext.mk₀]
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X))).injective
  simp only [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, analyticSheafComplexIntIsoSingle_naturality]
  simp [Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison carries the zero cohomology class to zero. -/
@[simp]
theorem analyticSheafCohomologyEquivExt_zero (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    analyticSheafCohomologyEquivExt X F n 0 = 0 := by
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X))).injective
  change _ = (0 : Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) F n).hom
  rw [Abelian.Ext.zero_hom]
  rw [analyticSheafCohomologyEquivExt_apply]
  simp only [Localization.SmallShiftedHom.equiv_comp]
  erw [hypercohomologyEquiv_zero X (analyticSheafComplexInt X F) (n : ℤ)]
  simp

set_option maxHeartbeats 1000000 in
/-- The cohomology/Ext comparison is additive. -/
theorem analyticSheafCohomologyEquivExt_add (F : AnalyticAdditiveSheaf X) (n : ℕ)
    (α β : Hypercohomology X (analyticSheafComplexInt X F) n) :
    analyticSheafCohomologyEquivExt X F n (α + β) =
      analyticSheafCohomologyEquivExt X F n α + analyticSheafCohomologyEquivExt X F n β := by
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X))).injective
  change _ = (analyticSheafCohomologyEquivExt X F n α +
    analyticSheafCohomologyEquivExt X F n β).hom
  rw [Abelian.Ext.add_hom]
  change _ = (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X)))
      (analyticSheafCohomologyEquivExt X F n α) +
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X)))
      (analyticSheafCohomologyEquivExt X F n β)
  have hadd := hypercohomologyEquiv_add X (analyticSheafComplexInt X F) (n : ℤ) α β
  rw [analyticSheafCohomologyEquivExt_apply, analyticSheafCohomologyEquivExt_apply,
    analyticSheafCohomologyEquivExt_apply]
  simp only [Localization.SmallShiftedHom.equiv_comp]
  rw [hadd]
  simp

/-- The cohomology/Ext comparison, as an isomorphism of abelian groups. -/
def analyticSheafCohomologyAddEquivExt (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Hypercohomology X (analyticSheafComplexInt X F) n ≃+
      Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) F n where
  toEquiv := analyticSheafCohomologyEquivExt X F n
  map_add' := analyticSheafCohomologyEquivExt_add X F n

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

local instance analyticSheafSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  analyticSheafExtHasDerivedCategory X

private def sheafCohomologySourceComparison :=
  Localization.SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (constantIntegerSheafComplexIntIsoSingleULift X).hom
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)

private def sheafCohomologyTargetComparison (F : AnalyticAdditiveSheaf X) :=
  Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (analyticSheafComplexIntIsoSingle X F).hom

/-- Hypercohomology of a degree-zero sheaf is its ordinary sheaf cohomology. -/
def analyticSheafHypercohomologyAddEquiv (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Hypercohomology X (analyticSheafComplexInt X F) n ≃+ Sheaf.H F n where
  toEquiv :=
    (Localization.SmallShiftedHom.precompEquiv.{1} (W := analyticQuasiIsomorphisms X)
      (constantIntegerSheafComplexIntIsoSingleULift X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (a := (n : ℤ))).symm.trans
    (Localization.SmallShiftedHom.postcompEquiv.{1} (W := analyticQuasiIsomorphisms X)
      (analyticSheafComplexIntIsoSingle X F).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (a := (n : ℤ)))
  map_add' α β := by
    apply Abelian.Ext.ext
    rw [Abelian.Ext.add_hom]
    show Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((sheafCohomologySourceComparison X).comp (α + β) _).comp (sheafCohomologyTargetComparison X F) _) =
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((sheafCohomologySourceComparison X).comp α _).comp (sheafCohomologyTargetComparison X F) _) +
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((sheafCohomologySourceComparison X).comp β _).comp (sheafCohomologyTargetComparison X F) _)
    simp only [Localization.SmallShiftedHom.equiv_comp, hypercohomologyEquiv_add,
      ShiftedHom.add_comp, ShiftedHom.comp_add]
    rfl

private lemma sheafCohomologySourceComparison_comp_comp_mk₀
    {L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ)
    (β : Hypercohomology X L n) (h : L ⟶ M) :
    ((sheafCohomologySourceComparison X).comp β (add_zero n)).comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl h) (zero_add n) =
    (sheafCohomologySourceComparison X).comp
      (β.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl h)
        (zero_add n)) (add_zero n) :=
  Localization.SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) _ β _
    (add_zero n) (zero_add n) (by simp)

/-- The comparison with ordinary sheaf cohomology respects coefficient maps. -/
lemma analyticSheafHypercohomologyAddEquiv_naturality
    {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X F) n) :
    analyticSheafHypercohomologyAddEquiv X G n
      (hypercohomologyMap X (analyticSheafComplexIntMap X f) n α) =
    Sheaf.H.map f n (analyticSheafHypercohomologyAddEquiv X F n α) := by
  show ((sheafCohomologySourceComparison X).comp
      (hypercohomologyMap X (analyticSheafComplexIntMap X f) n α) (add_zero _)).comp
      (sheafCohomologyTargetComparison X G) (zero_add _) =
    (((sheafCohomologySourceComparison X).comp α (add_zero _)).comp (sheafCohomologyTargetComparison X F)
      (zero_add _)).comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f)) (zero_add _)
  refine (sheafCohomologySourceComparison_comp_comp_mk₀ X _ _ _).trans (Eq.trans ?_
    ((congrArg (fun γ => γ.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X)
      (0 : ℤ) rfl ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f))
      (zero_add _)) (sheafCohomologySourceComparison_comp_comp_mk₀ X _ α _)).trans
        (sheafCohomologySourceComparison_comp_comp_mk₀ X _ _ _)).symm)
  congr 1
  change hypercohomologyMap X _ n (hypercohomologyMap X _ n α) =
    hypercohomologyMap X _ n (hypercohomologyMap X _ n α)
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  exact congrArg (fun g => hypercohomologyMap X g n α)
    (analyticSheafComplexIntIsoSingle_naturality X f)

/-- The ordinary sheaf-cohomology comparison respects coefficient maps. -/
lemma sheafCohomologyEquivExt_naturality {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) (n : ℕ)
    (α : Sheaf.H F n) :
    sheafCohomologyEquivExt X G n (Sheaf.H.map f n α) =
      (sheafCohomologyEquivExt X F n α).comp (Abelian.Ext.mk₀ f) (add_zero n) := by
  let e := (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).mapIso
    (show AddCommGrpCat.of (ULift ℤ) ≅ AddCommGrpCat.of ℤ from
      (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso)
  let η := (Abelian.extFunctor n).mapIso e.op
  exact congrArg (fun g => g α) (η.inv.naturality f)

/-- Integral-to-rational coefficient change agrees in the two cohomology presentations. -/
lemma integralToRationalCohomology_analyticSheafHypercohomologyAddEquiv (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X (𝓒(↧(ComplexPoint X); ℤ))) n) :
    integralToRationalCohomology X n
      (analyticSheafHypercohomologyAddEquiv X (𝓒(↧(ComplexPoint X); ℤ)) n α) =
    hypercohomologyAddEquivConstantCohomology ℚ X n
      (hypercohomologyMap X (analyticSheafComplexIntMap X
        (integerToFieldConstantSheaf ℚ X 1)) n α) :=
  (analyticSheafHypercohomologyAddEquiv_naturality X
    (integerToFieldConstantSheaf ℚ X 1) n α).symm

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary and hypercohomology comparisons give the same class in Ext. -/
lemma sheafCohomologyEquivExt_analyticSheafHypercohomologyAddEquiv (F : AnalyticAdditiveSheaf X) (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X F) n) :
    sheafCohomologyEquivExt X F n
        (analyticSheafHypercohomologyAddEquiv X F n α) =
      analyticSheafCohomologyEquivExt X F n α := by
  let e := (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).mapIso
    (show AddCommGrpCat.of (ULift ℤ) ≅ AddCommGrpCat.of ℤ from
      (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso)
  change (Abelian.Ext.mk₀ e.inv).comp
    (analyticSheafHypercohomologyAddEquiv X F n α) (zero_add n) = _
  let b := constantIntegerSheafComplexIntIsoSingleULift X
  have hb : Localization.SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      b.hom ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) =
      Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl b.inv := by
    apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_mk₀Inv, Localization.SmallShiftedHom.equiv_mk₀]
    congr 1
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← Functor.map_comp, b.hom_inv_id, CategoryTheory.Functor.map_id]
  change (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map e.inv)).comp
    (((Localization.SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      b.hom ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).comp α _).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (analyticSheafComplexIntIsoSingle X F).hom) _) _ = _
  rw [hb, analyticSheafCohomologyEquivExt_apply]
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  simp only [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  have hs : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map e.inv ≫
      b.inv = (analyticSheafComplexIntIsoSingle X (𝓒(↧(ComplexPoint X); ℤ))).inv := by
    change (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map e.inv ≫
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map e.hom ≫ _ = _
    rw [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [← Functor.map_comp_assoc, hs]
  rfl

end AlgebraicGeometry.ComplexPoint
