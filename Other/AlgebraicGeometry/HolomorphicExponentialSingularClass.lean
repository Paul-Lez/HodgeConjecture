/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialSingularCochain
public import Other.AlgebraicGeometry.ChernRelativeClass
public import Other.AlgebraicGeometry.ComplexSingularComparison
public import Other.Algebra.Homology.MappingConeCocycle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# The exponential comparison in the complex of singular sheaves

The evaluation and winding maps are cochains in the integer-indexed singular resolution.
The lifted-cochain identity identifies the winding cocycle with the negative connecting
class of the exponential sequence. The sign is the one of mathlib's cone triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular CochainComplex.HomComplex CategoryTheory.Localization

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance exponentialSingularClassTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

local instance exponentialSingularClassDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- A nonnegative term of the extended singular complex is the corresponding cochain sheaf. -/
abbrev singularCochainSheafTermIso (n : ℕ) :
    (singularCochainSheafComplexInt X ℚ).X (n : ℤ) ≅
      singularCochainSheaf ℚ (TopCat.of (ComplexPoint X)) n :=
  (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))).extendXIso
    ComplexShape.embeddingUpNat (i := n) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The term identification intertwines the singular differentials. -/
@[reassoc]
theorem singularCochainSheafTermIso_inv_d (n : ℕ) :
    (singularCochainSheafTermIso X n).inv ≫
        (singularCochainSheafComplexInt X ℚ).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      singularCochainSheafCoboundary ℚ (TopCat.of (ComplexPoint X)) n ≫
        (singularCochainSheafTermIso X (n + 1)).inv := by
  dsimp only [singularCochainSheafTermIso, singularCochainSheafComplexInt]
  erw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat (i := n) (j := n + 1) rfl rfl]
  simp only [Iso.inv_hom_id_assoc, singularCochainSheafComplex_d]

/-- Evaluation of holomorphic functions, as a cochain with a single sheaf as source. -/
def holomorphicSingularZeroCochain :
    Cochain ((analyticSingleFunctor X).obj (holomorphicAdditiveSheaf X d))
      (singularCochainSheafComplexInt X ℚ) 0 :=
  Cochain.fromSingleMk
    (holomorphicToSingularZeroSheaf X d ≫ (singularCochainSheafTermIso X 0).inv) (zero_add 0)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Winding of holomorphic units, as a cocycle in the singular resolution. -/
def holomorphicSingularOneCocycle :
    Cocycle ((analyticSingleFunctor X).obj (holomorphicUnitSheaf X d))
      (singularCochainSheafComplexInt X ℚ) 1 :=
  Cocycle.fromSingleMk
    (holomorphicUnitToSingularOneSheaf X d ≫ (singularCochainSheafTermIso X 1).inv)
    (zero_add 1) 2 rfl (by
      erw [Category.assoc, singularCochainSheafTermIso_inv_d X 1, ← Category.assoc,
        holomorphicUnitToSingularOneSheaf_comp_coboundary, zero_comp])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integer constants as a zero-cocycle in the singular resolution. -/
def integerSingularZeroCocycle :
    Cocycle ((analyticSingleFunctor X).obj (constantIntegerSheaf X))
      (singularCochainSheafComplexInt X ℚ) 0 :=
  Cocycle.fromSingleMk
    (integerToFieldConstantSheaf ℚ X 1 ≫
      constantsToSingularCochainZeroSheaf ℚ (TopCat.of (ComplexPoint X)) ≫
        (singularCochainSheafTermIso X 0).inv) (zero_add 0) 1 rfl (by
      erw [Category.assoc, Category.assoc, singularCochainSheafTermIso_inv_d X 0,
        ← Category.assoc (constantsToSingularCochainZeroSheaf ℚ _),
        constantsToSingularCochainZeroSheaf_comp_coboundary, zero_comp, comp_zero])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation extends the integer coefficient cocycle. -/
theorem holomorphicSingularZeroCochain_precomp_integer :
    (Cochain.ofHom ((analyticSingleFunctor X).map (integerConstantsToHolomorphicSheaf X d))).comp
        (holomorphicSingularZeroCochain X d) (zero_add 0) =
      (integerSingularZeroCocycle X : Cochain _ _ 0) := by
  rw [holomorphicSingularZeroCochain, ← Cochain.fromSingleMk_precomp]
  change Cochain.fromSingleMk _ (zero_add (0 : ℤ)) = Cochain.fromSingleMk _ (zero_add (0 : ℤ))
  rw [← Category.assoc, integerConstantsToHolomorphicSheaf_comp_toSingularZeroSheaf,
    Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Differentiating evaluation is winding precomposed with the exponential. -/
theorem holomorphicSingularZeroCochain_d :
    δ 0 1 (holomorphicSingularZeroCochain X d) =
      ((holomorphicSingularOneCocycle X d).precomp
        ((analyticSingleFunctor X).map (holomorphicExponential X d))).1 := by
  rw [holomorphicSingularZeroCochain, Cochain.δ_fromSingleMk _ _ _ 1 (zero_add 1)]
  change _ = (Cochain.ofHom ((analyticSingleFunctor X).map (holomorphicExponential X d))).comp
    (Cochain.fromSingleMk _ (zero_add 1)) (zero_add 1)
  erw [← Cochain.fromSingleMk_precomp, Category.assoc, singularCochainSheafTermIso_inv_d X 0,
    ← Category.assoc, ← holomorphicExponential_comp_toSingularOneSheaf, Category.assoc]

/-- The exponential short complex, placed in degree zero. -/
abbrev exponentialSingleShortComplex : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ) :=
  (holomorphicExponentialSequence X d).map (analyticSingleFunctor X)

set_option backward.isDefEq.respectTransparency false in
/-- Winding on the exponential cone represents the positive projection, hence the negative
of the distinguished triangle's connecting morphism. -/
theorem holomorphicSingularOneCocycle_cone_class :
    CohomologyClass.mk ((holomorphicSingularOneCocycle X d).precomp
      (CochainComplex.mappingCone.descShortComplex (exponentialSingleShortComplex X d))) =
    CohomologyClass.mk ((CochainComplex.mappingCone.fst
      (exponentialSingleShortComplex X d).f).postcomp
        (Cocycle.homOf (integerSingularZeroCocycle X))) := by
  apply CochainComplex.mappingCone.cocycleClass_precomp_descShortComplex_eq
    (exponentialSingleShortComplex X d) (singularCochainSheafComplexInt X ℚ)
    (Cocycle.homOf (integerSingularZeroCocycle X)) (holomorphicSingularZeroCochain X d)
    (holomorphicSingularOneCocycle X d)
  · rw [Cocycle.cochain_ofHom_homOf_eq_coe]
    exact holomorphicSingularZeroCochain_precomp_integer X d
  · exact holomorphicSingularZeroCochain_d X d

set_option backward.isDefEq.respectTransparency false in
/-- The sign-calibrated exponential comparison in the homotopy category of sheaf complexes. -/
theorem holomorphicSingularOneCocycle_cone_quotient :
    (HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
        (CochainComplex.mappingCone.descShortComplex (exponentialSingleShortComplex X d)) ≫
      (HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
        (Cocycle.equivHomShift.symm (holomorphicSingularOneCocycle X d)) =
    -(HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
      ((CochainComplex.mappingCone.triangle (exponentialSingleShortComplex X d).f).mor₃ ≫
        (Cocycle.homOf (integerSingularZeroCocycle X))⟦(1 : ℤ)⟧') := by
  apply CochainComplex.mappingCone.quotient_map_descShortComplex_comp_cocycle_eq_neg
    (exponentialSingleShortComplex X d) (singularCochainSheafComplexInt X ℚ)
    (Cocycle.homOf (integerSingularZeroCocycle X)) (holomorphicSingularZeroCochain X d)
    (holomorphicSingularOneCocycle X d)
  · rw [Cocycle.cochain_ofHom_homOf_eq_coe]
    exact holomorphicSingularZeroCochain_precomp_integer X d
  · exact holomorphicSingularZeroCochain_d X d

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The integer cocycle is the standard rational singular augmentation, with its usual source identification. -/
theorem integerSingularZeroCocycle_homOf :
    Cocycle.homOf (integerSingularZeroCocycle X) =
      (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
        integerToFieldConstantSheafComplexInt ℚ X 1 ≫ constantsToSingularCochainComplexInt X ℚ := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  dsimp only [integerSingularZeroCocycle, Cocycle.homOf, Cocycle.fromSingleMk, Cocycle.mk]
  erw [Cochain.fromSingleMk_v]
  simp only [analyticSheafComplexIntIsoSingle, HomologicalComplex.extendSingleIso_inv_f]
  rw [integerToFieldConstantSheafComplexInt, constantsToSingularCochainComplexInt]
  erw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl,
    HomologicalComplex.extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl]
  simp [constantsToSingularCochainSheafComplex, singularCochainSheafTermIso,
    CochainComplex.single₀, HomologicalComplex.single_map_f_self,
    Category.assoc, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  erw [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing the exponential extension class by its cone presentation recovers the triangle boundary. -/
theorem exponential_cone_comp_extClass :
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      (CochainComplex.mappingCone.descShortComplex (exponentialSingleShortComplex X d))).comp
        (holomorphicExponentialSequence_shortExact X d).extClass (add_zero (1 : ℤ)) =
      SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (CochainComplex.mappingCone.triangle (exponentialSingleShortComplex X d).f).mor₃ := by
  apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk,
    ShiftedHom.mk₀_comp]
  erw [show (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (holomorphicExponentialSequence_shortExact X d).extClass =
        (holomorphicExponentialSequence_shortExact X d).extClass.hom from rfl,
    ShortComplex.ShortExact.extClass_hom]
  simp [ShortComplex.ShortExact.singleδ, DerivedCategory.triangleOfSESδ, ShiftedHom.map,
    SingleFunctors.evaluation, -DerivedCategory.Q_obj_single_obj,
    DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
    DerivedCategory.singleFunctorsPostcompQIso_inv_hom, CochainComplex.singleFunctors,
    ShortComplex.map, CochainComplex.singleFunctor, analyticSingleFunctor,
    exponentialSingleShortComplex, Category.comp_id, SingleFunctors.postcomp]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The repository's rational exponential class is represented by negative winding in the
standard singular resolution. Both the coefficient normalization and the cone sign are fixed. -/
theorem rationalChernShiftedHom_comp_singularAugmentation :
    (rationalChernShiftedHom X d).comp
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (constantsToSingularCochainComplexInt X ℚ)) (zero_add (1 : ℤ)) =
    SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
      (-Cocycle.equivHomShift.symm (holomorphicSingularOneCocycle X d)) := by
  apply (SmallShiftedHom.precompEquiv
    (CochainComplex.mappingCone.descShortComplex (exponentialSingleShortComplex X d))
    (by
      change QuasiIso _
      exact CochainComplex.mappingCone.quasiIso_descShortComplex
        ((holomorphicExponentialSequence_shortExact X d).map_of_exact
          (HomologicalComplex.single _ _ _))) (a := (1 : ℤ))).injective
  change (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl _).comp _ (add_zero (1 : ℤ)) =
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl _).comp _ (add_zero (1 : ℤ))
  unfold rationalChernShiftedHom
  rw [← SmallShiftedHom.comp_assoc _ _ _ _ (add_zero (1 : ℤ)) (zero_add (1 : ℤ)) (by omega),
    ← SmallShiftedHom.comp_assoc _ _ _ _ (add_zero (1 : ℤ)) (zero_add (1 : ℤ)) (by omega),
    exponential_cone_comp_extClass]
  apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀,
    SmallShiftedHom.equiv_mk, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  simp only [ShiftedHom.map, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
  have h := holomorphicSingularOneCocycle_cone_quotient X d
  rw [← Functor.map_comp, ← Functor.map_neg] at h
  have hD := DerivedCategory.Q_map_eq_of_homotopy (AnalyticAdditiveSheaf X) (HomotopyCategory.homotopyOfEq _ _ h)
  rw [Functor.map_comp, Functor.map_neg, Functor.map_comp] at hD
  simp only [Category.assoc]
  rw [← (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) (1 : ℤ)).map_comp,
    ← DerivedCategory.Q.map_comp, Category.assoc, ← integerSingularZeroCocycle_homOf]
  erw [← Functor.commShiftIso_hom_naturality]
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.assoc] using!
    congrArg (fun f => -f ≫ (Functor.commShiftIso DerivedCategory.Q (1 : ℤ)).hom.app
      (singularCochainSheafComplexInt X ℚ)) hD.symm

end AlgebraicGeometry.ComplexPoint
