/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenCoverOrderedCechBicomplex
public import Other.AlgebraicTopology.RationalCechTotalAugmentation
public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularExcisionField

import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Rational ordered-intersection Čech chains

This is the coefficient-`ℚ` counterpart of the ordered-cover identification.  It is kept at
chain level so that its linear dual contains literal rational singular cochains on the genuine
finite intersections of an open cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial
open AlgebraicTopology.OrderedCechTuple

namespace AlgebraicTopology.Singular

variable {ι : Type} [LinearOrder ι] (X : TopCat) (U : ι → Set X)

/-- Rational singular chains on the nonempty finite intersections of an open cover. -/
public def rationalOpenCoverIntersectionChainModels : SupportChainModels ι (ModuleCat ℚ) where
  obj s := (TopCat.toSSet.obj (TopCat.of
    (openCoverIntersection X U s.unop.1))).chainComplex (ModuleCat.of ℚ ℚ)
  map {s t} f := SSet.chainComplexMap
    (TopCat.toSSet.map (openCoverIntersectionInclusion X U (leOfHom f.unop)))
    (ModuleCat.of ℚ ℚ)
  map_id s := by
    unfold SSet.chainComplexMap
    rw [openCoverIntersectionInclusion_refl]
    simp
  map_comp {r s t} f g := by
    unfold SSet.chainComplexMap
    rw [← Functor.map_comp, ← Functor.map_comp,
      openCoverIntersectionInclusion_comp]

/-- Rational chains commute canonically with the coproduct of a family of simplicial sets. -/
public def rationalChainsCoproductDiagramIso {κ : Type} (Y : κ → SSet) :
    Discrete.functor (fun i ↦
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (Y i)) ≅
      Discrete.functor Y ⋙
        (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    rintro ⟨A⟩ ⟨B⟩ ⟨⟨h⟩⟩
    change A = B at h
    subst B
    simp)

@[simp]
public theorem rationalChainsCoproductDiagramIso_hom_app {κ : Type}
    (Y : κ → SSet) (i : κ) :
    (rationalChainsCoproductDiagramIso Y).hom.app (Discrete.mk i) = 𝟙 _ :=
  rfl

/-- Rational chains of a coproduct are the coproduct of the rational chain complexes. -/
public def rationalChainsCoproductIso {κ : Type} (Y : κ → SSet) :
    (∐ fun i ↦ (Y i).chainComplex (ModuleCat.of ℚ ℚ)) ≅
      (∐ Y).chainComplex (ModuleCat.of ℚ ℚ) := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  letI : PreservesColimitsOfShape (Discrete κ) F :=
    HomologicalComplex.preservesColimitsOfShape_of_eval F (fun n => by
      change PreservesColimitsOfShape (Discrete κ)
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk n)) ⋙
            sigmaConst.obj (ModuleCat.of ℚ ℚ))
      infer_instance)
  exact (HasColimit.isoOfNatIso (rationalChainsCoproductDiagramIso Y)).trans
    (preservesColimitIso F (Discrete.functor Y)).symm

@[reassoc]
public theorem rationalChainsCoproductIso_hom_ι {κ : Type}
    (Y : κ → SSet) (i : κ) :
    Sigma.ι (fun j ↦ (Y j).chainComplex (ModuleCat.of ℚ ℚ)) i ≫
        (rationalChainsCoproductIso Y).hom =
      SSet.chainComplexMap (Sigma.ι Y i) (ModuleCat.of ℚ ℚ) := by
  simp only [rationalChainsCoproductIso, Iso.trans_hom, ← Category.assoc,
    HasColimit.isoOfNatIso_ι_hom, rationalChainsCoproductDiagramIso_hom_app,
    Category.id_comp, Iso.symm_hom, ι_preservesColimitIso_inv]

/-- In a fixed Čech degree, the ordered rational intersection chains identify with the actual
rational augmented-Čech column. -/
public def rationalOpenCoverOrderedCechColumnIso (p : ℕ) :
    (rationalOpenCoverIntersectionChainModels X U).cechObject TupleClass.all p ≅
      (rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U))).X p :=
  rationalChainsCoproductIso (openCoverOrderedIntersectionSSet X U p) ≪≫
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).mapIso
        (openCoverOrderedCechIso X U (Opposite.op (SimplexCategory.mk p)))

@[reassoc]
public theorem rationalOpenCoverOrderedCechColumnIso_hom_ι (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // True}) :
    Sigma.ι (fun b ↦
        (openCoverOrderedIntersectionSSet X U p b).chainComplex
          (ModuleCat.of ℚ ℚ)) a ≫
        (rationalOpenCoverOrderedCechColumnIso X U p).hom =
      SSet.chainComplexMap
        (openCoverTupleIntersectionToCechSummand X U
          (n := Opposite.op (SimplexCategory.mk p)) a)
        (ModuleCat.of ℚ ℚ) := by
  change Sigma.ι (fun b ↦
      (openCoverOrderedIntersectionSSet X U p b).chainComplex
        (ModuleCat.of ℚ ℚ)) a ≫
      ((rationalChainsCoproductIso
          (openCoverOrderedIntersectionSSet X U p)).hom ≫
        ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
          (ModuleCat.of ℚ ℚ)).map
            (openCoverOrderedCechIso X U
              (Opposite.op (SimplexCategory.mk p))).hom) = _
  rw [← Category.assoc, rationalChainsCoproductIso_hom_ι]
  change SSet.chainComplexMap
      (Sigma.ι (openCoverOrderedIntersectionSSet X U p) a)
        (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap
        (openCoverOrderedCechIso X U
          (Opposite.op (SimplexCategory.mk p))).hom
        (ModuleCat.of ℚ ℚ) = _
  rw [← Functor.map_comp, openCoverOrderedCechIso_hom, openCoverOrderedCechMap,
    Sigma.ι_desc]

set_option backward.isDefEq.respectTransparency false in
/-- The preceding formula in the `SupportChainModels` presentation. -/
@[reassoc]
public theorem rationalOpenCoverOrderedCechColumnIso_model_hom_ι (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // TupleClass.all.mem p _a}) :
    Sigma.ι (fun b : {_b : Fin (p + 1) → ι // TupleClass.all.mem p _b} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        (rationalOpenCoverOrderedCechColumnIso X U p).hom =
      SSet.chainComplexMap
        (openCoverTupleIntersectionToCechSummand X U
          (n := Opposite.op (SimplexCategory.mk p)) a)
        (ModuleCat.of ℚ ℚ) := by
  change Sigma.ι (fun b ↦
      (openCoverOrderedIntersectionSSet X U p b).chainComplex
        (ModuleCat.of ℚ ℚ)) a ≫
        (rationalOpenCoverOrderedCechColumnIso X U p).hom = _
  rw [rationalOpenCoverOrderedCechColumnIso_hom_ι]

set_option backward.isDefEq.respectTransparency false in
/-- On one ordered summand, the outer differential is the signed sum of the inclusions into
its tuple faces, with rational coefficients. -/
@[reassoc]
public theorem rationalOpenCoverIntersectionChainModels_ι_comp_d (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a}) :
    Sigma.ι (fun b : {_b : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _b} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        ((rationalOpenCoverIntersectionChainModels X U).cechComplex TupleClass.all).d
          (p + 1) p =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.val) •
        ((rationalOpenCoverIntersectionChainModels X U).face
            (openCoverCechTupleFace_support_subset a i) ≫
          Sigma.ι (fun b : {_b : Fin (p + 1) → ι // TupleClass.all.mem p _b} ↦
            (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1))
              (openCoverCechTupleFace a i)) := by
  rw [SupportChainModels.cechComplex_d, SupportChainModels.ι_realize, boundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Finsupp.single (Fin.removeNth i a.1) ((-1 : ℤ) ^ i.val * 1) =
      ((-1 : ℤ) ^ i.val) • Finsupp.single (Fin.removeNth i a.1) 1 by simp, map_zsmul]
  congr 1
  rw [SupportChainModels.realizeAux_single]
  unfold SupportChainModels.faceOrZero
  rw [dif_pos (by
    rw [tupleSupport_subset_iff]
    exact Set.range_comp_subset_range i.succAbove a.1), SupportChainModels.ιOrZero_of_mem]
  rfl

omit [LinearOrder ι] in
set_option backward.isDefEq.respectTransparency false in
/-- The outer differential of the actual rational Čech bicomplex is the alternating sum of its
Čech face maps. -/
public theorem rationalCechBicomplex_d_eq_sum_faces (p : ℕ) :
    (rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U))).d (p + 1) p =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.val) •
        (SimplicialObject.Augmented.drop.obj
          (rationalCechAugmentedChains
            (Arrow.mk (coverSmallPresentation X U)))).δ i := by
  change (AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj
      (rationalCechAugmentedChains
        (Arrow.mk (coverSmallPresentation X U))))).d (p + 1) p = _
  rw [AlternatingFaceMapComplex.obj_d_eq]

omit [LinearOrder ι] in
/-- Čech faces with rational coefficients are the maps induced by the simplicial Čech faces. -/
public theorem rationalCechAugmentedChains_δ (p : ℕ) (i : Fin (p + 2)) :
    (SimplicialObject.Augmented.drop.obj
      (rationalCechAugmentedChains
        (Arrow.mk (coverSmallPresentation X U)))).δ i =
      SSet.chainComplexMap
        ((Arrow.mk (coverSmallPresentation X U)).cechNerve.δ i)
        (ModuleCat.of ℚ ℚ) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The rational chain map from one ordered intersection summand into its actual Čech column. -/
public def rationalOpenCoverTupleCechSummandChainMap (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // TupleClass.all.mem p _a}) :
    (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport a.1) ⟶
      (rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U))).X p :=
  SSet.chainComplexMap
    (openCoverTupleIntersectionToCechSummand X U
      (n := Opposite.op (SimplexCategory.mk p)) a)
    (ModuleCat.of ℚ ℚ)

/-- In outer degree zero, the canonical map from an ordered intersection summand followed by
the Čech augmentation is the canonical map to cover-small singular chains. -/
@[reassoc]
public theorem rationalOpenCoverTupleCechSummandChainMap_comp_outerAugmentation_zero
    (a : {_a : Fin 1 → ι // TupleClass.all.mem 0 _a}) :
    rationalOpenCoverTupleCechSummandChainMap X U 0 a ≫
        (rationalCechOuterAugmentation
          (Arrow.mk (coverSmallPresentation X U))).f 0 =
      SSet.chainComplexMap
        (openCoverTupleIntersectionToSmall X U
          (n := Opposite.op (SimplexCategory.mk 0)) a)
        (ModuleCat.of ℚ ℚ) := by
  change SSet.chainComplexMap
      (openCoverTupleIntersectionToCechSummand X U
        (n := Opposite.op (SimplexCategory.mk 0)) a)
      (ModuleCat.of ℚ ℚ) ≫
    SSet.chainComplexMap
      ((Arrow.mk (coverSmallPresentation X U)).augmentedCechNerve.hom.app
        (Opposite.op (SimplexCategory.mk 0))) (ModuleCat.of ℚ ℚ) = _
  rw [← Functor.map_comp,
    openCoverTupleIntersectionToCechSummand_comp_augmentation]
  rfl

/-- A rational geometric model face is the chain map induced by the inclusion of intersections. -/
public theorem rationalOpenCoverIntersectionChainModels_face_eq (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a})
    (i : Fin (p + 2)) :
    (rationalOpenCoverIntersectionChainModels X U).face
        (openCoverCechTupleFace_support_subset a i) =
      SSet.chainComplexMap
        (TopCat.toSSet.map (openCoverTupleFaceIntersectionInclusion X U a i))
        (ModuleCat.of ℚ ℚ) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- One rational ordered-intersection summand commutes with each actual Čech face. -/
@[reassoc]
public theorem rationalOpenCoverTupleCechSummandChainMap_comp_face (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a})
    (i : Fin (p + 2)) :
    rationalOpenCoverTupleCechSummandChainMap X U (p + 1) a ≫
        (SimplicialObject.Augmented.drop.obj
          (rationalCechAugmentedChains
            (Arrow.mk (coverSmallPresentation X U)))).δ i =
      (rationalOpenCoverIntersectionChainModels X U).face
          (openCoverCechTupleFace_support_subset a i) ≫
        rationalOpenCoverTupleCechSummandChainMap X U p
          (openCoverCechTupleFace a i) := by
  rw [rationalOpenCoverIntersectionChainModels_face_eq]
  have h := congrArg
    (fun f ↦ ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map f)
    (openCoverTupleIntersectionToCechSummand_comp_δ X U a i).symm
  simpa only [rationalOpenCoverTupleCechSummandChainMap,
    rationalCechAugmentedChains_δ, Functor.map_comp] using h

set_option backward.isDefEq.respectTransparency false in
/-- The rational column isomorphism restricts to the canonical map on each summand. -/
@[reassoc]
public theorem rationalOpenCoverOrderedCechColumnIso_hom_ι_chainMap (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // TupleClass.all.mem p _a}) :
    Sigma.ι (fun b : {_b : Fin (p + 1) → ι // TupleClass.all.mem p _b} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        (rationalOpenCoverOrderedCechColumnIso X U p).hom =
      rationalOpenCoverTupleCechSummandChainMap X U p a :=
  rationalOpenCoverOrderedCechColumnIso_model_hom_ι X U p a

set_option backward.isDefEq.respectTransparency false in
/-- The rational column isomorphisms commute with outer differentials on every summand. -/
public theorem rationalOpenCoverOrderedCechColumnIso_comm_ι (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a}) :
    (Sigma.ι (fun b : {_b : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _b} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
      (rationalOpenCoverOrderedCechColumnIso X U (p + 1)).hom) ≫
        (rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U))).d (p + 1) p =
      Sigma.ι (fun b : {_b : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _b} ↦
          (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        (((rationalOpenCoverIntersectionChainModels X U).cechComplex TupleClass.all).d
          (p + 1) p ≫ (rationalOpenCoverOrderedCechColumnIso X U p).hom) := by
  rw [← Category.assoc, rationalOpenCoverOrderedCechColumnIso_hom_ι_chainMap,
    rationalCechBicomplex_d_eq_sum_faces, Preadditive.comp_sum,
    rationalOpenCoverIntersectionChainModels_ι_comp_d, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  rw [Category.assoc, rationalOpenCoverOrderedCechColumnIso_hom_ι_chainMap]
  exact rationalOpenCoverTupleCechSummandChainMap_comp_face X U p a i

set_option backward.isDefEq.respectTransparency false in
/-- The rational column isomorphisms commute with every outer differential. -/
public theorem rationalOpenCoverOrderedCechColumnIso_comm (m n : ℕ)
    (hmn : (ComplexShape.down ℕ).Rel m n) :
    (rationalOpenCoverOrderedCechColumnIso X U m).hom ≫
        (rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U))).d m n =
      ((rationalOpenCoverIntersectionChainModels X U).cechComplex TupleClass.all).d m n ≫
        (rationalOpenCoverOrderedCechColumnIso X U n).hom := by
  obtain rfl : m = n + 1 := hmn.symm
  apply Sigma.hom_ext
  intro a
  exact rationalOpenCoverOrderedCechColumnIso_comm_ι X U n a

/-- The ordered rational intersection bicomplex is the actual rational Čech bicomplex. -/
public def rationalOpenCoverOrderedCechBicomplexIso :
    (rationalOpenCoverIntersectionChainModels X U).cechComplex TupleClass.all ≅
      rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U)) :=
  HomologicalComplex.Hom.isoOfComponents
    (rationalOpenCoverOrderedCechColumnIso X U)
    (rationalOpenCoverOrderedCechColumnIso_comm X U)

/-- The induced isomorphism of direct-sum rational total complexes. -/
public def rationalOpenCoverOrderedCechTotalIso :
    (rationalOpenCoverIntersectionChainModels X U).cechTotal TupleClass.all ≅
      (rationalCechBicomplex
        (Arrow.mk (coverSmallPresentation X U))).total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.mapIso (rationalOpenCoverOrderedCechBicomplexIso X U)
    (ComplexShape.down ℕ)

/-- The normalized rational Čech total maps to the rational chains subordinate to the cover. -/
public def rationalOpenCoverNormalizedCechTotalAugmentation :
    (rationalOpenCoverIntersectionChainModels X U).cechTotal TupleClass.strictMono ⟶
      CoverSmallRationalSingularChainComplex X U :=
  (rationalOpenCoverIntersectionChainModels X U).totalNormalizedInclusion ≫
    (rationalOpenCoverOrderedCechTotalIso X U).hom ≫
      rationalCechTotalAugmentationToTarget
        (Arrow.mk (coverSmallPresentation X U))

set_option linter.style.haveILetI false in
/-- The normalized rational ordered-intersection total computes cover-small rational singular
chains, without hypotheses on the intersections. -/
public theorem rationalOpenCoverNormalizedCechTotalAugmentation_quasiIso :
    QuasiIso (rationalOpenCoverNormalizedCechTotalAugmentation X U) := by
  let M := rationalOpenCoverIntersectionChainModels X U
  letI : QuasiIso M.totalNormalizedInclusion :=
    M.totalNormalizationHomotopyEquiv.quasiIso_inv
  letI : IsIso (rationalOpenCoverOrderedCechTotalIso X U).hom :=
    (rationalOpenCoverOrderedCechTotalIso X U).isIso_hom
  letI : QuasiIso (rationalCechTotalAugmentationToTarget
      (Arrow.mk (coverSmallPresentation X U))) :=
    coverSmallRationalCechTotalAugmentationToTarget_quasiIso X U
  change QuasiIso
    (M.totalNormalizedInclusion ≫
      (rationalOpenCoverOrderedCechTotalIso X U).hom ≫
        rationalCechTotalAugmentationToTarget
          (Arrow.mk (coverSmallPresentation X U)))
  infer_instance

/-- The normalized rational ordered-intersection Čech total mapped to all rational singular
chains of the ambient space. -/
public def rationalOpenCoverNormalizedCechTotalToSingular :
    (rationalOpenCoverIntersectionChainModels X U).cechTotal
        TupleClass.strictMono ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) :=
  rationalOpenCoverNormalizedCechTotalAugmentation X U ≫
    coverSmallRationalSingularChainInclusion X U

set_option linter.style.haveILetI false in
/-- If the cover has a universal member, the normalized rational Čech total computes all
singular chains directly, without open-cover or subdivision hypotheses. -/
public theorem rationalOpenCoverNormalizedCechTotalToSingular_quasiIso_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    QuasiIso (rationalOpenCoverNormalizedCechTotalToSingular X U) := by
  letI : QuasiIso (rationalOpenCoverNormalizedCechTotalAugmentation X U) :=
    rationalOpenCoverNormalizedCechTotalAugmentation_quasiIso X U
  letI : IsIso (coverSmallRationalSingularChainInclusion X U) :=
    coverSmallRationalSingularChainInclusion_isIso_of_member_eq_univ X U j hj
  exact quasiIso_comp _ _

set_option linter.style.haveILetI false in
/-- Every open cover is computed by its normalized rational singular Čech total. -/
public theorem rationalOpenCoverNormalizedCechTotalToSingular_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (rationalOpenCoverNormalizedCechTotalToSingular X U) := by
  letI : QuasiIso (rationalOpenCoverNormalizedCechTotalAugmentation X U) :=
    rationalOpenCoverNormalizedCechTotalAugmentation_quasiIso X U
  have hsmall : QuasiIso (coverSmallRationalSingularChainInclusion X U) := by
    rw [← coverSmallRationalChainHomotopyEquiv_of_openCover_hom X U hUopen hUcover]
    exact (coverSmallRationalChainHomotopyEquiv_of_openCover X U hUopen hUcover).quasiIso_hom
  letI : QuasiIso (coverSmallRationalSingularChainInclusion X U) := hsmall
  exact quasiIso_comp _ _

end AlgebraicTopology.Singular
