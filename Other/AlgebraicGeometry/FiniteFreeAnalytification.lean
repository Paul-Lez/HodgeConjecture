/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitEndomorphismComparison
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Degree-zero comparison for finite free module sheaves

The degree-zero comparison on tensor-unit endomorphisms extends entrywise to matrices between
finite free sheaves. This is the finite-sum form needed when both terms of a twist presentation
have degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace SheafOfModules

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat} [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]

/-- The coordinate projection from a finite free sheaf, defined directly from its coproduct
universal property. This avoids making the chosen coproduct definitionally equal to a chosen
biproduct. -/
def πFree {I : Type} [DecidableEq I] (i : I) : free (R := R) I ⟶ unit R :=
  Cofan.IsColimit.desc (isColimitFreeCofan (R := R) I)
    (fun j ↦ if j = i then 𝟙 _ else 0)

@[reassoc (attr := simp)]
lemma ιFree_πFree {I : Type} [DecidableEq I] (i j : I) :
    ιFree (R := R) j ≫ πFree (R := R) i = if j = i then 𝟙 _ else 0 := by
  exact Cofan.IsColimit.fac (isColimitFreeCofan (R := R) I) _ j

/-- A matrix of scalar endomorphisms defines a map between finite free sheaves. -/
def matrix {I K : Type} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (a : I → K → (unit R ⟶ unit R)) : free (R := R) I ⟶ free (R := R) K :=
  ∑ i, ∑ k, πFree (R := R) i ≫ a i k ≫ ιFree (R := R) k

@[simp]
lemma ιFree_matrix_πFree {I K : Type} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] (a : I → K → (unit R ⟶ unit R)) (i : I) (k : K) :
    ιFree (R := R) i ≫ matrix (R := R) a ≫ πFree (R := R) k = a i k := by
  simp [matrix, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
    comp_ite, ite_comp]

/-- Coordinate projections and inclusions resolve the identity of a finite free sheaf. -/
lemma sum_πFree_ιFree (I : Type) [Fintype I] [DecidableEq I] :
    ∑ i, πFree (R := R) i ≫ ιFree (R := R) i = 𝟙 (free (R := R) I) := by
  apply Cofan.IsColimit.hom_ext (isColimitFreeCofan (R := R) I)
  intro j
  change ιFree (R := R) j ≫ (∑ i, πFree (R := R) i ≫ ιFree (R := R) i) =
    ιFree (R := R) j ≫ 𝟙 (free (R := R) I)
  simp [Preadditive.comp_sum, Category.assoc, comp_ite, ite_comp]

/-- Maps out of a finite free sheaf are determined by their matrix entries. -/
lemma hom_ext_matrixEntries {I K : Type} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] {f g : free (R := R) I ⟶ free (R := R) K}
    (h : ∀ i k, ιFree (R := R) i ≫ f ≫ πFree (R := R) k =
      ιFree (R := R) i ≫ g ≫ πFree (R := R) k) : f = g := by
  apply Cofan.IsColimit.hom_ext (isColimitFreeCofan (R := R) I)
  intro i
  change ιFree (R := R) i ≫ f = ιFree (R := R) i ≫ g
  rw [← Category.comp_id (ιFree (R := R) i ≫ f),
    ← Category.comp_id (ιFree (R := R) i ≫ g), ← sum_πFree_ιFree (R := R) K]
  simp only [Preadditive.comp_sum, Category.assoc]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Category.assoc] using congrArg
    (fun q ↦ q ≫ ιFree (R := R) k) (h i k)

end SheafOfModules

namespace AlgebraicGeometry.ComplexPoint

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance finiteFreeComparison_siteContinuous :
    (Opens.map (underlyingContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map (underlyingContinuousMap X))
    (coverPreserving_opens_map (underlyingContinuousMap X))

/-- Analytification of a free algebraic module sheaf is the free holomorphic module sheaf of
the same rank. -/
def unitFreeAnalytificationIso (I : Type) :
    (moduleAnalytification X d).obj
        (SheafOfModules.free (R := X.left.ringCatSheaf) I) ≅
      SheafOfModules.free (R := holomorphicRingSheaf X d) I := by
  letI : PreservesColimitsOfShape (Discrete I) (moduleAnalytification X d) :=
    (moduleAnalytificationAdjunction X d).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    (moduleAnalytification X d) I this
    (moduleAnalytificationUnitIso X d).symm).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma unitFreeAnalytificationIso_inv_ιFree (I : Type) (i : I) :
    SheafOfModules.ιFree (R := holomorphicRingSheaf X d) i ≫
        (unitFreeAnalytificationIso X d I).inv =
      (moduleAnalytificationUnitIso X d).inv ≫
        (moduleAnalytification X d).map
          (SheafOfModules.ιFree (R := X.left.ringCatSheaf) i) := by
  letI : PreservesColimitsOfShape (Discrete I) (moduleAnalytification X d) :=
    (moduleAnalytificationAdjunction X d).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact SheafOfModules.ιFree_mapFreeIso_hom
    (moduleAnalytification X d) I (moduleAnalytificationUnitIso X d).symm i

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma unitFreeAnalytificationIso_hom_πFree (I : Type) [Finite I] [DecidableEq I] (i : I) :
    (unitFreeAnalytificationIso X d I).hom ≫
        SheafOfModules.πFree (R := holomorphicRingSheaf X d) i =
      (moduleAnalytification X d).map
          (SheafOfModules.πFree (R := X.left.ringCatSheaf) i) ≫
        (moduleAnalytificationUnitIso X d).hom := by
  rw [← cancel_epi (unitFreeAnalytificationIso X d I).inv]
  apply Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R := holomorphicRingSheaf X d) I)
  intro j
  change SheafOfModules.ιFree (R := holomorphicRingSheaf X d) j ≫
      ((unitFreeAnalytificationIso X d I).inv ≫
        ((unitFreeAnalytificationIso X d I).hom ≫
          SheafOfModules.πFree (R := holomorphicRingSheaf X d) i)) =
    SheafOfModules.ιFree (R := holomorphicRingSheaf X d) j ≫
      ((unitFreeAnalytificationIso X d I).inv ≫
        ((moduleAnalytification X d).map
          (SheafOfModules.πFree (R := X.left.ringCatSheaf) i) ≫
            (moduleAnalytificationUnitIso X d).hom))
  calc
    _ = SheafOfModules.ιFree (R := holomorphicRingSheaf X d) j ≫
        SheafOfModules.πFree (R := holomorphicRingSheaf X d) i := by simp
    _ = if j = i then 𝟙 _ else 0 :=
      SheafOfModules.ιFree_πFree (R := holomorphicRingSheaf X d) i j
    _ = (moduleAnalytificationUnitIso X d).inv ≫
        (moduleAnalytification X d).map
          (if j = i then 𝟙 (SheafOfModules.unit X.left.ringCatSheaf) else 0) ≫
            (moduleAnalytificationUnitIso X d).hom := by
      by_cases hji : j = i <;> simp [hji]
    _ = (moduleAnalytificationUnitIso X d).inv ≫
        (moduleAnalytification X d).map
          (SheafOfModules.ιFree (R := X.left.ringCatSheaf) j ≫
            SheafOfModules.πFree (R := X.left.ringCatSheaf) i) ≫
              (moduleAnalytificationUnitIso X d).hom := by
      rw [SheafOfModules.ιFree_πFree]
    _ = (moduleAnalytificationUnitIso X d).inv ≫
        ((moduleAnalytification X d).map
          (SheafOfModules.ιFree (R := X.left.ringCatSheaf) j) ≫
            (moduleAnalytification X d).map
              (SheafOfModules.πFree (R := X.left.ringCatSheaf) i)) ≫
                (moduleAnalytificationUnitIso X d).hom := by
      rw [(moduleAnalytification X d).map_comp]
    _ = ((moduleAnalytificationUnitIso X d).inv ≫
          (moduleAnalytification X d).map
            (SheafOfModules.ιFree (R := X.left.ringCatSheaf) j)) ≫
        (moduleAnalytification X d).map
          (SheafOfModules.πFree (R := X.left.ringCatSheaf) i) ≫
            (moduleAnalytificationUnitIso X d).hom := by simp only [Category.assoc]
    _ = (SheafOfModules.ιFree (R := holomorphicRingSheaf X d) j ≫
          (unitFreeAnalytificationIso X d I).inv) ≫
        (moduleAnalytification X d).map
          (SheafOfModules.πFree (R := X.left.ringCatSheaf) i) ≫
            (moduleAnalytificationUnitIso X d).hom := by
      rw [unitFreeAnalytificationIso_inv_ιFree]
    _ = _ := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Taking a matrix entry commutes with the finite-free analytification comparison. -/
lemma unitFreeAnalytification_entry (I K : Type) [Finite I] [Finite K]
    [DecidableEq I] [DecidableEq K]
    (f : SheafOfModules.free (R := X.left.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.left.ringCatSheaf) K) (i : I) (k : K) :
    SheafOfModules.ιFree (R := holomorphicRingSheaf X d) i ≫
        ((unitFreeAnalytificationIso X d I).inv ≫
          ((moduleAnalytification X d).map f ≫
            (unitFreeAnalytificationIso X d K).hom)) ≫
              SheafOfModules.πFree (R := holomorphicRingSheaf X d) k =
      (moduleAnalytificationUnitIso X d).inv ≫
        (moduleAnalytification X d).map
          (SheafOfModules.ιFree (R := X.left.ringCatSheaf) i ≫ f ≫
            SheafOfModules.πFree (R := X.left.ringCatSheaf) k) ≫
              (moduleAnalytificationUnitIso X d).hom := by
  calc
    _ = (SheafOfModules.ιFree (R := holomorphicRingSheaf X d) i ≫
          (unitFreeAnalytificationIso X d I).inv) ≫
        (moduleAnalytification X d).map f ≫
          ((unitFreeAnalytificationIso X d K).hom ≫
            SheafOfModules.πFree (R := holomorphicRingSheaf X d) k) := by
      simp only [Category.assoc]
    _ = ((moduleAnalytificationUnitIso X d).inv ≫
          (moduleAnalytification X d).map
            (SheafOfModules.ιFree (R := X.left.ringCatSheaf) i)) ≫
        (moduleAnalytification X d).map f ≫
          ((moduleAnalytification X d).map
            (SheafOfModules.πFree (R := X.left.ringCatSheaf) k) ≫
              (moduleAnalytificationUnitIso X d).hom) := by
      rw [unitFreeAnalytificationIso_inv_ιFree,
        unitFreeAnalytificationIso_hom_πFree]
    _ = (moduleAnalytificationUnitIso X d).inv ≫
        ((moduleAnalytification X d).map
            (SheafOfModules.ιFree (R := X.left.ringCatSheaf) i) ≫
          (moduleAnalytification X d).map f ≫
            (moduleAnalytification X d).map
              (SheafOfModules.πFree (R := X.left.ringCatSheaf) k)) ≫
                (moduleAnalytificationUnitIso X d).hom := by
      simp only [Category.assoc]
    _ = _ := by
      rw [← (moduleAnalytification X d).map_comp,
        ← (moduleAnalytification X d).map_comp]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- On a preconnected projective analytification, analytification is full on morphisms between
finite free module sheaves. Equivalently, every finite holomorphic matrix has algebraic entries. -/
theorem finiteFreeHom_analytification_surjective [IsProjective X.hom]
    [PreconnectedSpace (ComplexPoint X)] (I K : Type) [Finite I] [Finite K] :
    Function.Surjective
      (fun f : SheafOfModules.free (R := X.left.ringCatSheaf) I ⟶
          SheafOfModules.free (R := X.left.ringCatSheaf) K ↦
        (unitFreeAnalytificationIso X d I).inv ≫
          (moduleAnalytification X d).map f ≫
            (unitFreeAnalytificationIso X d K).hom) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype K := Fintype.ofFinite K
  intro h
  have hs : ∀ i k, ∃ a : SheafOfModules.unit X.left.ringCatSheaf ⟶
      SheafOfModules.unit X.left.ringCatSheaf,
      (moduleAnalytificationUnitIso X d).inv ≫
          (moduleAnalytification X d).map a ≫
            (moduleAnalytificationUnitIso X d).hom =
        SheafOfModules.ιFree (R := holomorphicRingSheaf X d) i ≫ h ≫
          SheafOfModules.πFree (R := holomorphicRingSheaf X d) k :=
    fun i k ↦ unitEndomorphism_analytification_surjective X d _
  choose a ha using hs
  refine ⟨SheafOfModules.matrix (R := X.left.ringCatSheaf) a, ?_⟩
  apply SheafOfModules.hom_ext_matrixEntries (R := holomorphicRingSheaf X d)
  intro i k
  rw [unitFreeAnalytification_entry, SheafOfModules.ιFree_matrix_πFree, ha]

end AlgebraicGeometry.ComplexPoint
