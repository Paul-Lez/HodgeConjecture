/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.ClosedEmbeddingSheafExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# The actual derived pushforward of a closed embedding

Closed-embedding sheaf pushforward is exact by the proved stalk calculation. It therefore
induces a functor on the unbounded derived category directly by localization of its
termwise action. That functor preserves lower cohomological bounds and hence restricts to
`D⁺`. The displayed comparisons fix its normalization on coefficient complexes.

No boundedness of an arbitrary singular chain model is assumed. A source object must
actually belong to `D⁺` to use the bounded-below restriction. No claim that an intrinsic
chain model is quasi-isomorphic to the ambient supported model is needed here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe u

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Z X : TopCat.{u}} (i : Z ⟶ X) (hi : IsClosedEmbedding i)

local instance closedPushforwardSourceHasDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} Z) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} Z)

local instance closedPushforwardTargetHasDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

/-- The functor on the actual derived categories induced by exact closed-embedding
pushforward, not an independently supplied derived functor. -/
def closedEmbeddingDerivedPushforward :
    DerivedCategory (Sheaf AddCommGrpCat.{u} Z) ⥤
      DerivedCategory (Sheaf AddCommGrpCat.{u} X) := by
  have h := closedEmbeddingPushforward_preservesFiniteColimits i hi
  exact (pushforward AddCommGrpCat.{u} i).mapDerivedCategory

instance closedEmbeddingDerivedPushforward_commShift :
    (closedEmbeddingDerivedPushforward i hi).CommShift ℤ := by
  have h := closedEmbeddingPushforward_preservesFiniteColimits i hi
  exact inferInstanceAs ((pushforward AddCommGrpCat.{u} i).mapDerivedCategory.CommShift ℤ)

instance closedEmbeddingDerivedPushforward_isTriangulated :
    (closedEmbeddingDerivedPushforward i hi).IsTriangulated := by
  have h := closedEmbeddingPushforward_preservesFiniteColimits i hi
  exact inferInstanceAs ((pushforward AddCommGrpCat.{u} i).mapDerivedCategory.IsTriangulated)

/-- The induced derived functor agrees with actual termwise pushforward on complexes. -/
def closedEmbeddingDerivedPushforwardFactors :
    DerivedCategory.Q ⋙ closedEmbeddingDerivedPushforward i hi ≅
      (pushforward AddCommGrpCat.{u} i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q := by
  have h := closedEmbeddingPushforward_preservesFiniteColimits i hi
  exact (pushforward AddCommGrpCat.{u} i).mapDerivedCategoryFactors

/-- In particular, the comparison preserves every actual coefficient-complex morphism. -/
@[reassoc]
lemma closedEmbeddingDerivedPushforwardFactors_naturality
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} Z) ℤ} (f : K ⟶ L) :
    (closedEmbeddingDerivedPushforward i hi).map (DerivedCategory.Q.map f) ≫
      (closedEmbeddingDerivedPushforwardFactors i hi).hom.app L =
      (closedEmbeddingDerivedPushforwardFactors i hi).hom.app K ≫
        DerivedCategory.Q.map
          (((pushforward AddCommGrpCat.{u} i).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  (closedEmbeddingDerivedPushforwardFactors i hi).hom.naturality f

/-- The same normalization on the actual homotopy categories. -/
def closedEmbeddingDerivedPushforwardFactorsh :
    DerivedCategory.Qh ⋙ closedEmbeddingDerivedPushforward i hi ≅
      (pushforward AddCommGrpCat.{u} i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh := by
  have h := closedEmbeddingPushforward_preservesFiniteColimits i hi
  exact (pushforward AddCommGrpCat.{u} i).mapDerivedCategoryFactorsh

/-- Exact direct image preserves every lower cohomological bound. -/
theorem closedEmbeddingDerivedPushforward_isGE
    (A : DerivedCategory (Sheaf AddCommGrpCat.{u} Z)) (n : ℤ) [A.IsGE n] :
    ((closedEmbeddingDerivedPushforward i hi).obj A).IsGE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE A n
  have hmap : CochainComplex.IsStrictlyGE
      (((pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) n := inferInstance
  have hQ : (DerivedCategory.Q.obj
      (((pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)).IsGE n := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  let e' : (closedEmbeddingDerivedPushforward i hi).obj A ≅
      DerivedCategory.Q.obj
        (((pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
    (closedEmbeddingDerivedPushforward i hi).mapIso e ≪≫
      (closedEmbeddingDerivedPushforwardFactors i hi).app K
  exact DerivedCategory.TStructure.t.isGE_of_iso e'.symm n

/-- The bounded-below restriction of the constructed exact derived pushforward. -/
def closedEmbeddingDerivedPushforwardPlus :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} Z) ⥤
      DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) :=
  DerivedCategory.TStructure.t.plus.lift
    (DerivedCategory.Plus.ι ⋙ closedEmbeddingDerivedPushforward i hi) (by
      intro A
      obtain ⟨n, hn⟩ := A.property
      exact ⟨n, closedEmbeddingDerivedPushforward_isGE i hi A.obj n⟩)

/-- Forgetting the lower-bound certificate gives exactly the constructed unbounded
derived pushforward. -/
def closedEmbeddingDerivedPushforwardPlusForgetIso :
    closedEmbeddingDerivedPushforwardPlus i hi ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ closedEmbeddingDerivedPushforward i hi := Iso.refl _

instance closedEmbeddingDerivedPushforwardPlus_commShift :
    (closedEmbeddingDerivedPushforwardPlus i hi).CommShift ℤ := by
  dsimp only [closedEmbeddingDerivedPushforwardPlus]
  infer_instance

instance closedEmbeddingDerivedPushforwardPlus_isTriangulated :
    (closedEmbeddingDerivedPushforwardPlus i hi).IsTriangulated := by
  dsimp only [closedEmbeddingDerivedPushforwardPlus]
  infer_instance

/-- On bounded-below homotopy models the `D⁺` functor is the actual termwise direct image. -/
def closedEmbeddingDerivedPushforwardPlusFactors :
    DerivedCategory.Plus.Qh ⋙ closedEmbeddingDerivedPushforwardPlus i hi ≅
      (pushforward AddCommGrpCat.{u} i).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh :=
  NatIso.ofComponents
    (fun K => DerivedCategory.Plus.ι.preimageIso
      ((closedEmbeddingDerivedPushforwardFactorsh i hi).app K.obj)) (by
        intro K L f
        apply DerivedCategory.Plus.ι.map_injective
        simp only [Functor.map_comp, Functor.preimageIso, Functor.map_preimage]
        exact (closedEmbeddingDerivedPushforwardFactorsh i hi).hom.naturality f.hom)

/-- The `D⁺` comparison has precisely the unbounded localization comparison as its
underlying map; it introduces no new choice of normalization. -/
@[simp]
lemma closedEmbeddingDerivedPushforwardPlusFactors_hom
    (K : HomotopyCategory.Plus (Sheaf AddCommGrpCat.{u} Z)) :
    DerivedCategory.Plus.ι.map
        ((closedEmbeddingDerivedPushforwardPlusFactors i hi).hom.app K) =
      (closedEmbeddingDerivedPushforwardFactorsh i hi).hom.app K.obj := by
  change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = _
  exact Functor.map_preimage _ _

end TopCat.Sheaf
