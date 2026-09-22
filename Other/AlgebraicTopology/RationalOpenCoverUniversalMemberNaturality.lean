/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.RationalOpenCoverUniversalMember
public import Other.AlgebraicTopology.RelativeCechConeComparison

/-!
# Naturality of the universal-member Čech section

The singleton section associated to a universal cover member commutes strictly with pullback-cover
maps.  This supplies the chain square needed to use singleton evaluation on relative Čech cones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial
open AlgebraicTopology.OrderedCechTuple

namespace AlgebraicTopology.Singular

variable {ι : Type} (X Y : TopCat) (f : Y ⟶ X)
  (U : ι → Set X) (j : ι)

/-- A universal cover member remains universal after pulling the cover back. -/
public lemma pullbackCover_member_eq_univ (hj : U j = Set.univ) :
    pullbackCover f U j = Set.univ := by
  ext y
  simp [pullbackCover, hj]

variable [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of the chain map into the intersection belonging to the universal singleton. -/
public lemma rationalOpenCoverUniversalMemberChainMap_naturality
    (hj : U j = Set.univ) :
    SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
      rationalOpenCoverUniversalMemberChainMap X U j hj =
    rationalOpenCoverUniversalMemberChainMap Y (pullbackCover f U) j
        (pullbackCover_member_eq_univ X Y f U j hj) ≫
      (rationalPullbackCoverLocalMap f U).app
        (Opposite.op (tupleSupport (singletonStrictCechTuple j).1)) := by
  have hx : rationalOpenCoverUniversalMemberChainMap X U j hj =
      SSet.chainComplexMap
        (TopCat.toSSet.map (openCoverUniversalMemberIso X U j hj).inv)
        (ModuleCat.of ℚ ℚ) := by rfl
  have hy : rationalOpenCoverUniversalMemberChainMap Y (pullbackCover f U) j
      (pullbackCover_member_eq_univ X Y f U j hj) =
      SSet.chainComplexMap
        (TopCat.toSSet.map (openCoverUniversalMemberIso Y (pullbackCover f U) j
          (pullbackCover_member_eq_univ X Y f U j hj)).inv)
        (ModuleCat.of ℚ ℚ) := by rfl
  rw [hx, hy, rationalPullbackCoverLocalMap_app]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of the universal-singleton inclusion into outer Čech degree zero. -/
public lemma rationalOpenCoverUniversalMemberColumnMap_naturality
    (hj : U j = Set.univ) :
    SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
      rationalOpenCoverUniversalMemberColumnMap X U j hj =
    rationalOpenCoverUniversalMemberColumnMap Y (pullbackCover f U) j
        (pullbackCover_member_eq_univ X Y f U j hj) ≫
      (rationalPullbackCoverLocalMap f U).cechObjectMap TupleClass.strictMono 0 := by
  unfold rationalOpenCoverUniversalMemberColumnMap
  rw [← Category.assoc,
    rationalOpenCoverUniversalMemberChainMap_naturality X Y f U j hj]
  simp only [Category.assoc]
  dsimp only [SupportChainModels.Hom.cechObjectMap]
  rw [Limits.Sigma.ι_map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The literal universal-member section commutes with the normalized pullback-cover total map. -/
@[reassoc]
public lemma rationalOpenCoverUniversalMemberSection_naturality
    (hj : U j = Set.univ) :
    SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
      rationalOpenCoverUniversalMemberSection X U j hj =
    rationalOpenCoverUniversalMemberSection Y (pullbackCover f U) j
        (pullbackCover_member_eq_univ X Y f U j hj) ≫
      rationalPullbackCoverNormalizedTotalMap f U := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f]
  dsimp only [rationalOpenCoverUniversalMemberSection]
  have hcol := congrArg (fun k ↦ k.f n)
    (rationalOpenCoverUniversalMemberColumnMap_naturality X Y f U j hj)
  simp only [HomologicalComplex.comp_f] at hcol
  rw [← Category.assoc, hcol]
  simp only [Category.assoc]
  unfold rationalPullbackCoverNormalizedTotalMap
  rw [HomologicalComplex₂.ιTotal_map]
  rfl

end AlgebraicTopology.Singular
