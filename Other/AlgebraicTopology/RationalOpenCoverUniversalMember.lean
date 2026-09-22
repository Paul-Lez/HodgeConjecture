/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.RationalOpenCoverOrderedCechBicomplex

/-!
# The singleton section for a rational Čech cover with a universal member

If one cover member is the whole ambient space, ordinary singular chains embed in outer Čech
degree zero through that member.  This file constructs the literal chain map into the normalized
ordered Čech total.  The complementary prepend-extra-degeneracy homotopy is a separate result.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial
open AlgebraicTopology.OrderedCechTuple

namespace AlgebraicTopology.Singular

variable {ι : Type} [LinearOrder ι] (X : TopCat) (U : ι → Set X)

/-- A one-entry tuple is strictly increasing. -/
lemma strictMono_singletonTuple (j : ι) : StrictMono (![j] : Fin 1 → ι) := by
  intro a b hab
  omega

/-- The singleton tuple, packaged as a normalized Čech index in outer degree zero. -/
def singletonStrictCechTuple (j : ι) :
    {a : Fin 1 → ι // TupleClass.strictMono.mem 0 a} :=
  ⟨![j], strictMono_singletonTuple j⟩

/-- The same singleton, viewed as an unrestricted ordered Čech tuple in outer degree zero. -/
abbrev singletonAllCechTuple (j : ι) :
    OpenCoverCechTuple (ι := ι) (Opposite.op (SimplexCategory.mk 0)) :=
  ⟨(singletonStrictCechTuple j).1, trivial⟩

/-- The singleton intersection at a universal member is canonically homeomorphic to the
ambient space. -/
noncomputable def openCoverUniversalMemberIso (j : ι) (hj : U j = Set.univ) :
    TopCat.of (openCoverIntersection X U (tupleSupport (singletonStrictCechTuple j).1).1) ≅ X := by
  have hI : openCoverIntersection X U
      (tupleSupport (singletonStrictCechTuple j).1).1 = Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      rw [mem_openCoverIntersection_iff]
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨k, _, rfl⟩
      rw [show (singletonStrictCechTuple j).1 k = j by fin_cases k; rfl, hj]
      exact Set.mem_univ x
  exact TopCat.isoOfHomeo (topologicalSubsetHomeomorphOfEqUniv X _ hI)

/-- The forward map of the universal-singleton isomorphism is the underlying subset
inclusion. -/
@[simp]
theorem openCoverUniversalMemberIso_hom (j : ι) (hj : U j = Set.univ) :
    (openCoverUniversalMemberIso X U j hj).hom =
      topologicalSubsetInclusion X
        (openCoverIntersection X U
          (tupleSupport (singletonStrictCechTuple j).1).1) := by
  ext x
  rfl

/-- The universal singleton enters the cover-small singular simplicial set and then the
ambient singular simplicial set by the identity. -/
@[reassoc]
theorem openCoverUniversalMemberToSmall_comp_inclusion
    (j : ι) (hj : U j = Set.univ) :
    TopCat.toSSet.map (openCoverUniversalMemberIso X U j hj).inv ≫
        openCoverTupleIntersectionToSmall X U (singletonAllCechTuple j) ≫
        (coverSmallSingularSubcomplex X U).ι =
      𝟙 (TopCat.toSSet.obj X) := by
  dsimp [openCoverTupleIntersectionToSmall, singletonAllCechTuple]
  rw [Category.assoc, coverMemberToSmallSingularSet_comp_inclusion]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Ordinary rational chains mapped into the local chain model belonging to the universal
singleton. -/
noncomputable def rationalOpenCoverUniversalMemberChainMap
    (j : ι) (hj : U j = Set.univ) :
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (rationalOpenCoverIntersectionChainModels X U).model
        (tupleSupport (singletonStrictCechTuple j).1) := by
  change (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) ⟶
    (TopCat.toSSet.obj (TopCat.of (openCoverIntersection X U
      (tupleSupport (singletonStrictCechTuple j).1).1))).chainComplex (ModuleCat.of ℚ ℚ)
  exact SSet.chainComplexMap
    (TopCat.toSSet.map (openCoverUniversalMemberIso X U j hj).inv)
    (ModuleCat.of ℚ ℚ)

/-- At chain level, the universal singleton followed by the cover-small inclusion is the
identity on ordinary rational singular chains. -/
@[reassoc]
theorem rationalOpenCoverUniversalMemberChainMap_comp_small_inclusion
    (j : ι) (hj : U j = Set.univ) :
    rationalOpenCoverUniversalMemberChainMap X U j hj ≫
        SSet.chainComplexMap
          (openCoverTupleIntersectionToSmall X U (singletonAllCechTuple j))
          (ModuleCat.of ℚ ℚ) ≫
        coverSmallRationalSingularChainInclusion X U = 𝟙 _ := by
  dsimp [singletonAllCechTuple]
  change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map
        (TopCat.toSSet.map (openCoverUniversalMemberIso X U j hj).inv) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map
        (openCoverTupleIntersectionToSmall X U (singletonAllCechTuple j)) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map
          (coverSmallSingularSubcomplex X U).ι = 𝟙 _
  rw [← Functor.map_comp, ← Functor.map_comp,
    openCoverUniversalMemberToSmall_comp_inclusion]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The universal-member chains included in the normalized outer-degree-zero Čech column. -/
noncomputable def rationalOpenCoverUniversalMemberColumnMap
    (j : ι) (hj : U j = Set.univ) :
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      ((rationalOpenCoverIntersectionChainModels X U).cechComplex
        TupleClass.strictMono).X 0 :=
  rationalOpenCoverUniversalMemberChainMap X U j hj ≫
    Sigma.ι (fun a : {a : Fin 1 → ι // TupleClass.strictMono.mem 0 a} ↦
      (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport a.1))
      (singletonStrictCechTuple j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The literal singleton section from ordinary rational singular chains to the normalized
ordered Čech total.  It lands entirely in outer degree zero. -/
noncomputable def rationalOpenCoverUniversalMemberSection
    (j : ι) (hj : U j = Set.univ) :
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (rationalOpenCoverIntersectionChainModels X U).cechTotal TupleClass.strictMono where
  f n :=
    (rationalOpenCoverUniversalMemberColumnMap X U j hj).f n ≫
    ((rationalOpenCoverIntersectionChainModels X U).cechComplex
      TupleClass.strictMono).ιTotal (ComplexShape.down ℕ) 0 n n (by simp)
  comm' := by
    intro n m hnm
    rw [Category.assoc, AlgebraicTopology.ιTotal_total_d]
    rw [AlgebraicTopology.d₁_zero, zero_add]
    rw [((rationalOpenCoverIntersectionChainModels X U).cechComplex
      TupleClass.strictMono).d₂_eq
      (ComplexShape.down ℕ) 0 hnm m (by simp)]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The singleton section at a universal cover member is a strict section of the normalized
Čech-to-singular comparison. -/
@[reassoc]
theorem rationalOpenCoverUniversalMemberSection_comp_toSingular
    (j : ι) (hj : U j = Set.univ) :
    rationalOpenCoverUniversalMemberSection X U j hj ≫
      rationalOpenCoverNormalizedCechTotalToSingular X U = 𝟙 _ := by
  have hnorm :
      Sigma.ι (fun a : {a : Fin 1 → ι // TupleClass.strictMono.mem 0 a} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport a.1))
        (singletonStrictCechTuple j) ≫
        (rationalOpenCoverIntersectionChainModels X U).normalizedInclusion.f 0 =
      (rationalOpenCoverIntersectionChainModels X U).ιOrZero TupleClass.all
        (singletonStrictCechTuple j).1 := by
    unfold SupportChainModels.normalizedInclusion
      SupportChainModels.strictInclusion SupportChainModels.monotoneInclusion
    simp only [HomologicalComplex.comp_f]
    change Sigma.ι (fun a : {a : Fin 1 → ι // TupleClass.strictMono.mem 0 a} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport a.1))
        (singletonStrictCechTuple j) ≫
        (rationalOpenCoverIntersectionChainModels X U).realize
          TupleClass.strictMono TupleClass.monotone LinearMap.id ≫
        (rationalOpenCoverIntersectionChainModels X U).realize
          TupleClass.monotone TupleClass.all LinearMap.id = _
    rw [SupportChainModels.ι_realize_assoc,
      LinearMap.id_apply,
      SupportChainModels.realizeAux_single,
      SupportChainModels.faceOrZero_self,
      SupportChainModels.ιOrZero_of_mem,
      Category.id_comp,
      SupportChainModels.ι_realize]
    rw [LinearMap.id_apply, SupportChainModels.realizeAux_single,
      SupportChainModels.faceOrZero_self, SupportChainModels.ιOrZero_of_mem]
    all_goals try trivial
    exact (strictMono_singletonTuple j).monotone
  have hcolumn :
      rationalOpenCoverUniversalMemberColumnMap X U j hj ≫
        (rationalOpenCoverIntersectionChainModels X U).normalizedInclusion.f 0 =
      rationalOpenCoverUniversalMemberChainMap X U j hj ≫
        (rationalOpenCoverIntersectionChainModels X U).ιOrZero TupleClass.all
          (singletonStrictCechTuple j).1 := by
    dsimp [rationalOpenCoverUniversalMemberColumnMap]
    rw [Category.assoc, hnorm]
  have hchain :
      (rationalOpenCoverIntersectionChainModels X U).ιOrZero TupleClass.all
          (singletonStrictCechTuple j).1 ≫
        (rationalOpenCoverOrderedCechBicomplexIso X U).hom.f 0 =
      rationalOpenCoverTupleCechSummandChainMap X U 0
        (singletonAllCechTuple j) := by
    rw [(rationalOpenCoverIntersectionChainModels X U).ιOrZero_of_mem
      TupleClass.all (by trivial)]
    change Sigma.ι (fun b : {_b : Fin 1 → ι // TupleClass.all.mem 0 _b} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1))
          (singletonAllCechTuple j) ≫
        (rationalOpenCoverOrderedCechColumnIso X U 0).hom = _
    exact rationalOpenCoverOrderedCechColumnIso_hom_ι_chainMap X U 0
      (singletonAllCechTuple j)
  have hdegreeZero :
      rationalOpenCoverUniversalMemberChainMap X U j hj ≫
        (rationalOpenCoverIntersectionChainModels X U).ιOrZero TupleClass.all
          (singletonStrictCechTuple j).1 ≫
        (rationalOpenCoverOrderedCechBicomplexIso X U).hom.f 0 ≫
        (rationalCechOuterAugmentation
          (Arrow.mk (coverSmallPresentation X U))).f 0 ≫
        coverSmallRationalSingularChainInclusion X U = 𝟙 _ := by
    calc
      _ = rationalOpenCoverUniversalMemberChainMap X U j hj ≫
          rationalOpenCoverTupleCechSummandChainMap X U 0
            (singletonAllCechTuple j) ≫
          (rationalCechOuterAugmentation
            (Arrow.mk (coverSmallPresentation X U))).f 0 ≫
          coverSmallRationalSingularChainInclusion X U := by
            simpa only [Category.assoc] using congrArg
              (fun k ↦ rationalOpenCoverUniversalMemberChainMap X U j hj ≫
                k ≫ (rationalCechOuterAugmentation
                  (Arrow.mk (coverSmallPresentation X U))).f 0 ≫
                coverSmallRationalSingularChainInclusion X U) hchain
      _ = rationalOpenCoverUniversalMemberChainMap X U j hj ≫
          SSet.chainComplexMap
            (openCoverTupleIntersectionToSmall X U (singletonAllCechTuple j))
            (ModuleCat.of ℚ ℚ) ≫
          coverSmallRationalSingularChainInclusion X U := by
            simpa only [Category.assoc] using congrArg
              (fun k ↦ rationalOpenCoverUniversalMemberChainMap X U j hj ≫
                k ≫ coverSmallRationalSingularChainInclusion X U)
              (rationalOpenCoverTupleCechSummandChainMap_comp_outerAugmentation_zero
                X U (singletonAllCechTuple j))
      _ = 𝟙 _ := by
        exact rationalOpenCoverUniversalMemberChainMap_comp_small_inclusion X U j hj
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp [rationalOpenCoverUniversalMemberSection,
    rationalOpenCoverNormalizedCechTotalToSingular,
    rationalOpenCoverNormalizedCechTotalAugmentation]
  simp
  unfold SupportChainModels.totalNormalizedInclusion
  rw [HomologicalComplex₂.ιTotal_map_assoc
    ((rationalOpenCoverIntersectionChainModels X U).cechComplex TupleClass.strictMono)
    ((rationalOpenCoverIntersectionChainModels X U).cechComplex TupleClass.all)
    (rationalOpenCoverIntersectionChainModels X U).normalizedInclusion
    (ComplexShape.down ℕ) 0 n n (by simp)
    ((rationalOpenCoverOrderedCechTotalIso X U).hom.f n ≫
      (rationalCechTotalAugmentationToTarget
        (Arrow.mk (coverSmallPresentation X U))).f n ≫
      (coverSmallRationalSingularChainInclusion X U).f n)]
  dsimp [rationalOpenCoverOrderedCechTotalIso]
  dsimp [HomologicalComplex₂.total.mapIso]
  rw [HomologicalComplex₂.ιTotal_map_assoc
    ((rationalOpenCoverIntersectionChainModels X U).cechComplex TupleClass.all)
    (rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U)))
    (rationalOpenCoverOrderedCechBicomplexIso X U).hom
    (ComplexShape.down ℕ) 0 n n (by simp)
    ((rationalCechTotalAugmentationToTarget
      (Arrow.mk (coverSmallPresentation X U))).f n ≫
      (coverSmallRationalSingularChainInclusion X U).f n)]
  dsimp [rationalCechTotalAugmentationToTarget]
  unfold rationalCechTotalAugmentation
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map_assoc
    (rationalCechBicomplex (Arrow.mk (coverSmallPresentation X U)))
    (firstQuadrantSingleZeroBicomplexGeneric
      ((coverSmallSingularSubcomplex X U).toSSet.chainComplex
        (ModuleCat.of ℚ ℚ)))
    (rationalCechOuterAugmentation (Arrow.mk (coverSmallPresentation X U)))
    (ComplexShape.down ℕ) 0 n n (by simp)
    ((firstQuadrantTotalToSingleZeroGeneric
      ((coverSmallSingularSubcomplex X U).toSSet.chainComplex
        (ModuleCat.of ℚ ℚ))).f n ≫
      (coverSmallRationalSingularChainInclusion X U).f n)]
  dsimp only [firstQuadrantTotalToSingleZeroGeneric]
  rw [HomologicalComplex₂.ι_totalDesc_assoc]
  simp only [firstQuadrantSingleZeroTotalComponentGeneric_zero]
  rw [show firstQuadrantSingleZeroColumnIsoGeneric
      ((coverSmallSingularSubcomplex X U).toSSet.chainComplex
        (ModuleCat.of ℚ ℚ)) = Iso.refl _ from
    ChainComplex.single₀ObjXSelf _]
  have hcolumn_n := congrArg (fun f => f.f n) hcolumn
  simp only [HomologicalComplex.comp_f] at hcolumn_n
  rw [← Category.assoc, hcolumn_n]
  have hdegreeZero_n := congrArg (fun f => f.f n) hdegreeZero
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    Iso.refl_hom, Category.id_comp, Category.assoc] using hdegreeZero_n

end AlgebraicTopology.Singular
