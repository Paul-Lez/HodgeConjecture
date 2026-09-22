/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.RationalOpenCoverOrderedCechBicomplex

/-!
# The geometric part of the universal-member Čech contraction

If one member of an open cover is the whole space, prepending that member to an ordered
Čech tuple does not change the underlying intersection.  This file records the resulting
chain map on the concrete rational intersection-chain model.  The alternating homotopy
identities are intentionally kept separate: they require the signed face calculation and
the totalization bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial
open AlgebraicTopology AlgebraicTopology.OrderedCechTuple

namespace AlgebraicTopology.Singular

variable {ι : Type} [LinearOrder ι]

/-- The support of a tuple after prepending `i₀` is the insertion of `i₀` into its old support. -/
public lemma tupleSupport_cons_finite (i₀ : ι) {n : ℕ} (a : Fin (n + 1) → ι) :
    (tupleSupport (Fin.cons i₀ a)).1 = insert i₀ (tupleSupport a).1 := by
  ext x
  simp only [tupleSupport, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨j, hj⟩
    induction j using Fin.cases with
    | zero => exact Or.inl hj.symm
    | succ k => exact Or.inr ⟨k, hj⟩
  · intro hx
    rcases hx with rfl | ⟨k, hk⟩
    · exact ⟨0, rfl⟩
    · exact ⟨Fin.succ k, hk⟩

/-- The intersection-space isomorphism induced by a universal cover member. -/
public noncomputable def universalMemberIntersectionIso
    (X : TopCat) (U : ι → Set X) (i₀ : ι) {n : ℕ} (a : Fin (n + 1) → ι)
    (hU : U i₀ = Set.univ) :
    TopCat.of (openCoverIntersection X U (tupleSupport a).1) ≅
      TopCat.of (openCoverIntersection X U (tupleSupport (Fin.cons i₀ a)).1) := by
  let hsub : (tupleSupport a).1 ⊆ (tupleSupport (Fin.cons i₀ a)).1 := by
    rw [tupleSupport_cons_finite]
    exact Finset.subset_insert _ _
  let f : TopCat.of (openCoverIntersection X U (tupleSupport a).1) ⟶
      TopCat.of (openCoverIntersection X U (tupleSupport (Fin.cons i₀ a)).1) :=
    TopCat.ofHom
      { toFun := fun z ↦ ⟨z.1, by
          rw [mem_openCoverIntersection_iff]
          intro i hi
          rcases Finset.mem_insert.mp (by
            rw [← tupleSupport_cons_finite i₀ a]
            exact hi) with rfl | hi
          · rw [hU]
            exact Set.mem_univ _
          · exact (mem_openCoverIntersection_iff X U (tupleSupport a).1 z.1).mp z.2 i hi⟩
        continuous_toFun := by fun_prop }
  let g := openCoverIntersectionInclusion X U hsub
  refine { hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    rfl
  · apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    rfl

/-- The induced map on rational singular chain complexes. -/
public noncomputable def universalMemberIntersectionChainMap
    (X : TopCat) (U : ι → Set X) (i₀ : ι) {n : ℕ} (a : Fin (n + 1) → ι)
    (hU : U i₀ = Set.univ) :
    (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport a) ⟶
      (rationalOpenCoverIntersectionChainModels X U).model
        (tupleSupport (Fin.cons i₀ a)) :=
  SSet.chainComplexMap
    (TopCat.toSSet.map (universalMemberIntersectionIso X U i₀ a hU).hom)
    (ModuleCat.of ℚ ℚ)

/-- Prepending the universal member on every ordered Čech summand. -/
public noncomputable def universalMemberPrependMap
    (X : TopCat) (U : ι → Set X) (i₀ : ι) (n : ℕ)
    (hU : U i₀ = Set.univ) :
    (rationalOpenCoverIntersectionChainModels X U).cechObject TupleClass.all n ⟶
      (rationalOpenCoverIntersectionChainModels X U).cechObject TupleClass.all (n + 1) :=
  Sigma.desc (fun a ↦
    universalMemberIntersectionChainMap X U i₀ a.1 hU ≫
      Sigma.ι (fun b : {b : Fin (n + 2) → ι // TupleClass.all.mem (n + 1) b} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1))
        ⟨Fin.cons i₀ a.1, trivial⟩)

@[reassoc]
public lemma universalMemberPrependMap_ι
    (X : TopCat) (U : ι → Set X) (i₀ : ι) (n : ℕ)
    (hU : U i₀ = Set.univ)
    (a : {a : Fin (n + 1) → ι // TupleClass.all.mem n a}) :
    Sigma.ι (fun a : {a : Fin (n + 1) → ι // TupleClass.all.mem n a} ↦
        (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport a.1)) a ≫
      universalMemberPrependMap X U i₀ n hU =
      universalMemberIntersectionChainMap X U i₀ a.1 hU ≫
        Sigma.ι (fun b : {b : Fin (n + 2) → ι // TupleClass.all.mem (n + 1) b} ↦
          (rationalOpenCoverIntersectionChainModels X U).model (tupleSupport b.1))
          ⟨Fin.cons i₀ a.1, trivial⟩ := by
  rw [universalMemberPrependMap, Sigma.ι_desc]

/-- Removing the newly prepended universal member gives back the original chain map. -/
public lemma universalMemberIntersectionChainMap_face_zero
    (X : TopCat) (U : ι → Set X) (i₀ : ι) {n : ℕ}
    (a : Fin (n + 1) → ι) (hU : U i₀ = Set.univ) :
    universalMemberIntersectionChainMap X U i₀ a hU ≫
        (rationalOpenCoverIntersectionChainModels X U).face
          (show (tupleSupport a).1 ⊆ (tupleSupport (Fin.cons i₀ a)).1 by
            rw [tupleSupport_cons_finite]
            exact Finset.subset_insert _ _) = 𝟙 _ := by
  unfold universalMemberIntersectionChainMap
    SupportChainModels.face rationalOpenCoverIntersectionChainModels
  rw [← Functor.map_comp]
  have htopTop :
      (universalMemberIntersectionIso X U i₀ a hU).hom ≫
          openCoverIntersectionInclusion X U
            (show (tupleSupport a).1 ⊆ (tupleSupport (Fin.cons i₀ a)).1 by
              rw [tupleSupport_cons_finite]
              exact Finset.subset_insert _ _) =
        𝟙 _ := by
    apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    rfl
  have htop :
      TopCat.toSSet.map (universalMemberIntersectionIso X U i₀ a hU).hom ≫
          TopCat.toSSet.map (openCoverIntersectionInclusion X U
            (show (tupleSupport a).1 ⊆ (tupleSupport (Fin.cons i₀ a)).1 by
              rw [tupleSupport_cons_finite]
              exact Finset.subset_insert _ _)) =
        𝟙 _ := by
    rw [← TopCat.toSSet.map_comp, htopTop, TopCat.toSSet.map_id]
  rw [htop]
  simp

/-- Prepending commutes with restriction to a face.  This is the local naturality identity
needed to transport the signed Čech boundary through the universal-member map. -/
public lemma universalMemberIntersectionChainMap_comp_face
    (X : TopCat) (U : ι → Set X) (i₀ : ι) {n m : ℕ}
    (a : Fin (n + 1) → ι) (b : Fin (m + 1) → ι)
    (hba : Set.range b ⊆ Set.range a) (hU : U i₀ = Set.univ) :
    universalMemberIntersectionChainMap X U i₀ a hU ≫
        (rationalOpenCoverIntersectionChainModels X U).faceOrZero
          (Fin.cons i₀ a) (Fin.cons i₀ b) =
      (rationalOpenCoverIntersectionChainModels X U).faceOrZero a b ≫
        universalMemberIntersectionChainMap X U i₀ b hU := by
  unfold universalMemberIntersectionChainMap
    SupportChainModels.faceOrZero
    SupportChainModels.face rationalOpenCoverIntersectionChainModels
  have hcons : Set.range (Fin.cons i₀ b) ⊆ Set.range (Fin.cons i₀ a) := by
    rintro x ⟨j, rfl⟩
    induction j using Fin.cases with
    | zero => exact ⟨0, rfl⟩
    | succ j =>
      obtain ⟨k, hk⟩ := hba ⟨j, rfl⟩
      exact ⟨Fin.succ k, hk⟩
  rw [dif_pos ((tupleSupport_subset_iff (Fin.cons i₀ a) (Fin.cons i₀ b)).2
      hcons),
    dif_pos ((tupleSupport_subset_iff a b).2 hba),
    ← Functor.map_comp, ← Functor.map_comp]
  dsimp [rationalOpenCoverIntersectionChainModels]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp]
  rw [← TopCat.toSSet.map_comp]
  congr 1

/- The prepend map can be moved through a realized Čech combination supported in a fixed
tuple.  This is the chain-level form of the face naturality needed for the cone identity. -/
public lemma universalMemberIntersectionChainMap_comp_realizeAux_cons
    (X : TopCat) (U : ι → Set X) (i₀ : ι) {n m : ℕ}
    (a : Fin (n + 1) → ι) (v : Formal ι (m + 1))
    (hv : ∀ b ∈ v.support, Set.range b ⊆ Set.range a)
    (hU : U i₀ = Set.univ) :
    universalMemberIntersectionChainMap X U i₀ a hU ≫
        (rationalOpenCoverIntersectionChainModels X U).realizeAux
          (Fin.cons i₀ a) TupleClass.all (consMap i₀ v) =
      (rationalOpenCoverIntersectionChainModels X U).realizeAux
          a TupleClass.all v ≫ universalMemberPrependMap X U i₀ m hU := by
  apply linearMap_apply_eq_of_forall_mem_support
    (L := (Preadditive.leftComp _
      (universalMemberIntersectionChainMap X U i₀ a hU)).toIntLinearMap ∘ₗ
        (rationalOpenCoverIntersectionChainModels X U).realizeAux
          (Fin.cons i₀ a) TupleClass.all ∘ₗ consMap i₀)
    (R := (Preadditive.rightComp _
      (universalMemberPrependMap X U i₀ m hU)).toIntLinearMap ∘ₗ
        (rationalOpenCoverIntersectionChainModels X U).realizeAux
          a TupleClass.all)
    (w := v)
  intro b hb
  change universalMemberIntersectionChainMap X U i₀ a hU ≫
      (rationalOpenCoverIntersectionChainModels X U).realizeAux
        (Fin.cons i₀ a) TupleClass.all (consMap i₀ (Finsupp.single b 1)) =
    (rationalOpenCoverIntersectionChainModels X U).realizeAux
        a TupleClass.all (Finsupp.single b 1) ≫ universalMemberPrependMap X U i₀ m hU
  rw [consMap_single,
    (rationalOpenCoverIntersectionChainModels X U).realizeAux_single,
    (rationalOpenCoverIntersectionChainModels X U).realizeAux_single,
    ← Category.assoc,
    universalMemberIntersectionChainMap_comp_face X U i₀ a b (hv b hb) hU]
  simp only [Category.assoc]
  rw [(rationalOpenCoverIntersectionChainModels X U).ιOrZero_of_mem
      TupleClass.all (by trivial),
    (rationalOpenCoverIntersectionChainModels X U).ιOrZero_of_mem
      TupleClass.all (by trivial)]
  simp only [Category.assoc]
  rw [universalMemberPrependMap_ι X U i₀ m hU ⟨b, trivial⟩]

end AlgebraicTopology.Singular
