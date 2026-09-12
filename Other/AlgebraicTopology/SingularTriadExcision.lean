/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Other.AlgebraicTopology.SingularTriadCapProduct
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Field
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Excision for the chain complex of a topological triad

For subsets `A B ⊆ X`, this file compares the sum-relative chain complex

`coker(C_*(A; ℚ) ⊕ C_*(B; ℚ) ⟶ C_*(X; ℚ))`

with the ordinary relative chain complex `C_*(X, A ∪ B; ℚ)`.  The comparison is a
quasi-isomorphism when `A` and `B`, regarded as subsets of `A ∪ B`, are open.  The proof uses
the affine-subdivision small-chain theorem for the two-set cover of `A ∪ B`.

The argument factors the comparison into two pieces.  First, the sum of the chains on `A` and
`B` maps epimorphically onto the cover-small chains of `A ∪ B`, so replacing the former by the
latter does not change the cokernel.  Second, the open-cover small-chain inclusion is a
quasi-isomorphism, and the short exact homology sequence transfers this to the relative
cokernels.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial
open scoped Simplicial

namespace AlgebraicTopology.Singular

variable (X : TopCat) (A B : Set X)

/-- The cover of `A ∪ B` by the subsets induced by `A` and `B`. -/
def triadUnionCover : Bool → Set (TopPair.ofSubset (A ∪ B)).snd :=
  fun b ↦ if b then {x | x.1 ∈ A} else {x | x.1 ∈ B}

/-- The induced two-set cover covers all of `A ∪ B`. -/
lemma triadUnionCover_iUnion :
    ⋃ b, triadUnionCover X A B b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases x.2 with hx | hx
  · exact Set.mem_iUnion.2 ⟨true, by simpa [triadUnionCover] using hx⟩
  · exact Set.mem_iUnion.2 ⟨false, by simpa [triadUnionCover] using hx⟩

/-- Openness of `A` and `B` in their union makes the induced cover open. -/
lemma triadUnionCover_isOpen
    (hA : IsOpen (triadUnionCover X A B true))
    (hB : IsOpen (triadUnionCover X A B false)) :
    ∀ b, IsOpen (triadUnionCover X A B b) :=
  fun b ↦ Bool.rec hB hA b

/-- Identify `A` with the `true` member of the induced cover of `A ∪ B`. -/
def triadLeftToUnionCoverMember :
    (TopPair.ofSubset A).snd ⟶ TopCat.of (triadUnionCover X A B true) :=
  TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, Or.inl x.2⟩, x.2⟩, by fun_prop⟩

/-- Identify `B` with the `false` member of the induced cover of `A ∪ B`. -/
def triadRightToUnionCoverMember :
    (TopPair.ofSubset B).snd ⟶ TopCat.of (triadUnionCover X A B false) :=
  TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, Or.inr x.2⟩, x.2⟩, by fun_prop⟩

/-- Forget the redundant membership proof from the `true` cover member. -/
def triadUnionCoverMemberToLeft :
    TopCat.of (triadUnionCover X A B true) ⟶ (TopPair.ofSubset A).snd :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩

/-- Forget the redundant membership proof from the `false` cover member. -/
def triadUnionCoverMemberToRight :
    TopCat.of (triadUnionCover X A B false) ⟶ (TopPair.ofSubset B).snd :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩

/-- The simplicial map from `A` to the small singular subcomplex of `A ∪ B`. -/
def triadLeftToUnionSmallSingularSet :
    TopCat.toSSet.obj (TopPair.ofSubset A).snd ⟶
      coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
        (triadUnionCover X A B) :=
  TopCat.toSSet.map (triadLeftToUnionCoverMember X A B) ≫
    coverMemberToSmallSingularSet (TopPair.ofSubset (A ∪ B)).snd
      (triadUnionCover X A B) true

/-- The simplicial map from `B` to the small singular subcomplex of `A ∪ B`. -/
def triadRightToUnionSmallSingularSet :
    TopCat.toSSet.obj (TopPair.ofSubset B).snd ⟶
      coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
        (triadUnionCover X A B) :=
  TopCat.toSSet.map (triadRightToUnionCoverMember X A B) ≫
    coverMemberToSmallSingularSet (TopPair.ofSubset (A ∪ B)).snd
      (triadUnionCover X A B) false

/-- Rational chains on the two-set cover-small singular subcomplex of `A ∪ B`. -/
abbrev TriadUnionSmallChainComplex : ChainCategory ℚ :=
  CoverSmallRationalSingularChainComplex (TopPair.ofSubset (A ∪ B)).snd
    (triadUnionCover X A B)

/-- The chain map from `A` into the cover-small chains of `A ∪ B`. -/
def triadLeftToUnionSmallChains :
    ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj
        (TopPair.ofSubset A).snd ⟶
      TriadUnionSmallChainComplex X A B :=
  SSet.chainComplexMap (triadLeftToUnionSmallSingularSet X A B) (ModuleCat.of ℚ ℚ)

/-- The chain map from `B` into the cover-small chains of `A ∪ B`. -/
def triadRightToUnionSmallChains :
    ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj
        (TopPair.ofSubset B).snd ⟶
      TriadUnionSmallChainComplex X A B :=
  SSet.chainComplexMap (triadRightToUnionSmallSingularSet X A B) (ModuleCat.of ℚ ℚ)

/-- The two cover-member chain maps, combined into a map onto cover-small chains. -/
def triadCoverMembersToUnionSmallChains :
    (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj
          (TopPair.ofSubset A).snd ⊞
        ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj
          (TopPair.ofSubset B).snd) ⟶
      TriadUnionSmallChainComplex X A B :=
  biprod.desc (triadLeftToUnionSmallChains X A B)
    (triadRightToUnionSmallChains X A B)

/-- Every small simplex of the two-set cover comes from a simplex of `A` or a simplex of `B`.
This is the set-level fact behind the epimorphism from the sum of the two chain complexes. -/
lemma triadUnionSmallSimplex_exists_left_or_right {n : SimplexCategoryᵒᵖ}
    (sigma : (coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
      (triadUnionCover X A B) : SSet).obj n) :
    (∃ a : (TopCat.toSSet.obj (TopPair.ofSubset A).snd).obj n,
      (triadLeftToUnionSmallSingularSet X A B).app n a = sigma) ∨
    (∃ b : (TopCat.toSSet.obj (TopPair.ofSubset B).snd).obj n,
      (triadRightToUnionSmallSingularSet X A B).app n b = sigma) := by
  obtain ⟨i, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage
      (TopPair.ofSubset (A ∪ B)).snd (triadUnionCover X A B) sigma.1).mp sigma.2
  cases i with
  | false =>
      right
      let b := (TopCat.toSSet.map (triadUnionCoverMemberToRight X A B)).app n y
      refine ⟨b, ?_⟩
      change (coverMemberToSmallSingularSet (TopPair.ofSubset (A ∪ B)).snd
        (triadUnionCover X A B) false).app n
          ((TopCat.toSSet.map (triadRightToUnionCoverMember X A B)).app n b) = sigma
      have hback :
          (TopCat.toSSet.map (triadRightToUnionCoverMember X A B)).app n b = y := by
        apply ((TopCat.of (triadUnionCover X A B false)).toSSetObjEquiv n).injective
        ext t
        rfl
      rw [hback]
      exact Subtype.ext hy
  | true =>
      left
      let a := (TopCat.toSSet.map (triadUnionCoverMemberToLeft X A B)).app n y
      refine ⟨a, ?_⟩
      change (coverMemberToSmallSingularSet (TopPair.ofSubset (A ∪ B)).snd
        (triadUnionCover X A B) true).app n
          ((TopCat.toSSet.map (triadLeftToUnionCoverMember X A B)).app n a) = sigma
      have hback :
          (TopCat.toSSet.map (triadLeftToUnionCoverMember X A B)).app n a = y := by
        apply ((TopCat.of (triadUnionCover X A B true)).toSSetObjEquiv n).injective
        ext t
        rfl
      rw [hback]
      exact Subtype.ext hy

/-- In each degree, the sum of the two cover-member chain groups surjects onto the small-chain
group. -/
lemma triadCoverMembersToUnionSmallChains_component_epi (n : ℕ) :
    Epi ((triadCoverMembersToUnionSmallChains X A B).f n) := by
  constructor
  intro Z f g h
  apply SSet.chainComplex_hom_ext
  intro sigma
  rcases triadUnionSmallSimplex_exists_left_or_right X A B sigma with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · let ia : ModuleCat.of ℚ ℚ ⟶
        (((singularChainComplexFunctor (ModuleCat ℚ)).obj
          (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset A).snd).X n :=
      (TopCat.toSSet.obj (TopPair.ofSubset A).snd).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) a
    let k := ia ≫
        (biprod.inl :
          ((singularChainComplexFunctor (ModuleCat ℚ)).obj
              (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset A).snd ⟶
            (((singularChainComplexFunctor (ModuleCat ℚ)).obj
                (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset A).snd ⊞
              ((singularChainComplexFunctor (ModuleCat ℚ)).obj
                (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset B).snd)).f n
    have hk : k ≫ (triadCoverMembersToUnionSmallChains X A B).f n =
        (coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
          (triadUnionCover X A B) : SSet).ιChainComplex
            (R := ModuleCat.of ℚ ℚ) sigma := by
      change (ia ≫ _) ≫ _ = _
      rw [Category.assoc]
      dsimp [triadCoverMembersToUnionSmallChains]
      rw [HomologicalComplex.biprod_inl_desc_f]
      change _ ≫ (SSet.chainComplexMap
        (triadLeftToUnionSmallSingularSet X A B) (ModuleCat.of ℚ ℚ)).f n = _
      dsimp [ia]
      rw [SSet.ι_chainComplexMap_f, ha]
    rw [← hk, Category.assoc, h, ← Category.assoc, hk]
  · let ib : ModuleCat.of ℚ ℚ ⟶
        (((singularChainComplexFunctor (ModuleCat ℚ)).obj
          (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset B).snd).X n :=
      (TopCat.toSSet.obj (TopPair.ofSubset B).snd).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) b
    let k := ib ≫
        (biprod.inr :
          ((singularChainComplexFunctor (ModuleCat ℚ)).obj
              (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset B).snd ⟶
            (((singularChainComplexFunctor (ModuleCat ℚ)).obj
                (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset A).snd ⊞
              ((singularChainComplexFunctor (ModuleCat ℚ)).obj
                (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset B).snd)).f n
    have hk : k ≫ (triadCoverMembersToUnionSmallChains X A B).f n =
        (coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
          (triadUnionCover X A B) : SSet).ιChainComplex
            (R := ModuleCat.of ℚ ℚ) sigma := by
      change (ib ≫ _) ≫ _ = _
      rw [Category.assoc]
      dsimp [triadCoverMembersToUnionSmallChains]
      rw [HomologicalComplex.biprod_inr_desc_f]
      change _ ≫ (SSet.chainComplexMap
        (triadRightToUnionSmallSingularSet X A B) (ModuleCat.of ℚ ℚ)).f n = _
      dsimp [ib]
      rw [SSet.ι_chainComplexMap_f, hb]
    rw [← hk, Category.assoc, h, ← Category.assoc, hk]

/-- The sum of the two cover-member chain complexes maps epimorphically onto the cover-small
chain complex. -/
instance triadCoverMembersToUnionSmallChains_epi :
    Epi (triadCoverMembersToUnionSmallChains X A B) :=
  HomologicalComplex.epi_of_epi_f _
    (triadCoverMembersToUnionSmallChains_component_epi X A B)

@[reassoc]
lemma triadLeftToUnionCoverMember_comp_inclusion :
    triadLeftToUnionCoverMember X A B ≫
        topologicalSubsetInclusion (TopPair.ofSubset (A ∪ B)).snd
          (triadUnionCover X A B true) =
      subsetToUnionLeft X A B := by
  ext x
  rfl

@[reassoc]
lemma triadRightToUnionCoverMember_comp_inclusion :
    triadRightToUnionCoverMember X A B ≫
        topologicalSubsetInclusion (TopPair.ofSubset (A ∪ B)).snd
          (triadUnionCover X A B false) =
      subsetToUnionRight X A B := by
  ext x
  rfl

@[reassoc]
lemma triadLeftToUnionSmallSingularSet_comp_inclusion :
    triadLeftToUnionSmallSingularSet X A B ≫
        (coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
          (triadUnionCover X A B)).ι =
      TopCat.toSSet.map (subsetToUnionLeft X A B) := by
  rw [triadLeftToUnionSmallSingularSet, Category.assoc,
    coverMemberToSmallSingularSet_comp_inclusion, ← Functor.map_comp,
    triadLeftToUnionCoverMember_comp_inclusion]

@[reassoc]
lemma triadRightToUnionSmallSingularSet_comp_inclusion :
    triadRightToUnionSmallSingularSet X A B ≫
        (coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
          (triadUnionCover X A B)).ι =
      TopCat.toSSet.map (subsetToUnionRight X A B) := by
  rw [triadRightToUnionSmallSingularSet, Category.assoc,
    coverMemberToSmallSingularSet_comp_inclusion, ← Functor.map_comp,
    triadRightToUnionCoverMember_comp_inclusion]

/-- Inclusion of the two-set small chains into all chains on `A ∪ B`. -/
abbrev triadUnionSmallChainInclusion :
    TriadUnionSmallChainComplex X A B ⟶
      ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset (A ∪ B)).snd :=
  coverSmallRationalSingularChainInclusion (TopPair.ofSubset (A ∪ B)).snd
    (triadUnionCover X A B)

lemma triadLeftToUnionSmallChains_comp_inclusion :
    triadLeftToUnionSmallChains X A B ≫
        triadUnionSmallChainInclusion X A B =
      subsetToUnionLeftChainMap ℚ X A B := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map (triadLeftToUnionSmallSingularSet X A B) ≫
      F.map (coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
        (triadUnionCover X A B)).ι =
    F.map (TopCat.toSSet.map (subsetToUnionLeft X A B))
  rw [← Functor.map_comp, triadLeftToUnionSmallSingularSet_comp_inclusion]

lemma triadRightToUnionSmallChains_comp_inclusion :
    triadRightToUnionSmallChains X A B ≫
        triadUnionSmallChainInclusion X A B =
      subsetToUnionRightChainMap ℚ X A B := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map (triadRightToUnionSmallSingularSet X A B) ≫
      F.map (coverSmallSingularSubcomplex (TopPair.ofSubset (A ∪ B)).snd
        (triadUnionCover X A B)).ι =
    F.map (TopCat.toSSet.map (subsetToUnionRight X A B))
  rw [← Functor.map_comp, triadRightToUnionSmallSingularSet_comp_inclusion]

/-- The explicit singular-chain map for the inclusion `A ∪ B ⊆ X`. -/
def triadUnionAmbientChainMap :
    ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset (A ∪ B)).snd ⟶
      ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj X :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (A ∪ B)).map)
    (ModuleCat.of ℚ ℚ)

lemma triadUnionAmbientChainMap_eq_subspaceChainMap :
    triadUnionAmbientChainMap X A B =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (A ∪ B))).hom :=
  rfl

/-- The explicit singular-chain map for `A ⊆ X`. -/
def triadLeftAmbientChainMap :
    ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset A).snd ⟶
      ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj X :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset A).map)
    (ModuleCat.of ℚ ℚ)

/-- The explicit singular-chain map for `B ⊆ X`. -/
def triadRightAmbientChainMap :
    ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopPair.ofSubset B).snd ⟶
      ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj X :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset B).map)
    (ModuleCat.of ℚ ℚ)

lemma triadLeftAmbientChainMap_eq_subspaceChainMap :
    triadLeftAmbientChainMap X A =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset A)).hom :=
  rfl

lemma triadRightAmbientChainMap_eq_subspaceChainMap :
    triadRightAmbientChainMap X B =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset B)).hom :=
  rfl

lemma triadSubspaceChainMap_eq_explicit :
    triadSubspaceChainMap ℚ X A B =
      biprod.desc (triadLeftAmbientChainMap X A)
        (triadRightAmbientChainMap X B) := by
  rw [triadSubspaceChainMap, triadLeftAmbientChainMap_eq_subspaceChainMap,
    triadRightAmbientChainMap_eq_subspaceChainMap]

/-- Include cover-small chains of `A ∪ B` into ambient chains on `X`. -/
def triadUnionSmallToAmbientChains :
    TriadUnionSmallChainComplex X A B ⟶
      ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj X :=
  triadUnionSmallChainInclusion X A B ≫
    triadUnionAmbientChainMap X A B

lemma triadLeftToUnionSmallChains_comp_ambient :
    triadLeftToUnionSmallChains X A B ≫
        triadUnionSmallToAmbientChains X A B =
      triadLeftAmbientChainMap X A := by
  rw [triadUnionSmallToAmbientChains, ← Category.assoc,
    triadLeftToUnionSmallChains_comp_inclusion]
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map (TopCat.toSSet.map (subsetToUnionLeft X A B)) ≫
      F.map (TopCat.toSSet.map (TopPair.ofSubset (A ∪ B)).map) =
    F.map (TopCat.toSSet.map (TopPair.ofSubset A).map)
  rw [← Functor.map_comp, ← Functor.map_comp,
    subsetToUnionLeft_comp_unionMap]
  rfl

lemma triadRightToUnionSmallChains_comp_ambient :
    triadRightToUnionSmallChains X A B ≫
        triadUnionSmallToAmbientChains X A B =
      triadRightAmbientChainMap X B := by
  rw [triadUnionSmallToAmbientChains, ← Category.assoc,
    triadRightToUnionSmallChains_comp_inclusion]
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map (TopCat.toSSet.map (subsetToUnionRight X A B)) ≫
      F.map (TopCat.toSSet.map (TopPair.ofSubset (A ∪ B)).map) =
    F.map (TopCat.toSSet.map (TopPair.ofSubset B).map)
  rw [← Functor.map_comp, ← Functor.map_comp,
    subsetToUnionRight_comp_unionMap]
  rfl

/-- The original two-summand map factors through the cover-small chains of `A ∪ B`. -/
lemma triadCoverMembersToUnionSmallChains_comp_ambient :
    triadCoverMembersToUnionSmallChains X A B ≫
        triadUnionSmallToAmbientChains X A B =
      triadSubspaceChainMap ℚ X A B := by
  rw [triadSubspaceChainMap_eq_explicit]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.biprodX_ext_from
  · rw [HomologicalComplex.comp_f, ← Category.assoc]
    dsimp [triadCoverMembersToUnionSmallChains]
    rw [HomologicalComplex.biprod_inl_desc_f, HomologicalComplex.biprod_inl_desc_f]
    exact congrArg (fun f ↦ f.f n)
      (triadLeftToUnionSmallChains_comp_ambient X A B)
  · rw [HomologicalComplex.comp_f, ← Category.assoc]
    dsimp [triadCoverMembersToUnionSmallChains]
    rw [HomologicalComplex.biprod_inr_desc_f, HomologicalComplex.biprod_inr_desc_f]
    exact congrArg (fun f ↦ f.f n)
      (triadRightToUnionSmallChains_comp_ambient X A B)

/-- The relative quotient obtained by killing cover-small chains in the ambient chain complex. -/
abbrev TriadUnionSmallRelativeChainComplex : ChainCategory ℚ :=
  cokernel (triadUnionSmallToAmbientChains X A B)

/-- Replacing `C_*(A) ⊕ C_*(B)` by the two-set cover-small complex does not change the
relative cokernel. -/
def triadRelativeUnionSmallIso :
    triadRelativeChainComplex ℚ X A B ≅
      TriadUnionSmallRelativeChainComplex X A B :=
  cokernelIsoOfEq (triadCoverMembersToUnionSmallChains_comp_ambient X A B).symm ≪≫
    cokernelEpiComp (triadCoverMembersToUnionSmallChains X A B)
      (triadUnionSmallToAmbientChains X A B)

/-- Projection of ambient chains onto the small-relative quotient. -/
abbrev triadUnionSmallRelativeProjection :
    ((singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj X ⟶
      TriadUnionSmallRelativeChainComplex X A B :=
  cokernel.π (triadUnionSmallToAmbientChains X A B)

@[reassoc]
lemma triadRelativeChainProjection_comp_unionSmallIso :
    triadRelativeChainProjection ℚ X A B ≫
        (triadRelativeUnionSmallIso X A B).hom =
      triadUnionSmallRelativeProjection X A B := by
  change cokernel.π (triadSubspaceChainMap ℚ X A B) ≫
      ((cokernelIsoOfEq
          (triadCoverMembersToUnionSmallChains_comp_ambient X A B).symm).hom ≫
        (cokernelEpiComp (triadCoverMembersToUnionSmallChains X A B)
          (triadUnionSmallToAmbientChains X A B)).hom) =
    cokernel.π (triadUnionSmallToAmbientChains X A B)
  rw [← Category.assoc, π_comp_cokernelIsoOfEq_hom]
  simp [cokernelEpiComp]

instance triadUnionAmbientInclusion_mono :
    Mono (TopPair.ofSubset (A ∪ B)).map :=
  (TopCat.mono_iff_injective _).2 fun _ _ h ↦ Subtype.ext h

instance triadUnionAmbientChainMap_mono :
    Mono (triadUnionAmbientChainMap X A B) := by
  dsimp [triadUnionAmbientChainMap, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

instance triadUnionSubspaceChainMap_mono :
    Mono (((chainPairFunctor ℚ).obj (TopPair.ofSubset (A ∪ B))).hom) := by
  rw [← triadUnionAmbientChainMap_eq_subspaceChainMap]
  exact triadUnionAmbientChainMap_mono X A B

instance triadUnionSmallToAmbientChains_mono :
    Mono (triadUnionSmallToAmbientChains X A B) :=
  mono_comp'
    (coverSmallRationalSingularChainInclusion_mono
      (TopPair.ofSubset (A ∪ B)).snd (triadUnionCover X A B))
    (triadUnionAmbientChainMap_mono X A B)

/-- The arrow whose cokernel is the small-relative chain complex. -/
def triadUnionSmallChainArrow : Arrow (ChainCategory ℚ) :=
  Arrow.mk (triadUnionSmallToAmbientChains X A B)

/-- The morphism from the cover-small pair to the ordinary pair `(X, A ∪ B)`. -/
def triadUnionSmallToUnionPairArrow :
    triadUnionSmallChainArrow X A B ⟶
      (chainPairFunctor ℚ).obj (TopPair.ofSubset (A ∪ B)) := by
  refine Arrow.homMk (triadUnionSmallChainInclusion X A B) (𝟙 _) ?_
  change triadUnionSmallChainInclusion X A B ≫
      triadUnionAmbientChainMap X A B =
    triadUnionSmallToAmbientChains X A B ≫ 𝟙 _
  simp [triadUnionSmallToAmbientChains]

/-- The map from the small-relative quotient to ordinary chains relative to `A ∪ B`. -/
def triadUnionSmallRelativeToUnionRelativeChainMap :
    TriadUnionSmallRelativeChainComplex X A B ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (A ∪ B)) :=
  (Limits.coker (C := ChainCategory ℚ)).map
    (triadUnionSmallToUnionPairArrow X A B)

@[reassoc]
lemma triadUnionSmallRelativeProjection_comp_toUnion :
    triadUnionSmallRelativeProjection X A B ≫
        triadUnionSmallRelativeToUnionRelativeChainMap X A B =
      relativeChainProjection ℚ (TopPair.ofSubset (A ∪ B)) :=
  ((coker.π (C := ChainCategory ℚ)).naturality
    (triadUnionSmallToUnionPairArrow X A B)).symm

/-- The morphism between the small and ordinary cokernel short exact sequences. -/
def triadUnionSmallToUnionCokernelSequenceHom :
    ShortComplex.cokernelSequence (triadUnionSmallToAmbientChains X A B) ⟶
      ShortComplex.cokernelSequence
        ((chainPairFunctor ℚ).obj (TopPair.ofSubset (A ∪ B))).hom :=
  ShortComplex.homMk
    (triadUnionSmallChainInclusion X A B)
    (𝟙 _)
    (triadUnionSmallRelativeToUnionRelativeChainMap X A B)
    (by
      change triadUnionSmallChainInclusion X A B ≫
          triadUnionAmbientChainMap X A B =
        triadUnionSmallToAmbientChains X A B ≫ 𝟙 _
      simp [triadUnionSmallToAmbientChains])
    (triadUnionSmallRelativeProjection_comp_toUnion X A B).symm

lemma triadUnionSmallCokernelSequence_shortExact :
    (ShortComplex.cokernelSequence
      (triadUnionSmallToAmbientChains X A B)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := triadUnionSmallToAmbientChains_mono X A B
  epi_g := by infer_instance

lemma triadUnionCokernelSequence_shortExact :
    (ShortComplex.cokernelSequence
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (A ∪ B))).hom).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := triadUnionSubspaceChainMap_mono X A B
  epi_g := by infer_instance

/-- The small-relative quotient is quasi-isomorphic to ordinary relative chains whenever `A`
and `B` are open in `A ∪ B`. -/
theorem triadUnionSmallRelativeToUnionRelative_quasiIso
    (hA : IsOpen (triadUnionCover X A B true))
    (hB : IsOpen (triadUnionCover X A B false)) :
    QuasiIso (triadUnionSmallRelativeToUnionRelativeChainMap X A B) := by
  let e := coverSmallRationalChainHomotopyEquiv_of_openCover
    (TopPair.ofSubset (A ∪ B)).snd (triadUnionCover X A B)
      (triadUnionCover_isOpen X A B hA hB) (triadUnionCover_iUnion X A B)
  have hsmall : QuasiIso e.hom := e.quasiIso_hom
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom] at hsmall
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (triadUnionSmallToUnionCokernelSequenceHom X A B)
    (triadUnionSmallCokernelSequence_shortExact X A B)
    (triadUnionCokernelSequence_shortExact X A B)
    hsmall (inferInstanceAs (QuasiIso (𝟙 (((singularChainComplexFunctor
      (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj X))))

/-- Factoring through the two-set small-relative quotient recovers the canonical map from the
sum-relative triad complex to ordinary chains relative to `A ∪ B`. -/
lemma triadRelativeUnionSmallIso_hom_comp_toUnion :
    (triadRelativeUnionSmallIso X A B).hom ≫
        triadUnionSmallRelativeToUnionRelativeChainMap X A B =
      triadToUnionRelativeChainMap ℚ X A B := by
  let : Epi (triadRelativeChainProjection ℚ X A B) := by
    change Epi (cokernel.π (triadSubspaceChainMap ℚ X A B))
    infer_instance
  apply (cancel_epi (triadRelativeChainProjection ℚ X A B)).1
  rw [← Category.assoc, triadRelativeChainProjection_comp_unionSmallIso,
    triadUnionSmallRelativeProjection_comp_toUnion,
    triadRelativeChainProjection_triadToUnionRelativeChainMap]

/-- Triad excision over `ℚ`: if `A` and `B` are open as subsets of `A ∪ B`, the canonical
comparison from the sum-relative triad complex to ordinary chains relative to `A ∪ B` is a
quasi-isomorphism. -/
theorem triadToUnionRelativeChainMap_quasiIso_of_openCover
    (hA : IsOpen (triadUnionCover X A B true))
    (hB : IsOpen (triadUnionCover X A B false)) :
    QuasiIso (triadToUnionRelativeChainMap ℚ X A B) := by
  let : IsIso (triadRelativeUnionSmallIso X A B).hom :=
    (triadRelativeUnionSmallIso X A B).isIso_hom
  let : QuasiIso (triadRelativeUnionSmallIso X A B).hom := inferInstance
  let : QuasiIso
      (triadUnionSmallRelativeToUnionRelativeChainMap X A B) :=
    triadUnionSmallRelativeToUnionRelative_quasiIso X A B hA hB
  rw [← triadRelativeUnionSmallIso_hom_comp_toUnion]
  infer_instance

/-- In particular, ambiently open subsets satisfy the triad excision hypothesis. -/
theorem triadToUnionRelativeChainMap_quasiIso_of_isOpen
    (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (triadToUnionRelativeChainMap ℚ X A B) := by
  apply triadToUnionRelativeChainMap_quasiIso_of_openCover X A B
  · exact hA.preimage continuous_subtype_val
  · exact hB.preimage continuous_subtype_val

end AlgebraicTopology.Singular
