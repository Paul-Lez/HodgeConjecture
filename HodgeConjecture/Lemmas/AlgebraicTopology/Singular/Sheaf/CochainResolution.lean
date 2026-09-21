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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SingularSheafComparison

/-!
# The singular-cochain resolution of a constant sheaf

The map from a constant sheaf to its sheafified singular-cochain complex is a monomorphism, and
a quasi-isomorphism on a space with a basis of contractible open sets.
-/

@[expose] public noncomputable section

open CategoryTheory Filter Limits TopologicalSpace

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The constant-to-singular-cochain resolution is a monomorphism of complexes. -/
lemma constantsToSingularCochainSheafComplex_mono
    (R : Type) [CommRing R] (Y : TopCat.{0}) :
    Mono (constantsToSingularCochainSheafComplex R Y) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  cases n with
  | zero =>
      change Mono (constantsToSingularCochainZeroSheaf R Y)
      exact constantsToSingularCochainZeroSheaf_mono R Y
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        𝓒(Y; R) (n + 1) (by lia)).mono _

/-- Extending the constant-to-singular-cochain resolution to integer degrees remains monic. -/
lemma constantsToSingularCochainComplexInt_mono
    (R : Type) [CommRing R] (Y : TopCat.{0}) :
    Mono (HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex R Y) ComplexShape.embeddingUpNat) := by
  let a := constantsToSingularCochainSheafComplex R Y
  let : Mono a := constantsToSingularCochainSheafComplex_mono R Y
  apply HomologicalComplex.mono_of_mono_f
  intro n
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    change Mono ((HomologicalComplex.extendMap a ComplexShape.embeddingUpNat).f (m : ℤ))
    rw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat
      (i := m) (i' := (m : ℤ)) rfl]
    infer_instance
  · exact (((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat Y)).obj
      𝓒(Y; R)).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)).mono _

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [CommRing R] {U X : TopCat.{u}} (j : U ⟶ X)

lemma contractibleOpenBasis_of_isOpenEmbedding
    (hj : Topology.IsOpenEmbedding j)
    (hX : ∀ (x : X) (V : Opens X), x ∈ V →
      ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V) :
    ∀ (x : U) (V : Opens U), x ∈ V →
      ∃ (W : Opens U), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V := by
  intro x V hxV
  let Vi : Opens X := ⟨j '' (V : Set U), (hj.isOpen_iff_image_isOpen).mp V.2⟩
  have hjx : j x ∈ Vi := ⟨x, hxV, rfl⟩
  obtain ⟨W, hjxW, hWcontractible, hWVi⟩ := hX (j x) Vi hjx
  let W' : Opens U :=
    ⟨j ⁻¹' (W : Set X), W.2.preimage j.hom.continuous⟩
  have hWrange : (W : Set X) ⊆ Set.range j := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hWVi hy
    exact ⟨z, hzy⟩
  have hW'contractible : ContractibleSpace W' := by
    change ContractibleSpace (j ⁻¹' (W : Set X))
    exact (hj.toIsEmbedding.homeomorphOfSubsetRange hWrange).contractibleSpace_iff.mpr
      hWcontractible
  refine ⟨W', hjxW, hW'contractible, ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hWVi hy
  exact hj.toIsEmbedding.injective hzy ▸ hz

lemma locallyPathConnectedSpace_of_contractibleOpenBasis
    (hX : ∀ (x : X) (V : Opens X), x ∈ V →
      ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V) :
    LocallyPathConnectedSpace X := by
  refine ⟨fun x ↦ hasBasis_self.mpr fun S hS ↦ ?_⟩
  obtain ⟨V, hVS, hVopen, hxV⟩ := mem_nhds_iff.mp hS
  let Vo : Opens X := ⟨V, hVopen⟩
  obtain ⟨W, hxW, hWcontractible, hWVo⟩ := hX x Vo hxV
  refine ⟨(W : Set X), W.2.mem_nhds hxW, ?_, ?_⟩
  · rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance
  · exact fun y hy ↦ hVS (hWVo hy)

lemma constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis
    (hX : ∀ (x : X) (V : Opens X), x ∈ V →
      ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V) :
    QuasiIso (constantsToSingularCochainSheafComplex R X) := by
  let : LocallyPathConnectedSpace X :=
    locallyPathConnectedSpace_of_contractibleOpenBasis hX
  constructor
  intro n
  cases n with
  | zero => exact constantsToSingularCochainSheafComplex_quasiIsoAt_zero R X
  | succ n =>
      exact constantsToSingularCochainSheafComplex_quasiIsoAt_succ_of_contractibleOpenBasis
        R X hX n

end AlgebraicTopology.Singular

end
