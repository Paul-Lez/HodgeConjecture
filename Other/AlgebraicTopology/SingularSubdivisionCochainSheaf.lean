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

public import Other.Algebra.Homology.LinearDual
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import Other.AlgebraicTopology.FlasqueAcyclic

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

/-- Lift a singular simplex through an inclusion of open subsets, provided all of its values lie
in the smaller open subset. -/
noncomputable def openSimplexLift {X : TopCat.{u}} {U V : Opens X} (n : ℕ)
    (s : OpenSimplex X (.op U) n)
    (h : ∀ z, (((TopCat.of U).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) s z : U) : X) ∈ V) :
    OpenSimplex X (.op V) n := by
  let m := Opposite.op (SimplexCategory.mk n)
  let fs := (TopCat.of U).toSSetObjEquiv m s
  let f : C(stdSimplex ℝ (Fin (n + 1)), TopCat.of V) :=
    ⟨fun z ↦ ⟨((fs z : U) : X), h z⟩,
      Continuous.subtype_mk
        (continuous_subtype_val.comp fs.continuous) _⟩
  exact (TopCat.of V).toSSetObjEquiv m |>.symm f

@[simp]
lemma openSimplexMap_openSimplexLift {X : TopCat.{u}} {U V : Opens X} (i : V ⟶ U) (n : ℕ)
    (s : OpenSimplex X (.op U) n)
    (h : ∀ z, (((TopCat.of U).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) s z : U) : X) ∈ V) :
    openSimplexMap X i.op n (openSimplexLift n s h) = s := by
  apply (TopCat.of U).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n)) |>.injective
  rfl

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Ordinary singular cochain cohomology is canonically linearly equivalent to the cohomology of
cochains on the top open subset. -/
noncomputable def cochainCohomologyEquivTopOpen (n : ℕ) :
    CochainCohomology R X n ≃ₗ[R]
      ((TopOpenSingularChainComplex R X).sc n).linearDual.homology :=
  HomologicalComplex.HomotopyEquiv.linearDualCohomologyEquiv
    (HomotopyEquiv.ofIso (topOpenSingularChainComplexIso R X)) n

section RationalCover
variable {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

/-- The cover-small homotopy equivalence, with its source written as cochains on the top open
subset. -/
def topOpenRationalCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
      (CoverSmallRationalSingularChainComplex Y U).linearDualCochainComplex :=
  by
    let e₁ : HomotopyEquiv
        (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
        ((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of ℚ ℚ)).linearDualCochainComplex :=
      HomotopyEquiv.ofIso (singularCochainComplexIsoTopOpen ℚ Y).symm
    exact e₁.trans
      (rationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover)

lemma topOpenRationalCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (topOpenRationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
      topOpenRationalCochainRestrictionToCoverSmall Y U := by
  change (singularCochainComplexIsoTopOpen ℚ Y).inv ≫
      (rationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
    (singularCochainComplexIsoTopOpen ℚ Y).inv ≫
      rationalCochainRestrictionToCoverSmall Y U
  rw [rationalCochainHomotopyEquivCoverSmall_hom]

/-- For an open cover, restriction from top-open rational cochains to cover-small cochains is a
quasi-isomorphism. -/
theorem topOpenRationalCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (topOpenRationalCochainRestrictionToCoverSmall Y U) := by
  rw [← topOpenRationalCochainHomotopyEquivCoverSmall_hom Y U hUopen hUcover]
  infer_instance

/-- The complex of top-open rational cochains vanishing on all chains subordinate to an open
cover is acyclic. -/
theorem topOpenRationalCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (topOpenRationalCochainRestrictionToCoverSmall Y U)).Acyclic := by
  let := topOpenRationalCochainRestrictionToCoverSmall_quasiIso
    Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (topOpenRationalCochainRestrictionToCoverSmall Y U)

end RationalCover

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

variable {R : Type u} [Field R] {X : TopCat.{u}}

/-- Every positive sheaf-cohomology group of a term of the singular-cochain resolution vanishes
on a hereditarily paracompact Hausdorff space. -/
lemma singularCochainSheaf_cohomology_succ_eq_zero
    [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (n q : ℕ) (x : Abelian.Ext
      (TopCat.Sheaf.IsFlasque.globalSectionsSource (X := X))
      (singularCochainSheaf R X n) (q + 1)) :
    x = 0 :=
  TopCat.Sheaf.IsFlasque.cohomology_succ_eq_zero
    (singularCochainSheaf R X n) q x

end AlgebraicTopology.Singular
