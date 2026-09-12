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

public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularExcisionOpenCover

/-!
# Integral small-chain approximation

Small-chain approximation for an open cover gives an isomorphism on integral singular homology in
every degree, and it is induced by the inclusion of small chains. A cover one of whose members is
the whole space is small to begin with, so there the isomorphism is available directly.

The conjecture is stated with rational coefficients, where
`coverSmallRationalSingularHomologyIso_of_openCover` plays this role, so the integral statement is
not needed to state it.
-/

@[expose] public section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace AlgebraicTopology.Singular

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- A subspace equal to the whole space is homeomorphic to the ambient space by its inclusion. -/
public noncomputable def topologicalSubsetHomeomorphOfEqUniv
    (s : Set X) (hs : s = Set.univ) : s ≃ₜ X :=
  (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ X)

/-- The subspace inclusion is an isomorphism when the subset is all of `X`. -/
public theorem topologicalSubsetInclusion_isIso_of_eq_univ
    (s : Set X) (hs : s = Set.univ) :
    IsIso (topologicalSubsetInclusion X s) := by
  change IsIso (TopCat.isoOfHomeo
    (X := TopCat.of s) (Y := X) (topologicalSubsetHomeomorphOfEqUniv X s hs)).hom
  infer_instance

/-- If one cover member is the whole space, every singular simplex is already small. -/
public theorem coverSmallSingularSubcomplex_eq_top_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    coverSmallSingularSubcomplex X U = ⊤ := by
  let := topologicalSubsetInclusion_isIso_of_eq_univ X (U j) hj
  have hrange : SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U j))) = ⊤ :=
    SSet.Subcomplex.range_eq_top _
  exact top_unique (hrange ▸ le_iSup (fun k ↦ SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U k)))) j)

/-- For a cover containing the whole space, the small-chain inclusion is an isomorphism. -/
public theorem coverSmallIntegralSingularChainInclusion_isIso_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    IsIso (coverSmallIntegralSingularChainInclusion X U) := by
  let htop := coverSmallSingularSubcomplex_eq_top_of_member_eq_univ X U j hj
  let e : (coverSmallSingularSubcomplex X U : SSet) ≅ TopCat.toSSet.obj X :=
    SSet.Subcomplex.eqToIso htop ≪≫ SSet.Subcomplex.topIso _
  have he : e.hom = (coverSmallSingularSubcomplex X U).ι := by
    dsimp [e]
    exact SSet.Subcomplex.homOfLE_ι htop.le
  change IsIso (((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (coverSmallSingularSubcomplex X U).ι)
  rw [← he]
  infer_instance

/-- The small-chain approximation theorem holds directly for a cover containing the whole
space, without subdivision. -/
public theorem coverSmallChainApproximation_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
      (coverSmallIntegralSingularChainInclusion X U) := by
  let := coverSmallIntegralSingularChainInclusion_isIso_of_member_eq_univ X U j hj
  exact HomologicalComplex.homotopyEquivalences.of_isIso _

/-- Small-chain approximation gives the expected homology isomorphism in every degree. -/
public noncomputable def coverSmallIntegralSingularHomologyIso_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (CoverSmallIntegralSingularChainComplex X U).homology n ≅
      (IntegralSingularChainComplexObj X).homology n :=
  (coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover).toHomologyIso n

public theorem coverSmallIntegralSingularHomologyIso_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverSmallIntegralSingularHomologyIso_of_openCover X U hUopen hUcover n).hom =
      HomologicalComplex.homologyMap
        (coverSmallIntegralSingularChainInclusion X U) n := by
  change HomologicalComplex.homologyMap
    (coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom n = _
  rw [coverSmallChainHomotopyEquiv_of_openCover_hom]

end AlgebraicTopology.Singular
