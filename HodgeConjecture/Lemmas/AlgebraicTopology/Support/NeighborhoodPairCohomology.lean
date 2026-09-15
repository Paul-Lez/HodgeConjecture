/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.NeighborhoodPair
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-!
# Cohomology of neighborhood-support pairs

Vanishing for neighborhoods disjoint from their support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable {M : Type u} [TopologicalSpace M]

/-- The relative-chain complex is zero when a neighborhood misses the support. -/
theorem neighborhoodSupportRelativeChains_isZero
    (R : Type u) [CommRing R] (V S : Set M) (hV : ∀ x ∈ V, x ∉ S) :
    IsZero ((relativeChainFunctor R).obj (neighborhoodSupportComplementPair V S)) := by
  have hset : {v : V | v.1 ∉ S} = Set.univ := Set.eq_univ_of_forall fun v => hV v.1 v.2
  change IsZero ((relativeChainFunctor R).obj (TopPair.ofSubset (X := TopCat.of V) _))
  rw [hset]
  let P := TopPair.ofSubset (X := TopCat.of V) (Set.univ : Set V)
  have hPi : IsIso P.map :=
    (TopCat.isIso_iff_isHomeomorph P.map).mpr (Homeomorph.Set.univ V).isHomeomorph
  have hchain : IsIso ((chainPairFunctor R).obj P).hom := by
    change IsIso (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map P.map)
    infer_instance
  exact isZero_cokernel_of_epi ((chainPairFunctor R).obj P).hom

/-- Relative cohomology is zero when a neighborhood misses the support. -/
theorem neighborhoodSupportRelativeCohomology_isZero
    (R : Type u) [Field R] (V S : Set M) (hV : ∀ x ∈ V, x ∉ S) (n : ℕ) :
    IsZero (RelativeCohomology R (neighborhoodSupportComplementPair V S) n) :=
  relativeCohomology_isZero R _ n
    ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).map_isZero
      (neighborhoodSupportRelativeChains_isZero R V S hV))

/-- Relative cohomology is a subsingleton when a neighborhood misses the support. -/
theorem neighborhoodSupportRelativeCohomology_subsingleton
    (R : Type u) [Field R] (V S : Set M) (hV : ∀ x ∈ V, x ∉ S) (n : ℕ) :
    Subsingleton (RelativeCohomology R (neighborhoodSupportComplementPair V S) n) := by
  have hh : IsZero (RelativeHomology R (neighborhoodSupportComplementPair V S) n) :=
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).map_isZero
      (neighborhoodSupportRelativeChains_isZero R V S hV)
  exact relativeCohomology_subsingleton R _ n (ModuleCat.subsingleton_of_isZero hh)

end AlgebraicTopology.Singular
