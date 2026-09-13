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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Relative (co)homology of the empty subspace

The singular chain complex of the empty space is zero.  Consequently, the canonical projection
from absolute chains to the relative chains of `(X, ∅)` is an isomorphism.  This file records the
resulting canonical identifications

`Hₙ(X; R) ≅ Hₙ(X, ∅; R)` and `Hⁿ(X, X ∖ X; R) ≅ Hⁿ(X; R)`.

The second isomorphism is exactly the existing map which forgets support in all of `X`.  These
identifications are useful when Borel--Moore homology of a compact space is presented using the
space itself as a compactification, with empty boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The pair `(X, ∅)`. -/
abbrev emptySubspacePair : TopPair.{u} :=
  TopPair.ofSubset (X := X) (∅ : Set X)

/-- The empty subspace has no singular simplices. -/
lemma isEmpty_emptySubspacePair_simplices (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (emptySubspacePair X).snd).obj
      (Opposite.op (SimplexCategory.mk n))) := by
  constructor
  intro σ
  let f := ((emptySubspacePair X).snd.toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))) σ
  exact (f stdSimplex.barycenter).2

/-- The chain map induced by the inclusion `∅ ⊆ X` is zero. -/
lemma emptySubspacePair_chainMap_eq_zero :
    ((chainPairFunctor R).obj (emptySubspacePair X)).hom = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap
    (TopCat.toSSet.map (emptySubspacePair X).map)
    (ModuleCat.of R R)).f n = 0
  apply SSet.chainComplex_hom_ext
  intro σ
  exact (isEmpty_emptySubspacePair_simplices X n).false σ |>.elim

/-- The quotient from absolute chains to the relative chains of `(X, ∅)` is an isomorphism. -/
noncomputable instance relativeChainProjection_empty_isIso :
    IsIso (relativeChainProjection R (emptySubspacePair X)) :=
  cokernel.π_of_zero (emptySubspacePair_chainMap_eq_zero R X)

/-- The canonical isomorphism from absolute homology to relative homology for `(X, ∅)`. -/
def homologyEmptySubspaceIso (n : ℕ) :
    Homology R X n ≅ RelativeHomology R (emptySubspacePair X) n :=
  HomologicalComplex.homologyMapIso
    (asIso (relativeChainProjection R (emptySubspacePair X))) n

@[simp]
lemma homologyEmptySubspaceIso_hom (n : ℕ) :
    (homologyEmptySubspaceIso R X n).hom = relativeHomologyProjection R (emptySubspacePair X) n :=
  rfl

/-- Cohomology supported on all of `X` is canonically ordinary cohomology.  On cochains the
forget-support map is the dual of the relative chain projection, which is an isomorphism here, so
this is an isomorphism of cochain complexes before passing to cohomology. -/
def wholeSupportCohomologyLinearEquiv (n : ℕ) :
    CohomologyWithSupport R X Set.univ n ≃ₗ[R] Cohomology R X n :=
  LinearEquiv.ofBijective (forgetSupport R X Set.univ n) <| by
    let P : TopPair.{u} := TopPair.ofSubset ((Set.univ : Set X)ᶜ)
    let : IsIso (relativeChainProjection R P) := by
      change IsIso (relativeChainProjection R
        (TopPair.ofSubset ((Set.univ : Set X)ᶜ)))
      rw [Set.compl_univ]
      infer_instance
    let e := HomologicalComplex.homologyMapIso
      (HomologicalComplex.linearDualIso (asIso (relativeChainProjection R P))) n
    exact (ConcreteCategory.isIso_iff_bijective e.hom).mp e.isIso_hom

@[simp]
lemma wholeSupportCohomologyLinearEquiv_apply (n : ℕ)
    (α : CohomologyWithSupport R X Set.univ n) (z : Homology R X n) :
    cohomologyEquivDualHomology R X n (wholeSupportCohomologyLinearEquiv R X n α) z =
      relativeCohomologyEquivDualHomology R (TopPair.ofSubset ((Set.univ : Set X)ᶜ)) n α
        ((relativeHomologyProjection R
          (TopPair.ofSubset ((Set.univ : Set X)ᶜ)) n).hom z) :=
  cohomologyEquivDualHomology_forgetSupport R X Set.univ n α z

/-- The canonical whole-support equivalence has the existing forget-support map as its underlying
linear map. -/
lemma wholeSupportCohomologyLinearEquiv_toLinearMap (n : ℕ) :
    (wholeSupportCohomologyLinearEquiv R X n).toLinearMap =
      forgetSupport R X Set.univ n :=
  rfl

end AlgebraicTopology.Singular
