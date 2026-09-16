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

/-!
# A standard local fundamental cycle

This file constructs a canonical relative singular cycle in
`H_d(ℝ^d, ℝ^d ∖ {0}; R)`. The affine simplex has vertices the standard basis and
`(-1, ..., -1)`. Its barycenter is the unique point that maps to the origin, while each face
misses the origin. Its relative boundary therefore vanishes.

This explicit cycle fixes the ordering and sign convention needed to normalize local Thom and
fundamental classes without adding an orientation as arbitrary data.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

variable (R : Type) [CommRing R]

/-- The pair `(𝕜^d, 𝕜^d \ {0})` for a topological field `𝕜`. -/
abbrev puncturedPair (𝕜 : Type) [Field 𝕜] [TopologicalSpace 𝕜] (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin d → 𝕜)) ({0}ᶜ : Set (Fin d → 𝕜))

/-- The affine `d`-simplex with vertices the standard basis and the vector `(-1, ..., -1)`. -/
def standardAffineSimplex (d : ℕ) (t : stdSimplex ℝ (Fin (d + 1))) : Fin d → ℝ :=
  fun j => t (Fin.castSucc j) - t (Fin.last d)

-- Mathlib proves this but does not tag it, so `fun_prop` cannot see through `stdSimplex.map`.
attribute [fun_prop] stdSimplex.continuous_map

@[fun_prop]
lemma continuous_standardAffineSimplex (d : ℕ) : Continuous (standardAffineSimplex d) :=
  continuous_pi fun j =>
    ((continuous_apply (Fin.castSucc j)).comp continuous_subtype_val).sub
      ((continuous_apply (Fin.last d)).comp continuous_subtype_val)

lemma stdSimplex_map_succAbove_self_zero (n : ℕ) (i : Fin (n + 2))
    (t : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplex.map i.succAbove t i = 0 := by simp [FunOnFinite.linearMap_apply_apply]

lemma standardAffineSimplex_ne_zero_of_coord_zero (d : ℕ)
    (t : stdSimplex ℝ (Fin (d + 1))) (i : Fin (d + 1)) (hi : t i = 0) :
    standardAffineSimplex d t ≠ 0 := by
  intro h
  have hcoord (j : Fin d) : t (Fin.castSucc j) = t (Fin.last d) := by
    have hj := congr_fun h j
    simpa [standardAffineSimplex] using sub_eq_zero.mp hj
  have hlast : t (Fin.last d) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact (hcoord j).symm.trans hi
    · exact hi
  have hall (j : Fin (d + 1)) : t j = 0 := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · exact (hcoord k).trans hlast
    · exact hlast
  have hzero : ∑ j, (t : Fin (d + 1) → ℝ) j = 0 :=
    Finset.sum_eq_zero fun j _ => hall j
  exact zero_ne_one (hzero.symm.trans t.2.2)

/-- The affine simplex as a singular simplex of real coordinate space. -/
def standardSingularSimplex (d : ℕ) :
    (TopCat.toSSet.obj (puncturedPair ℝ d).fst) _⦋d⦌ :=
  ((puncturedPair ℝ d).fst.toSSetObjEquiv _).symm
    ⟨standardAffineSimplex d, continuous_standardAffineSimplex d⟩

/-- A face of the positive-dimensional standard simplex, lifted to the punctured space. -/
def standardFaceMap (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), ({0}ᶜ : Set (Fin (n + 1) → ℝ))) where
  toFun t := ⟨standardAffineSimplex (n + 1) (stdSimplex.map i.succAbove t),
    standardAffineSimplex_ne_zero_of_coord_zero (n + 1) _ i
      (stdSimplex_map_succAbove_self_zero n i t)⟩
  continuous_toFun := by fun_prop

/-- A face of the positive-dimensional standard simplex as a singular simplex of the
punctured space. -/
def standardFaceSimplex (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).snd) _⦋n⦌ :=
  ((puncturedPair ℝ (n + 1)).snd.toSSetObjEquiv _).symm
    (standardFaceMap n i)

/-- The relative singular chain complex of the standard punctured real coordinate space. -/
abbrev standardLocalRelativeChainComplex (d : ℕ) :=
  (relativeChainFunctor R).obj (puncturedPair ℝ d)

/-- The projection to the standard relative chain complex, in the arrow form that
`chainPairFunctor` produces. -/
def standardLocalProjection (d : ℕ) :
    ((chainPairFunctor R).obj (puncturedPair ℝ d)).right ⟶
      standardLocalRelativeChainComplex R d :=
  relativeChainProjection R (puncturedPair ℝ d)

/-- The standard affine simplex as an absolute singular chain. -/
def standardAmbientSimplexChain (d : ℕ) :
    ModuleCat.of R R ⟶
      ((chainPairFunctor R).obj (puncturedPair ℝ d)).right.X d :=
  (TopCat.toSSet.obj (puncturedPair ℝ d).fst).ιChainComplex
    (standardSingularSimplex d)

/-- The standard affine simplex, projected to the relative singular chain complex of
`(ℝ^d, ℝ^d ∖ {0})`. -/
def standardLocalChain (d : ℕ) :
    ModuleCat.of R R ⟶ (standardLocalRelativeChainComplex R d).X d :=
  standardAmbientSimplexChain R d ≫ (standardLocalProjection R d).f d

/-- A face of the standard simplex as an absolute singular chain. -/
def standardAmbientFaceChain (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of R R ⟶
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).right.X n :=
  (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).fst).ιChainComplex
    ((TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).fst).δ i
      (standardSingularSimplex (n + 1)))

/-- A face of the standard simplex as a chain in the punctured subspace. -/
def standardSubspaceFaceChain (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of R R ⟶
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).left.X n :=
  (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).snd).ιChainComplex
    (standardFaceSimplex n i)

lemma standardFaceChain_inclusion (n : ℕ) (i : Fin (n + 2)) :
    standardSubspaceFaceChain R n i ≫
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).hom.f n =
    standardAmbientFaceChain R n i := by
  change (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).snd).ιChainComplex
      (standardFaceSimplex n i) ≫
    (SSet.chainComplexMap
      (TopCat.toSSet.map (puncturedPair ℝ (n + 1)).map)
      (ModuleCat.of R R)).f n = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

lemma standardAmbientSimplexChain_boundary (n : ℕ) :
    standardAmbientSimplexChain R (n + 1) ≫
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).right.d (n + 1) n =
    ∑ i : Fin (n + 2), (-1) ^ i.val • standardAmbientFaceChain R n i :=
  SSet.ιChainComplex_d
    (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).fst)
    (ModuleCat.of R R) (standardSingularSimplex (n + 1))

lemma standardAmbientFaceChain_projection (n : ℕ) (i : Fin (n + 2)) :
    standardAmbientFaceChain R n i ≫ (standardLocalProjection R (n + 1)).f n = 0 := by
  rw [← standardFaceChain_inclusion, Category.assoc, ← HomologicalComplex.comp_f,
    standardLocalProjection, subspaceChainMap_relativeChainProjection,
    HomologicalComplex.zero_f, comp_zero]

lemma standardLocalChain_boundary_succ (n : ℕ) :
    standardLocalChain R (n + 1) ≫
      (standardLocalRelativeChainComplex R (n + 1)).d (n + 1) n = 0 := by
  rw [standardLocalChain, Category.assoc, (standardLocalProjection R (n + 1)).comm (n + 1) n,
    ← Category.assoc, standardAmbientSimplexChain_boundary, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Preadditive.zsmul_comp, standardAmbientFaceChain_projection, smul_zero]

lemma standardLocalChain_boundary (d : ℕ) :
    standardLocalChain R d ≫
      (standardLocalRelativeChainComplex R d).d d ((ComplexShape.down ℕ).next d) = 0 := by
  cases d with
  | zero => simp
  | succ n => rw [ChainComplex.next_nat_succ]; exact standardLocalChain_boundary_succ R n

/-- The standard relative cycle represented by an affine simplex meeting the origin once. -/
def standardLocalCycle (d : ℕ) :
    ModuleCat.of R R ⟶ (standardLocalRelativeChainComplex R d).cycles d :=
  (standardLocalRelativeChainComplex R d).liftCycles (standardLocalChain R d)
    ((ComplexShape.down ℕ).next d) rfl (standardLocalChain_boundary R d)

/-- The canonical class represented by the standard affine local cycle in
`H_d(ℝ^d, ℝ^d ∖ {0}; R)`. -/
def standardLocalClass (d : ℕ) : RelativeHomology R (puncturedPair ℝ d) d :=
  ((standardLocalCycle R d ≫ (standardLocalRelativeChainComplex R d).homologyπ d).hom) 1

end AlgebraicTopology.Singular
