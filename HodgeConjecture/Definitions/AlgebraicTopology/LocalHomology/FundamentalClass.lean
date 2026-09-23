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

This explicit cycle fixes the ordering and sign convention used to normalize local Thom and
fundamental classes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

variable (R : Type) [CommRing R]

/-- Let `𝕜` be a field with a topology and `d` a natural number. This topological pair consists of
`𝕜^d`, with the product topology, and the inclusion of its subspace `𝕜^d \ {0}`. -/
abbrev puncturedPair (𝕜 : Type) [Field 𝕜] [TopologicalSpace 𝕜] (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin d → 𝕜)) ({0}ᶜ : Set (Fin d → 𝕜))

/-- Let `M` be a topological space and `W, S ⊆ M` subsets. This topological pair consists of the
subspace `W` and the inclusion into it of `W \ S`, also with its subspace topology. -/
abbrev neighborhoodSupportComplementPair {M : Type} [TopologicalSpace M] (W S : Set M) :
    TopPair :=
  -- The pair `(W, W \ S)`.
  TopPair.ofSubset (X := TopCat.of W) {w | w.1 ∉ S}

/-- For a natural number `d`, this affine map from the standard `d`-simplex to `ℝ^d` has ordered
vertices `e₀, …, e_{d-1}, (-1, …, -1)`. In barycentric coordinates it sends `t` to the vector
with coordinates `t_j - t_d`. -/
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

/-- For a natural number `d`, this is the singular `d`-simplex of `ℝ^d` given in barycentric
coordinates by `t ↦ (t_j - t_d)_j`. Its ordered vertices are the standard basis vectors followed
by `(-1, …, -1)`. -/
def standardSingularSimplex (d : ℕ) :
    (TopCat.toSSet.obj (puncturedPair ℝ d).fst) _⦋d⦌ :=
  ((puncturedPair ℝ d).fst.toSSetObjEquiv _).symm
    ⟨standardAffineSimplex d, continuous_standardAffineSimplex d⟩

/-- For a natural number `n` and face index `i`, this continuous map from the standard `n`-simplex
to `ℝ^{n+1} \ {0}` is the `i`-th face of the affine simplex with vertices the standard basis
followed by `(-1, …, -1)`. The face avoids the origin because one barycentric coordinate is
zero. -/
def standardFaceMap (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), ({0}ᶜ : Set (Fin (n + 1) → ℝ))) where
  toFun t := ⟨standardAffineSimplex (n + 1) (stdSimplex.map i.succAbove t),
    standardAffineSimplex_ne_zero_of_coord_zero (n + 1) _ i
      (stdSimplex_map_succAbove_self_zero n i t)⟩
  continuous_toFun := by fun_prop

/-- For a natural number `n` and face index `i`, this is the singular `n`-simplex of `ℝ^{n+1} \ {0}`
obtained by omitting vertex `i` from the ordered affine simplex with vertices the standard basis
followed by `(-1, …, -1)`. -/
def standardFaceSimplex (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).snd) _⦋n⦌ :=
  ((puncturedPair ℝ (n + 1)).snd.toSSetObjEquiv _).symm
    (standardFaceMap n i)

/-- Let `R` be a commutative ring and `d` a natural number. This is the quotient singular chain
complex `C_*(ℝ^d; R)/C_*(ℝ^d \ {0}; R)` of the pair consisting of real coordinate space and its
punctured subspace. -/
abbrev standardLocalRelativeChainComplex (d : ℕ) :=
  (relativeChainFunctor R).obj (puncturedPair ℝ d)

/-- Let `R` be a commutative ring and `d` a natural number. This is the quotient map of chain
complexes `C_*(ℝ^d; R) → C_*(ℝ^d, ℝ^d \ {0}; R)`, which sets chains contained in the punctured
space equal to zero. -/
def standardLocalProjection (d : ℕ) :
    ((chainPairFunctor R).obj (puncturedPair ℝ d)).right ⟶
      standardLocalRelativeChainComplex R d :=
  relativeChainProjection R (puncturedPair ℝ d)

/-- Let `R` be a commutative ring and `d` a natural number. The chosen affine simplex in `ℝ^d` has
ordered vertices `e₀, …, e_{d-1}, (-1, …, -1)`, where the `e_j` are standard basis vectors. This
linear map `R → C_d(ℝ^d; R)` sends `r` to `r` times that singular simplex. -/
def standardAmbientSimplexChain (d : ℕ) :
    ModuleCat.of R R ⟶
      ((chainPairFunctor R).obj (puncturedPair ℝ d)).right.X d :=
  (TopCat.toSSet.obj (puncturedPair ℝ d).fst).ιChainComplex
    (standardSingularSimplex d)

/-- Let `R` be a commutative ring and `d` a natural number. The chosen affine simplex in `ℝ^d` has
ordered vertices `e₀, …, e_{d-1}, (-1, …, -1)`, where the `e_j` are standard basis vectors. This
map `R → C_d(ℝ^d, ℝ^d \ {0}; R)` sends `1` to its relative chain class, by quotienting out
chains in the punctured space. -/
def standardLocalChain (d : ℕ) :
    ModuleCat.of R R ⟶ (standardLocalRelativeChainComplex R d).X d :=
  standardAmbientSimplexChain R d ≫ (standardLocalProjection R d).f d

/-- Let `R` be a commutative ring, `n` a natural number, and `i` a face index. This linear map `R →
C_n(ℝ^{n+1}; R)` sends `1` to the `i`-th face of the affine simplex with ordered vertices the
standard basis followed by `(-1, …, -1)`. -/
def standardAmbientFaceChain (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of R R ⟶
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).right.X n :=
  (TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).fst).ιChainComplex
    ((TopCat.toSSet.obj (puncturedPair ℝ (n + 1)).fst).δ i
      (standardSingularSimplex (n + 1)))

/-- Let `R` be a commutative ring, `n` a natural number, and `i` a face index. This map `R →
C_n(ℝ^{n+1} \ {0}; R)` sends `1` to the `i`-th face of the affine simplex with vertices the
standard basis followed by `(-1, …, -1)`. Every such face avoids the origin. -/
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

/-- Let `R` be a commutative ring and `d` a natural number. The chosen affine simplex in `ℝ^d` has
ordered vertices `e₀, …, e_{d-1}, (-1, …, -1)`, where the `e_j` are standard basis vectors. Its
boundary lies in `ℝ^d \ {0}`, so it defines a relative cycle. This map from `R` to relative
cycles sends `1` to that cycle. -/
def standardLocalCycle (d : ℕ) :
    ModuleCat.of R R ⟶ (standardLocalRelativeChainComplex R d).cycles d :=
  (standardLocalRelativeChainComplex R d).liftCycles (standardLocalChain R d)
    ((ComplexShape.down ℕ).next d) rfl (standardLocalChain_boundary R d)

/-- Let `R` be a commutative ring and `d` a natural number. The chosen affine simplex in `ℝ^d` has
ordered vertices `e₀, …, e_{d-1}, (-1, …, -1)`, where the `e_j` are standard basis vectors. This
is its class in `H_d(ℝ^d, ℝ^d \ {0}; R)`, with coefficient `1`. Its boundary vanishes in
relative chains because all faces avoid the origin. -/
def standardLocalClass (d : ℕ) : RelativeHomology R (puncturedPair ℝ d) d :=
  ((standardLocalCycle R d ≫ (standardLocalRelativeChainComplex R d).homologyπ d).hom) 1

end AlgebraicTopology.Singular
