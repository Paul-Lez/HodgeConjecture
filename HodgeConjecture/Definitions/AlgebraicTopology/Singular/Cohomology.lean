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
public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation -- shake: keep

public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits -- shake: keep
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Category.TopPair

/-!
# Singular cohomology over a commutative ring

For a topological space `X` and a commutative ring `R`, singular cochains are the
`R`-linear duals of singular chains. Their coboundary is precomposition with the singular
boundary, and their cohomology is singular cohomology with coefficients in `R`.

For a pair `(X,A)`, relative cochains are the linear duals of `C_*(X;R)/C_*(A;R)`.
Taking `A = X \ Z` defines singular cohomology with support in `Z`. Maps of pairs induce
pullback maps on these cochain complexes and their cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

/-- Let `R` be a commutative ring. This is the category of chain complexes of `R`-modules in
nonnegative degrees, with differentials lowering degree by one and morphisms given by chain
maps. -/
abbrev ChainCategory (R : Type u) [CommRing R] :=
  ChainComplex (ModuleCat.{u} R) ℕ

/-- Let `R` be a commutative ring and `X` a topological space. The singular chain complex `C_*(X;
R)` has the free `R`-module on continuous maps from the standard `n`-simplex to `X` in degree
`n`. The boundary is the alternating sum of restrictions to faces. -/
abbrev SingularChainComplex (R : Type u) [CommRing R] (X : TopCat.{u}) : ChainCategory R :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X

/-- `C_[n](X; R)` is the module of singular `n`-chains of `X` with coefficients in `R`. -/
scoped notation:max "C_[" n "]" "(" Y "; " R ")" =>
  HomologicalComplex.X (SingularChainComplex R Y) n

/-- Let `R` be a commutative ring and `X` a topological space. Singular homology `H_n(X; R)` is the
module of degree-`n` cycles modulo boundaries in the singular chain complex, whose chains are
finite `R`-linear combinations of continuous simplices in `X`. -/
abbrev Homology (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X

/-- `H_[n](X; R)` is singular homology of `X` in degree `n` with coefficients in `R`. -/
scoped notation:max "H_[" n "]" "(" Y "; " R ")" => Homology R Y n

/-- Let `R` be a commutative ring and `f : X → Y` a continuous map. This linear map `H_n(X; R) →
H_n(Y; R)` on singular homology sends the class of a cycle to the class obtained by composing
each of its singular simplices with `f`. -/
def homologyMap (R : Type u) [CommRing R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    H_[n](X; R) →ₗ[R] H_[n](Y; R) :=
  (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map f).hom

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
functor assigns the chain map `C_*(A; R) → C_*(X; R)` induced by the embedding. A map of pairs
gives the corresponding commuting square of singular chain maps. -/
def chainPairFunctor (R : Type u) [CommRing R] :
    TopPair.{u} ⥤ Arrow (ChainCategory R) where
  __ := MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤ ⋙
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapArrow

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. The
relative singular chain complex is `C_*(X, A; R) = C_*(X; R)/C_*(A; R)`, with the differential
induced by the singular boundary. This functor sends maps of pairs to the induced maps on these
quotient complexes. -/
def relativeChainFunctor (R : Type u) [CommRing R] :
    TopPair.{u} ⥤ ChainCategory R :=
  chainPairFunctor R ⋙ Limits.coker (C := ChainCategory R)

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
functor sends the pair to relative singular homology `H_n(X, A; R)`, cycles modulo boundaries in
`C_*(X; R)/C_*(A; R)`, and sends maps of pairs to their induced homology maps. -/
def relativeHomologyFunctor (R : Type u) [CommRing R] (n : ℕ) :
    TopPair.{u} ⥤ ModuleCat.{u} R :=
  relativeChainFunctor R ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`.
Relative singular homology `H_n(X, A; R)` is the degree-`n` homology of the quotient chain
complex `C_*(X; R)/C_*(A; R)`. -/
abbrev RelativeHomology (R : Type u) [CommRing R] (X : TopPair.{u}) (n : ℕ) :
    ModuleCat.{u} R :=
  (relativeHomologyFunctor R n).obj X

/-- `H_[n](X, A; R)` is relative singular homology of the pair `(X, A)` given by a subset
`A : Set X`, in degree `n` with coefficients in `R`. The pair keeps its comma and the
coefficients follow a semicolon, as in Hatcher. -/
scoped notation3:max "H_[" n "]" "(" Y ", " A "; " R ")" =>
  RelativeHomology R (TopPair.ofSubset (X := Y) A) n

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`.
Relative singular cochains are `C^n(X, A; R) = Hom_R(C_n(X; R)/C_n(A; R), R)`. Equivalently,
they are cochains on `X` vanishing on simplices in `A`. Their coboundary sends `φ` to `φ ∘ ∂`. -/
abbrev RelativeCochainComplex (R : Type u) [CommRing R] (X : TopPair.{u}) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((relativeChainFunctor R).obj X).linearDualCochainComplex

/-- `C^n(X, A; R)` is the module of relative singular `n`-cochains of the pair `(X, A)` given
by a subset `A : Set X`, with coefficients in `R`. -/
scoped notation3:max "C^" n:max "(" Y ", " A "; " R ")" =>
  (RelativeCochainComplex R (TopPair.ofSubset (X := Y) A)).X n

/-- Let `R` be a commutative ring and `f : (X, A) → (Y, B)` a map of topological pairs. This
pullback `C^*(Y, B; R) → C^*(X, A; R)` precomposes a relative cochain with the chain map induced
by `f`. -/
abbrev relativeCochainComplexMap (R : Type u) [CommRing R] {X Y : TopPair.{u}} (f : X ⟶ Y) :
    RelativeCochainComplex R Y ⟶ RelativeCochainComplex R X :=
  HomologicalComplex.linearDualMap ((relativeChainFunctor R).map f)

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`.
Relative singular cohomology `H^n(X, A; R)` is the module of cocycles modulo coboundaries in
`Hom_R(C_*(X; R)/C_*(A; R), R)`. Thus representatives are singular cochains on `X` vanishing on
simplices in `A`. -/
abbrev RelativeCohomology (R : Type u) [CommRing R] (X : TopPair.{u}) (n : ℕ) : ModuleCat.{u} R :=
  (RelativeCochainComplex R X).homology n

/-- `H^n(X, A; R)` is relative singular cohomology of the pair `(X, A)` given by a subset
`A : Set X`, in degree `n` with coefficients in `R`. -/
scoped notation3:max "H^" n:max "(" Y ", " A "; " R ")" =>
  RelativeCohomology R (TopPair.ofSubset (X := Y) A) n

/-- Let `R` be a commutative ring and `f : (X, A) → (Y, B)` a map of topological pairs. This linear
pullback `H^n(Y, B; R) → H^n(X, A; R)` sends a relative cocycle to its composite with the
singular chain map induced by `f`. -/
def relativeCohomologyMap (R : Type u) [CommRing R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeCohomology R Y n →ₗ[R] RelativeCohomology R X n :=
  (HomologicalComplex.homologyMap (relativeCochainComplexMap R f) n).hom

/-- Let `R` be a field and `(X, A)` a topological pair. Evaluation of relative singular cocycles on
relative cycles gives this linear equivalence `H^n(X, A; R) ≃ Hom_R(H_n(X, A; R), R)`. The field
hypothesis makes linear duality exact. -/
def relativeCohomologyEquivDualHomology (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    RelativeCohomology R X n ≃ₗ[R] Module.Dual R (RelativeHomology R X n) :=
  ((relativeChainFunctor R).obj X).linearDualHomologyEquiv n

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
quotient map `C_*(X; R) → C_*(X, A; R)` sends each singular chain to its class modulo chains in
`A`. -/
def relativeChainProjection (R : Type u) [CommRing R] (X : TopPair.{u}) :
    SingularChainComplex R X.fst ⟶ (relativeChainFunctor R).obj X :=
  cokernel.π ((chainPairFunctor R).obj X).hom

end AlgebraicTopology.Singular
