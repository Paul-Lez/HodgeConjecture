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
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# The relative singular-chain sheaf complex

This file constructs the presheaf of relative singular chain complexes
`U ↦ C_*(X, X ∖ U; R)`. For `V ⊆ U`, restriction is the relative chain map induced by
the identity map of `X` and the inclusion `X ∖ U ⊆ X ∖ V`. Degreewise sheafification gives a
complex of additive sheaves, then the grading embedding `n ↦ -n` gives a cochain complex
indexed by the integers.

The conceptual model is the sheafification of relative singular chains described in
Baumann--Kamnitzer--Knutson, *The Mirković--Vilonen basis and Duistermaat--Heckman measures*,
§5.1, p. 24, <https://irma.math.unistra.fr/~baumann/mvbasis.pdf>. No external code is copied.
The sheafification implementation follows the existing `Singular.Sheaf.Cochain` module.

This is a concrete candidate for the dualizing complex. Its dualizing property, the
identification with exceptional pullback, the orientation quasi-isomorphism, stalkwise local
homology, and the identification of its hypercohomology with intrinsic Borel--Moore homology are
all separate tasks.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- The contravariant functor sending an open set `U` to the pair `(X, X ∖ U)`. -/
def openComplementPairFunctor : (Opens X)ᵒᵖ ⥤ TopPair.{u} where
  obj U := TopPair.ofSubset (U.unop : Set X)ᶜ
  map i := supportInclusionPairMap X (leOfHom i.unop)
  map_id U := supportInclusionPairMap_rfl X (U.unop : Set X)
  map_comp i j :=
    supportInclusionPairMap_trans X (leOfHom j.unop) (leOfHom i.unop)

/-- Let `X` be a topological space and `R` a commutative ring. This functor sends an open `U ⊆ X` to
the relative singular chain complex `C_*(X,X \ U;R) = C_*(X;R)/C_*(X \ U;R)`. For `V ⊆ U`,
restriction is the quotient map induced by `X \ U ⊆ X \ V`. -/
def openRelativeSingularChainComplexFunctor :
    (Opens X)ᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  openComplementPairFunctor X ⋙ relativeChainFunctor R

/-- Relative chains of `(X, X ∖ U)` in degree `n`, forgetting only the scalar structure. -/
def singularChainPresheaf (n : ℕ) : TopCat.Presheaf AddCommGrpCat.{u} X :=
  openRelativeSingularChainComplexFunctor R X ⋙
    HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- The restriction map is induced by the inclusion of complements. -/
@[simp] lemma singularChainPresheaf_map {U V : Opens X} (i : V ⟶ U) (n : ℕ) :
    (singularChainPresheaf R X n).map i.op =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map
          (supportInclusionPairMap X (leOfHom i))).f n) :=
  rfl

/-- The singular boundary in the relative-chain presheaves. -/
def singularChainBoundary (n : ℕ) :
    singularChainPresheaf R X (n + 1) ⟶ singularChainPresheaf R X n where
  app U := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    (((openRelativeSingularChainComplexFunctor R X).obj U).d (n + 1) n)
  naturality {U V} i := by
    exact congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
      (((openRelativeSingularChainComplexFunctor R X).map i).comm (n + 1) n)

/-- Consecutive relative singular boundaries compose to zero. -/
lemma singularChainBoundary_comp (n : ℕ) :
    singularChainBoundary R X (n + 1) ≫ singularChainBoundary R X n = 0 :=
  NatTrans.ext (funext fun U ↦ congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
    (((openRelativeSingularChainComplexFunctor R X).obj U).d_comp_d (n + 2) (n + 1) n))

/-- The relative singular-chain complex as a complex of additive presheaves. -/
def singularChainPresheafComplex : ChainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ :=
  ChainComplex.of (singularChainPresheaf R X) (singularChainBoundary R X)
    (singularChainBoundary_comp R X)

@[simp] lemma singularChainPresheafComplex_d (n : ℕ) :
    (singularChainPresheafComplex R X).d (n + 1) n = singularChainBoundary R X n := by
  simp [singularChainPresheafComplex]

/-- The sheaf of relative singular chains in degree `n`. -/
def singularChainSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (singularChainPresheaf R X n)

/-- The sheafified relative singular boundary. -/
def singularChainSheafBoundary (n : ℕ) :
    singularChainSheaf R X (n + 1) ⟶ singularChainSheaf R X n :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (singularChainBoundary R X n)

/-- Let `X` be a topological space and `R` a commutative ring. This chain complex of sheaves of
abelian groups is obtained by sheafifying, in each nonnegative degree, the presheaf `U ↦ C_*(X,X
\ U;R)`. Its boundary is induced by the alternating sum of the faces of a singular simplex. -/
def singularChainSheafComplex : ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R X)

@[simp] lemma singularChainSheafComplex_d (n : ℕ) :
    (singularChainSheafComplex R X).d (n + 1) n = singularChainSheafBoundary R X n := by
  change (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    ((singularChainPresheafComplex R X).d (n + 1) n) = _
  rw [singularChainPresheafComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be a topological space and `R` a commutative ring. This chain map sends the presheaf
complex `U ↦ C_*(X,X \ U;R)` to the underlying presheaf complex of its degreewise
sheafification. In each degree it takes a relative chain to the section represented by that
chain locally. -/
def singularChainSheafificationUnit :
    singularChainPresheafComplex R X ⟶
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X) where
  f n := toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, singularChainPresheafComplex_d,
      singularChainSheafComplex_d]
    dsimp [singularChainSheafBoundary, singularChainSheaf]
    exact (toSheafify_naturality (Opens.grothendieckTopology X)
      (singularChainBoundary R X j)).symm

/-- Sheafification does not change the stalk of the relative-chain presheaf in any degree. -/
instance singularChainSheafificationUnit_stalk_isIso (x : X) (n : ℕ) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((singularChainSheafificationUnit R X).f n)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (singularChainPresheaf R X n)

/-- The sheafified relative singular-chain model with the cohomological grading convention:
homological degree `n` occupies cohomological degree `-n`, and positive degrees are zero. -/
def singularChainSheafCochainComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ :=
  (singularChainSheafComplex R X).extend ComplexShape.embeddingDownNat

/-- The integer-graded chain sheaf has no terms in positive degrees. -/
instance singularChainSheafCochainComplex_isStrictlyLE :
    (singularChainSheafCochainComplex R X).IsStrictlyLE 0 := by
  unfold singularChainSheafCochainComplex
  infer_instance

end AlgebraicTopology.Singular
