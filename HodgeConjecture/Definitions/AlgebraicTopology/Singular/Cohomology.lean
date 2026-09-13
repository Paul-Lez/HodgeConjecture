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
# Singular cohomology over a field

This file constructs field-valued singular cohomology from Mathlib's singular chain complex.

**Cohomology is defined by dualising the chain complex, not by dualising homology.** The singular
cochain complex `C^*(X; R)` is the degreewise `R`-linear dual of the singular chain complex
`C_*(X; R)`, and `Cohomology R X n` is the degree-`n` homology of that cochain complex, exactly as
Mathlib defines the homology of any `HomologicalComplex`. Pullback in cohomology is the map on
homology induced by the dualised chain map; the definition never mentions singular homology.

Dualising homology instead would be wrong in general: over a ring it silently discards the `Ext`
term of the universal coefficient theorem, and even over a field it produces an object with no
cochain-level representative, so cochain-level constructions — cup products, mapping cones of
restriction, comparisons with sheaf cohomology — cannot be expressed against it. The coefficients
are a field throughout this development, and there the universal coefficient theorem does identify
the two; that identification is recorded as `cohomologyEquivDualHomology` (and
`relativeCohomologyEquivDualHomology`) rather than being taken as the definition, so every
statement that pairs a cohomology class with a homology class goes through it explicitly.

For a topological pair `A ⊆ X`, the relative chain complex is the cokernel of the actual chain map
`C_*(A) ⟶ C_*(X)`; the relative cochain complex is its dual, and relative cohomology is again the
homology of that complex. Cohomology with support and the map that forgets support are derived
from this construction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

/-- The category containing field-valued singular chain complexes. -/
abbrev ChainCategory (R : Type u) [Field R] :=
  ChainComplex (ModuleCat.{u} R) ℕ

/-- The ordinary singular chain complex of `X` with coefficients in `R`. -/
abbrev SingularChainComplex (R : Type u) [Field R] (X : TopCat.{u}) : ChainCategory R :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X

/-- Singular homology of a topological space with coefficients in a field. -/
abbrev Homology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X

/-- The map on singular homology induced by a continuous map. -/
def homologyMap (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    Homology R X n →ₗ[R] Homology R Y n :=
  (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map f).hom

/-- A topological pair `A ⊆ X`, sent to the induced arrow `C_*(A) ⟶ C_*(X)` of singular
chain complexes. -/
def chainPairFunctor (R : Type u) [Field R] :
    TopPair.{u} ⥤ Arrow (ChainCategory R) where
  __ := MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤ ⋙
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapArrow

/-- The relative singular chain complex `C_*(X, A)`, defined as the cokernel of
`C_*(A) ⟶ C_*(X)`. -/
def relativeChainFunctor (R : Type u) [Field R] :
    TopPair.{u} ⥤ ChainCategory R :=
  chainPairFunctor R ⋙ Limits.coker (C := ChainCategory R)

/-- Relative singular homology. -/
def relativeHomologyFunctor (R : Type u) [Field R] (n : ℕ) :
    TopPair.{u} ⥤ ModuleCat.{u} R :=
  relativeChainFunctor R ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- Relative singular homology of the pair `A ⊆ X`. -/
abbrev RelativeHomology (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    ModuleCat.{u} R :=
  (relativeHomologyFunctor R n).obj X

/-- The relative singular cochain complex `C^*(X, A)`, the degreewise `R`-linear dual of the
relative singular chain complex. -/
abbrev RelativeCochainComplex (R : Type u) [Field R] (X : TopPair.{u}) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((relativeChainFunctor R).obj X).linearDualCochainComplex

/-- The relative singular cochain map induced by a map of pairs, obtained by dualising the
relative chain map. -/
abbrev relativeCochainComplexMap (R : Type u) [Field R] {X Y : TopPair.{u}} (f : X ⟶ Y) :
    RelativeCochainComplex R Y ⟶ RelativeCochainComplex R X :=
  HomologicalComplex.linearDualMap ((relativeChainFunctor R).map f)

/-- Relative singular cohomology over a field, defined as the homology of the relative singular
cochain complex — again by dualising the chain complex, not by dualising homology. -/
abbrev RelativeCohomology (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) : ModuleCat.{u} R :=
  (RelativeCochainComplex R X).homology n

/-- Pullback in relative singular cohomology, induced by the dualised relative chain map. -/
def relativeCohomologyMap (R : Type u) [Field R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeCohomology R Y n →ₗ[R] RelativeCohomology R X n :=
  (HomologicalComplex.homologyMap (relativeCochainComplexMap R f) n).hom

/-- Universal coefficients over a field for a pair: relative singular cohomology is canonically
the linear dual of relative singular homology. -/
def relativeCohomologyEquivDualHomology (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    RelativeCohomology R X n ≃ₗ[R] Module.Dual R (RelativeHomology R X n) :=
  ((relativeChainFunctor R).obj X).linearDualHomologyEquiv n

/-- The quotient map from absolute singular chains of `X` to relative chains of `(X, A)`. -/
def relativeChainProjection (R : Type u) [Field R] (X : TopPair.{u}) :
    SingularChainComplex R X.fst ⟶ (relativeChainFunctor R).obj X :=
  cokernel.π ((chainPairFunctor R).obj X).hom

end AlgebraicTopology.Singular
