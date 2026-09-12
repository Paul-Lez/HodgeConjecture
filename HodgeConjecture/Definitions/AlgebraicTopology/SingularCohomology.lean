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

public import HodgeConjecture.Mathlib.Algebra.Category.ModuleCat.Basic -- shake: keep
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

/-- The singular chain map induced by a continuous map. -/
abbrev singularChainComplexMap (R : Type u) [Field R] {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SingularChainComplex R X ⟶ SingularChainComplex R Y :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map f

/-- Singular homology of a topological space with coefficients in a field. -/
abbrev Homology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X

/-- The singular cochain complex `C^*(X; R)`, the degreewise `R`-linear dual of the singular
chain complex. -/
abbrev SingularCochainComplex (R : Type u) [Field R] (X : TopCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (SingularChainComplex R X).linearDualCochainComplex

/-- The singular cochain map induced by a continuous map, obtained by dualising the chain map. -/
abbrev singularCochainComplexMap (R : Type u) [Field R] {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SingularCochainComplex R Y ⟶ SingularCochainComplex R X :=
  HomologicalComplex.linearDualMap (singularChainComplexMap R f)

/-- Singular cohomology with coefficients in a field, defined as the homology of the singular
cochain complex — that is, by dualising the chain complex, not by dualising homology. -/
abbrev Cohomology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  (SingularCochainComplex R X).homology n

/-- The map on singular homology induced by a continuous map. -/
def homologyMap (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    Homology R X n →ₗ[R] Homology R Y n :=
  (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map f).hom

/-- Pullback in singular cohomology, induced by the dualised chain map. -/
def cohomologyMap (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    Cohomology R Y n →ₗ[R] Cohomology R X n :=
  (HomologicalComplex.homologyMap (singularCochainComplexMap R f) n).hom

/-- Universal coefficients over a field: singular cohomology, defined by dualising the chain
complex, is canonically the linear dual of singular homology. This is a theorem here, not the
definition of cohomology. -/
def cohomologyEquivDualHomology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :
    Cohomology R X n ≃ₗ[R] Module.Dual R (Homology R X n) :=
  (SingularChainComplex R X).linearDualHomologyEquiv n

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

/-- The map on relative homology induced by a map of pairs. -/
def relativeHomologyMap (R : Type u) [Field R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeHomology R X n →ₗ[R] RelativeHomology R Y n :=
  ((relativeHomologyFunctor R n).map f).hom

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

/-- The quotient map from absolute homology to relative homology. -/
def relativeHomologyProjection (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    Homology R X.fst n ⟶ RelativeHomology R X n :=
  HomologicalComplex.homologyMap (relativeChainProjection R X) n

/-- The canonical map from relative cohomology to absolute cohomology, induced by the dual of
the projection from absolute chains to relative chains. -/
def relativeCohomologyToAbsolute (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    RelativeCohomology R X n →ₗ[R] Cohomology R X.fst n :=
  (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (relativeChainProjection R X)) n).hom

/-- Singular cohomology of `X` with support in `Z`, defined as `H^n(X, X ∖ Z)`. -/
abbrev CohomologyWithSupport (R : Type u) [Field R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) : ModuleCat.{u} R :=
  RelativeCohomology R (TopPair.ofSubset Zᶜ) n

/-- Forget support in `Z`, mapping a supported class to ordinary singular cohomology. -/
def forgetSupport (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] Cohomology R X n :=
  relativeCohomologyToAbsolute R (TopPair.ofSubset Zᶜ) n

/-- A continuous map, regarded as a map of pairs for a closed support and its preimage. -/
def preimageSupportPairMap {X Y : TopCat.{u}} (f : X ⟶ Y) (Z : Set Y) :
    TopPair.ofSubset (f ⁻¹' Z)ᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom f
    (TopCat.ofHom ⟨fun x => ⟨f x.1, x.2⟩,
      Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) _⟩)
    (by ext x; rfl)

/-- Pull back a supported cohomology class. Its support pulls back along the continuous map. -/
def cohomologyWithSupportMap (R : Type u) [Field R] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y) (Z : Set Y) :
    CohomologyWithSupport R Y Z n →ₗ[R]
      CohomologyWithSupport R X (f ⁻¹' Z) n :=
  relativeCohomologyMap R n (preimageSupportPairMap f Z)

/-- The identity map as a map of pairs for an inclusion of supports `Z ⊆ W`. -/
def supportInclusionPairMap (X : TopCat.{u}) {Z W : Set X} (h : Z ⊆ W) :
    TopPair.ofSubset Wᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom (𝟙 X)
    (TopCat.ofHom ⟨fun x => ⟨x.1, fun hx => x.2 (h hx)⟩, by fun_prop⟩)
    (by ext x; rfl)

/-- Enlarge the allowed support of a supported cohomology class. -/
def enlargeSupport (R : Type u) [Field R] (X : TopCat.{u}) {Z W : Set X}
    (h : Z ⊆ W) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] CohomologyWithSupport R X W n :=
  relativeCohomologyMap R n (supportInclusionPairMap X h)

end AlgebraicTopology.Singular
