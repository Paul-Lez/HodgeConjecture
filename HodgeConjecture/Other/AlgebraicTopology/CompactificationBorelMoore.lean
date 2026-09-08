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

public import HodgeConjecture.Other.AlgebraicTopology.ChartLocalFundamentalClassGenerator

/-!
# Borel--Moore homology through a compactification

If `U` is the complement of a closed subset `S` in a compact Hausdorff space `X`, then
Borel--Moore homology of `U` is computed by relative singular homology `H_*(X, S)`.  This file
introduces the compactification-relative presentation needed for algebraic cycle components.

The local value of a class in `H_n(X, S)` at a point `x ∈ U` lies in
`H_n(X, X ∖ {x})`.  A Borel--Moore fundamental class is characterized by requiring every one
of these local values to equal the prescribed oriented local class.  This is an equality with a
chosen orientation generator, rather than the scale-independent condition that it span a
one-dimensional vector space.

The definitions themselves do not require compactness or closedness.  Those hypotheses enter
the comparison with locally finite chains and the existence and uniqueness theorem for manifold
fundamental classes.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular

/-- The identity on the compactification, regarded as a map from `(X, Uᶜ)` to
`(X, X ∖ {x})` for `x ∈ U`. -/
def compactificationToPointComplementPair
    {X : Type} [TopologicalSpace X] (U : Set X) (x : X) (hx : x ∈ U) :
    TopPair.ofSubset (X := TopCat.of X) Uᶜ ⟶ pointComplementPair x :=
  TopPair.ofHom (f := 𝟙 (TopCat.of X))
    (TopCat.ofHom ⟨fun y ↦ ⟨y.1, fun hy ↦ y.2 (hy ▸ hx)⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩)
    (by ext y; rfl)

/-- The category of integral singular chain complexes. -/
abbrev IntegralChainCategory := ChainComplex AddCommGrpCat ℕ

/-- A topological pair sent to the induced map of integral singular chain complexes. -/
def integralChainPairFunctor :
    TopPair ⥤ Arrow IntegralChainCategory where
  __ := MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤ ⋙
    ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).mapArrow

/-- The integral relative singular chain complex `C_*(X, A; ℤ)`. -/
def integralRelativeChainFunctor : TopPair ⥤ IntegralChainCategory :=
  integralChainPairFunctor ⋙ Limits.coker (C := IntegralChainCategory)

/-- Integral relative singular homology as a functor on topological pairs. -/
def integralRelativeHomologyFunctor (n : ℕ) : TopPair ⥤ AddCommGrpCat :=
  integralRelativeChainFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- Integral relative singular homology of a topological pair. -/
abbrev IntegralRelativeHomology (X : TopPair) (n : ℕ) : AddCommGrpCat :=
  (integralRelativeHomologyFunctor n).obj X

/-- The map on integral relative homology induced by a map of pairs. -/
def integralRelativeHomologyMap {X Y : TopPair} (n : ℕ) (f : X ⟶ Y) :
    IntegralRelativeHomology X n →+ IntegralRelativeHomology Y n :=
  ((integralRelativeHomologyFunctor n).map f).hom

/-- Integral relative homology of `(X, S)`, used as the compactification presentation of
Borel--Moore homology of `X ∖ S`. -/
abbrev IntegralCompactificationBorelMooreHomology
    {X : Type} [TopologicalSpace X] (S : Set X) (n : ℕ) : AddCommGrpCat :=
  IntegralRelativeHomology (TopPair.ofSubset (X := TopCat.of X) S) n

/-- The local value of an integral compactification-relative Borel--Moore class. -/
def integralCompactificationBorelMooreToLocal
    {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ) (x : X) (hx : x ∈ U) :
    IntegralCompactificationBorelMooreHomology Uᶜ n →+
      IntegralRelativeHomology (pointComplementPair x) n :=
  integralRelativeHomologyMap n (compactificationToPointComplementPair U x hx)

/-- An integral compactification-relative class has the prescribed orientation when every local
value is exactly the selected integral orientation generator. -/
def IsIntegralCompactificationFundamentalClass
    {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → IntegralRelativeHomology (pointComplementPair x) n)
    (c : IntegralCompactificationBorelMooreHomology Uᶜ n) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    integralCompactificationBorelMooreToLocal U n x hx c = orientation x hx

/-- The uniquely normalized integral compactification fundamental class, once existence and
uniqueness have been proved. -/
def integralCompactificationFundamentalClass
    {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → IntegralRelativeHomology (pointComplementPair x) n)
    (h : ∃! c, IsIntegralCompactificationFundamentalClass U n orientation c) :
    IntegralCompactificationBorelMooreHomology Uᶜ n :=
  Classical.choose h.exists

/-- The selected integral class has its defining local normalization. -/
lemma integralCompactificationFundamentalClass_isFundamental
    {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → IntegralRelativeHomology (pointComplementPair x) n)
    (h : ∃! c, IsIntegralCompactificationFundamentalClass U n orientation c) :
    IsIntegralCompactificationFundamentalClass U n orientation
      (integralCompactificationFundamentalClass U n orientation h) :=
  Classical.choose_spec h.exists

/-- Exact local normalization determines the integral compactification fundamental class. -/
lemma eq_integralCompactificationFundamentalClass
    {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → IntegralRelativeHomology (pointComplementPair x) n)
    (h : ∃! c, IsIntegralCompactificationFundamentalClass U n orientation c)
    (c : IntegralCompactificationBorelMooreHomology Uᶜ n)
    (hc : IsIntegralCompactificationFundamentalClass U n orientation c) :
    c = integralCompactificationFundamentalClass U n orientation h :=
  h.unique hc (integralCompactificationFundamentalClass_isFundamental U n orientation h)

/-- Relative singular homology of `(X, S)`, regarded as the compactification presentation of
Borel--Moore homology of `X ∖ S`.  When `X` is compact Hausdorff and `S` is closed, this computes
the usual Borel--Moore homology of the open complement. -/
abbrev CompactificationBorelMooreHomology
    (R : Type) [Field R] {X : Type} [TopologicalSpace X]
    (S : Set X) (n : ℕ) : ModuleCat R :=
  RelativeHomology R (TopPair.ofSubset (X := TopCat.of X) S) n

/-- The local value at `x` of a class represented in the compactification model for
Borel--Moore homology. -/
def compactificationBorelMooreToLocal
    (R : Type) [Field R] {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) (x : X) (hx : x ∈ U) :
    CompactificationBorelMooreHomology R Uᶜ n →ₗ[R]
      RelativeHomology R (pointComplementPair x) n :=
  relativeHomologyMap R n (compactificationToPointComplementPair U x hx)

/-- A compactification-relative Borel--Moore class has the prescribed orientation when all of
its local values are exactly the selected local orientation classes. -/
def IsCompactificationFundamentalClass
    (R : Type) [Field R] {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → RelativeHomology R (pointComplementPair x) n)
    (c : CompactificationBorelMooreHomology R Uᶜ n) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    compactificationBorelMooreToLocal R U n x hx c = orientation x hx

/-- The uniquely oriented compactification-relative fundamental class, once its existence and
uniqueness have been proved.  Unlike choosing an arbitrary generator, the resulting class is
fixed by its exact local normalization. -/
def compactificationFundamentalClass
    (R : Type) [Field R] {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → RelativeHomology R (pointComplementPair x) n)
    (h : ∃! c, IsCompactificationFundamentalClass R U n orientation c) :
    CompactificationBorelMooreHomology R Uᶜ n :=
  Classical.choose h.exists

/-- The selected compactification fundamental class has its defining local normalization. -/
lemma compactificationFundamentalClass_isFundamental
    (R : Type) [Field R] {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → RelativeHomology R (pointComplementPair x) n)
    (h : ∃! c, IsCompactificationFundamentalClass R U n orientation c) :
    IsCompactificationFundamentalClass R U n orientation
      (compactificationFundamentalClass R U n orientation h) :=
  Classical.choose_spec h.exists

/-- A class with the required local normalization equals the selected fundamental class. -/
lemma eq_compactificationFundamentalClass
    (R : Type) [Field R] {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → RelativeHomology R (pointComplementPair x) n)
    (h : ∃! c, IsCompactificationFundamentalClass R U n orientation c)
    (c : CompactificationBorelMooreHomology R Uᶜ n)
    (hc : IsCompactificationFundamentalClass R U n orientation c) :
    c = compactificationFundamentalClass R U n orientation h :=
  h.unique hc (compactificationFundamentalClass_isFundamental R U n orientation h)

@[simp]
lemma compactificationBorelMooreToLocal_fundamentalClass
    (R : Type) [Field R] {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ)
    (orientation : ∀ (x : X), x ∈ U → RelativeHomology R (pointComplementPair x) n)
    (h : ∃! c, IsCompactificationFundamentalClass R U n orientation c)
    (x : X) (hx : x ∈ U) :
    compactificationBorelMooreToLocal R U n x hx
        (compactificationFundamentalClass R U n orientation h) =
      orientation x hx :=
  compactificationFundamentalClass_isFundamental R U n orientation h x hx

end AlgebraicTopology.Singular
