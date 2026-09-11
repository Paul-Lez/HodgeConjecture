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

/-!
# Open inputs of the Borel--Moore layer

Four modules state the Borel--Moore route to the cycle class relative to named hypothesis
structures: `Other.AlgebraicGeometry.SheafBorelMoore`,
`Other.AlgebraicGeometry.BorelMooreCycleClass`,
`Other.AlgebraicGeometry.CycleComponentBorelMoore` and
`Other.AlgebraicGeometry.CycleComponentGlobalFundamentalClass`. Together they hold about 2300
lines; the declarations depending on one of the fifteen structures listed here span about 1400.
Thirteen of the structures stand for mathematics Mathlib currently lacks, so a theorem taking one
as an argument holds conditionally on it. This module lists them in one place and states nothing
itself.

## Maximal codimension is constructed

For a component with `coheight x = V.dimension` the following are inhabited by explicit terms,
built from the one-point calculation in `Other.AlgebraicGeometry.CycleComponentBorelMoore`:
`rationalCycleComponentBorelMooreDataOfCoheightEqDimension`,
`maximalCodimensionLocalThomCapInput`, `maximalCodimensionComplexOrientedComponentClassData` and
`auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension`. At Chow level
`AuxiliaryRationalBorelMooreCycleClassDescent.ofMaximalCodimension` then asks for one more
statement, `MaximalCodimensionPrincipalDivisorClassVanishes`: a principal divisor has zero
componentwise class.

In codimension below the dimension, every structure listed here is open, with two exceptions:
`RationalDualizingComplex` carries no predicate, so it and its extension
`RationalDualizingComplexOrientationInput` are inhabited by trivial terms (issue #100) and stand
for no missing mathematics; the notes on them below say what is missing instead.

## Sheaf-theoretic inputs

In `Other.AlgebraicGeometry.SheafBorelMoore`.

* `RationalDualizingComplex` (line 75) holds a bare cochain complex of analytic additive sheaves
  proposed as `ω_X`, with no predicate on it, so the zero complex inhabits it (issue #100). What
  is missing is the Verdier-duality predicate that gives the word dualizing its meaning.
* `RationalDualizingComplexOrientationInput` (line 85) adds the derived-category isomorphism
  `ω_X ≅ ℚ_X[2d]`, which `ℚ_X[2d]` itself satisfies, so it is inhabited too. What is missing
  is the complex-orientation normalization that pins that isomorphism down to a single choice.
* `DerivedSectionsWithSupportInput` (line 110) holds the functor `RΓ_Z`, its shift compatibility,
  and the equation identifying `RΓ_Z(ℚ_X)` with the mapping-cone support object of this project.
  Constructing it asks for the six-functor local-cohomology formalism.
* `RationalCycleComponentSheafBorelMooreComparisonInputs` (line 249) adds the comparison between
  the compactification-relative singular Borel--Moore model and the ambient sheaf model, the
  costalk evaluation at each smooth analytic point, and the square relating them. Constructing it
  asks for the closed-embedding and costalk comparison theorems.
* `ComplexOrientedRationalCycleComponentSheafBorelMooreData` (line 419) adds the theorem that the
  orientation-induced comparison agrees with the local Thom-cap operation. Constructing it asks
  for the Verdier/Thom compatibility theorem.

## Comparison and descent inputs

In `Other.AlgebraicGeometry.BorelMooreCycleClass`.

* `AuxiliaryRationalCycleComponentBorelMooreComparisonData` (line 75) pairs the Borel--Moore data
  with a rescalable linear equivalence to supported singular cohomology. Its images are auxiliary,
  since that equivalence carries a scale of its own.
* `RationalCycleComponentLocalThomCapInput` (line 154) holds the triad-cap operation against the
  ambient complex orientation and the theorem that local evaluations detect supported classes.
  Constructing it asks for the Thom class of the normal bundle and the purity theorem.
* `ComplexOrientedRationalCycleComponentClassData` (line 218) adds a comparison satisfying the
  Thom-cap square. Constructing it asks for normalized Alexander--Poincaré duality.
* `AuxiliaryRationalBorelMooreCycleClassDescent` (line 669) holds a componentwise family of
  auxiliary comparison data together with vanishing of the class of a principal divisor. The
  second field asks for the Gysin pushforward and the first Chern class of a principal divisor.
* `ComplexOrientedRationalBorelMooreCycleClassConstruction` (line 909) is the same descent input
  with normalized component data in place of auxiliary data.

## Fundamental-class inputs

In `Other.AlgebraicGeometry.CycleComponentBorelMoore` and
`Other.AlgebraicGeometry.CycleComponentGlobalFundamentalClass`.

* `RationalCycleComponentBorelMooreData` (`CycleComponentBorelMoore`, line 278) holds existence
  and uniqueness of a global Borel--Moore class with the constructed complex local orientation.
  Constructing it in general asks for oriented-manifold Borel--Moore homology, or for one of the
  three packages below.
* `RationalCycleComponentGlobalFundamentalClassCore` (`CycleComponentGlobalFundamentalClass`,
  line 138) holds a smooth anchor point, the predecessor of the top degree, and propagation of the
  local orientation from the anchor to every smooth point. The propagation field asks for relative
  Mayer--Vietoris on the smooth locus.
* `RationalCycleComponentGlobalFundamentalClassInputs` (line 159) adds boundary vanishing of the
  anchor's local class and vanishing of top homology of the punctured component.
* `RationalCycleComponentInjectiveBoundaryInputs` (line 177) derives boundary vanishing from
  injectivity of the punctured-space inclusion one degree below the top.
* `RationalCycleComponentBoundedModelInputs` (line 192) derives punctured top-homology vanishing
  from a quasi-isomorphic chain model whose top chain group is zero. Constructing it asks for a
  triangulation or a dimension-bounded cover of the punctured component.

The last three convert into each other and into `RationalCycleComponentBorelMooreData`, so the
roots of that branch are `RationalCycleComponentBoundedModelInputs` and the propagation field of
`RationalCycleComponentGlobalFundamentalClassCore`.
-/
