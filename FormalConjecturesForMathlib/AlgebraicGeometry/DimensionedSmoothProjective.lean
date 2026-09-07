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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexPoints

/-!
# Dimensioned smooth projective complex varieties

The Hodge conjecture is stated for a nonsingular projective variety of a fixed complex
dimension. This structure packages that dimension together with the corresponding relative
smoothness certificate. It avoids leaving the dimension as an unrelated theorem hypothesis.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ComplexPoint

/-- A smooth projective complex variety together with its complex dimension. -/
structure DimensionedSmoothProjectiveComplexVariety where
  /-- The underlying smooth projective complex variety. -/
  toSmoothProjectiveComplexVariety : SmoothProjectiveComplexVariety
  /-- The complex dimension. -/
  dimension : ℕ
  [smoothOfRelativeDimension : SmoothOfRelativeDimension dimension
    toSmoothProjectiveComplexVariety.structureMap]

namespace DimensionedSmoothProjectiveComplexVariety

/-- The relative-dimension certificate stored in a dimensioned variety. -/
instance (V : DimensionedSmoothProjectiveComplexVariety) :
    SmoothOfRelativeDimension V.dimension
      V.toSmoothProjectiveComplexVariety.structureMap :=
  V.smoothOfRelativeDimension

/-- The underlying scheme. -/
abbrev scheme (V : DimensionedSmoothProjectiveComplexVariety) :=
  V.toSmoothProjectiveComplexVariety.scheme

/-- The structure morphism to `Spec ℂ`. -/
abbrev structureMap (V : DimensionedSmoothProjectiveComplexVariety) :=
  V.toSmoothProjectiveComplexVariety.structureMap

/-- The analytic complex-point space. -/
abbrev analyticPoint (V : DimensionedSmoothProjectiveComplexVariety) :=
  V.toSmoothProjectiveComplexVariety.analyticPoint

end DimensionedSmoothProjectiveComplexVariety

end AlgebraicGeometry.ComplexPoint
