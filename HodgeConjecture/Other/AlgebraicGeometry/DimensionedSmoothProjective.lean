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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Points

/-!
# Dimensioned smooth projective complex varieties

This auxiliary wrapper packages a nonsingular projective complex variety with a chosen relative
dimension. It belongs in `Other`: the Hodge-conjecture statement itself uses the unbundled scheme,
structure morphism, and typeclass hypotheses from `Points`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

/-- An auxiliary bundled nonsingular projective complex variety.

The statement-facing API remains unbundled; this wrapper is used only by the Borel--Moore
construction, where carrying the same scheme and structure morphism through many comparison
objects is convenient. -/
structure SmoothProjectiveComplexVariety where
  /-- The underlying integral scheme. -/
  scheme : Scheme
  [isIntegral : IsIntegral scheme]
  /-- The structure morphism to `Spec ℂ`. -/
  structureMap : scheme ⟶ Spec ↧ℂ
  [smooth : Smooth structureMap]
  [projective : IsProjective structureMap]

namespace SmoothProjectiveComplexVariety

instance (V : SmoothProjectiveComplexVariety) : IsIntegral V.scheme := V.isIntegral

instance (V : SmoothProjectiveComplexVariety) : Smooth V.structureMap := V.smooth

instance (V : SmoothProjectiveComplexVariety) : IsProjective V.structureMap := V.projective

noncomputable instance (V : SmoothProjectiveComplexVariety) : IsNoetherian V.scheme :=
  isNoetherian_of_isProjective V.structureMap

/-- Forget smoothness while retaining the integral projective variety. -/
def toIntegralProjective (V : SmoothProjectiveComplexVariety) :
    IntegralProjectiveComplexVariety where
  scheme := V.scheme
  isIntegral := V.isIntegral
  structureMap := V.structureMap
  projective := V.projective

/-- The analytic complex-point space. -/
abbrev analyticPoint (V : SmoothProjectiveComplexVariety) :=
  ComplexPoint V.scheme V.structureMap

noncomputable instance (V : SmoothProjectiveComplexVariety) :
    TopologicalSpace V.analyticPoint := Point.analyticTopology

/-- The analytification as an object of `TopCat`. -/
noncomputable def analytification (V : SmoothProjectiveComplexVariety) : TopCat :=
  complexAnalytification.obj (Over.mk V.structureMap)

end SmoothProjectiveComplexVariety

namespace ComplexPoint

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

end ComplexPoint

end AlgebraicGeometry
