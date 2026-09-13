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

public import Other.AlgebraicGeometry.Points
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth projective complex varieties

This auxiliary wrapper packages a nonsingular projective complex variety as a single object. It
belongs in `Other`: the Hodge-conjecture statement itself uses the unbundled scheme, structure
morphism, and typeclass hypotheses from `ComplexPoint.Basic`. A relative dimension is supplied at
each use site as a natural number together with a `SmoothOfRelativeDimension` instance.
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
  @isNoetherian_of_isProjective (Over.mk V.structureMap) V.projective

/-- The variety regarded as the corresponding object over `Spec ℂ`. -/
noncomputable abbrev over (V : SmoothProjectiveComplexVariety) : Over (Spec ↧ℂ) :=
  Over.mk V.structureMap

noncomputable instance (V : SmoothProjectiveComplexVariety) : IsIntegral V.over.left := by
  change IsIntegral V.scheme
  infer_instance

noncomputable instance (V : SmoothProjectiveComplexVariety) : Smooth V.over.hom := by
  change Smooth V.structureMap
  infer_instance

noncomputable instance (V : SmoothProjectiveComplexVariety) : IsProjective V.over.hom := by
  change IsProjective V.structureMap
  infer_instance

noncomputable instance (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] :
    SmoothOfRelativeDimension d V.over.hom := by
  change SmoothOfRelativeDimension d V.structureMap
  infer_instance

/-- The analytic complex-point space. -/
abbrev analyticPoint (V : SmoothProjectiveComplexVariety) :=
  ComplexPoint V.over

/-- The analytification as an object of `TopCat`. -/
noncomputable def analytification (V : SmoothProjectiveComplexVariety) : TopCat :=
  complexAnalytification.obj V.over

end SmoothProjectiveComplexVariety

end AlgebraicGeometry
