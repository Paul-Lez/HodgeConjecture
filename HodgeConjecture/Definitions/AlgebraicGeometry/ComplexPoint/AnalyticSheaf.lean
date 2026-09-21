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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Sheaf.Basic

/-!
# Holomorphic functions on complex points

For a complex scheme smooth of relative dimension `d`, the algebraic étale charts constructed in
`ComplexPoint.SmoothCoordinates` give a canonical charted-space structure on its complex points.
This file defines its sheaf of holomorphic functions: a section is a complex-valued function
which is complex analytic in those charts. Mathlib expresses complex analyticity as manifold
differentiability of order `ω`.

The sheaf and its ring operations are built by the local-predicate sheaf machinery.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Let `X` be a smooth scheme over `ℂ` of relative dimension `d`. On its analytic space `X(ℂ)`,
this sheaf assigns to an open `U` the complex-valued functions on `U` that are analytic in the
chosen étale coordinate charts. Restriction is restriction of functions; the values here are
sets. -/
def holomorphicFunctionSheafToTypes [SmoothOfRelativeDimension d X.hom] :
    TopCat.Sheaf (Type) (TopCat.of (ComplexPoint X)) :=
  (contDiffWithinAt_localInvariantProp (I := 𝓘(ℂ, Fin d → ℂ))
    (I' := 𝓘(ℂ)) ω).sheaf (ComplexPoint X) ℂ

instance holomorphicFunctionSheafToTypes.commRing [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    CommRing ((holomorphicFunctionSheafToTypes X d).presheaf.obj U) :=
  inferInstanceAs <| CommRing
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X)); ℂ⟯

/-- Let `X` be a smooth scheme over `ℂ` of relative dimension `d`. This presheaf of commutative
rings on the analytic space `X(ℂ)` assigns to each open `U` the ring of holomorphic functions `U
→ ℂ`, with pointwise operations and restriction of functions. -/
def holomorphicFunctionPresheaf [SmoothOfRelativeDimension d X.hom] :
    TopCat.Presheaf CommRingCat (TopCat.of (ComplexPoint X)) where
  obj U := CommRingCat.of
    ((holomorphicFunctionSheafToTypes X d).presheaf.obj U)
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ℂ <|
      CategoryTheory.leOfHom h.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Let `X` be a smooth scheme over `ℂ` of relative dimension `d`. This is the sheaf of commutative
rings `𝒪` on `X(ℂ)`: its sections on an analytic open `U` are functions `U → ℂ` that are
analytic in the chosen étale charts, with pointwise ring operations. -/
def holomorphicFunctionSheaf [SmoothOfRelativeDimension d X.hom] :
    TopCat.Sheaf CommRingCat (TopCat.of (ComplexPoint X)) where
  obj := holomorphicFunctionPresheaf X d
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (holomorphicFunctionSheafToTypes X d).property

end AlgebraicGeometry.ComplexPoint
