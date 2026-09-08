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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Sheaf.Basic

/-!
# Holomorphic functions on complex points

For a complex scheme smooth of relative dimension `d`, the algebraic étale charts constructed in
`SmoothComplexCoordinates` give a canonical charted-space structure on its complex points. This
file defines its sheaf of holomorphic functions: a section is a complex-valued function which is
complex analytic in those charts. Mathlib expresses complex analyticity as manifold
differentiability of order `ω`.

The sheaf and its ring operations are constructed by the local-predicate sheaf machinery. No
analytic atlas or sheaf is supplied as data.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)

/-- The sheaf of complex-valued functions which are analytic in the algebraically constructed
étale charts, initially regarded as a sheaf of types. -/
def holomorphicFunctionSheafToTypes [SmoothOfRelativeDimension d structureMap] :
    TopCat.Sheaf (Type) (TopCat.of (ComplexPoint (Over.mk structureMap))) :=
  (contDiffWithinAt_localInvariantProp (I := 𝓘(ℂ, Fin d → ℂ))
    (I' := 𝓘(ℂ)) ω).sheaf (ComplexPoint (Over.mk structureMap)) ℂ

instance holomorphicFunctionSheafToTypes.commRing [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint (Over.mk structureMap))))ᵒᵖ) :
    CommRing ((holomorphicFunctionSheafToTypes structureMap d).presheaf.obj U) :=
  inferInstanceAs <| CommRing
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint (Over.mk structureMap))); ℂ⟯

/-- The presheaf of rings underlying the holomorphic-function sheaf. -/
def holomorphicFunctionPresheaf [SmoothOfRelativeDimension d structureMap] :
    TopCat.Presheaf CommRingCat (TopCat.of (ComplexPoint (Over.mk structureMap))) where
  obj U := CommRingCat.of
    ((holomorphicFunctionSheafToTypes structureMap d).presheaf.obj U)
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ℂ <|
      CategoryTheory.leOfHom h.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf of complex-valued functions which are analytic in the algebraically constructed
étale charts. -/
def holomorphicFunctionSheaf [SmoothOfRelativeDimension d structureMap] :
    TopCat.Sheaf CommRingCat (TopCat.of (ComplexPoint (Over.mk structureMap))) where
  obj := holomorphicFunctionPresheaf structureMap d
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (holomorphicFunctionSheafToTypes structureMap d).property

/-- A section of the holomorphic-function sheaf is an analytic map to `ℂ` in the constructed
charted-space structure. -/
lemma holomorphicFunctionSheaf_section_analytic [SmoothOfRelativeDimension d structureMap]
    {U : (Opens (TopCat.of (ComplexPoint (Over.mk structureMap))))ᵒᵖ}
    (s : (holomorphicFunctionSheaf structureMap d).presheaf.obj U) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω s.1 :=
  (contDiffWithinAt_localInvariantProp ω).section_spec _ _ _ _

end AlgebraicGeometry.ComplexPoint
