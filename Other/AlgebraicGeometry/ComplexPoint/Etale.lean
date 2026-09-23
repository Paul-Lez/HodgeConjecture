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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Localization
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.StandardEtale
public import Mathlib.Analysis.Calculus.ContDiff.RCLike -- shake: keep
public import Mathlib.Analysis.Calculus.Deriv.Polynomial -- shake: keep
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Etale

/-!
# Etale, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Etale`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
open scoped Polynomial Topology ContDiff
open CategoryTheory Topology Filter
namespace AlgebraicGeometry.ComplexAlgHom
open ComplexPoint Point
noncomputable section
variable {n : ℕ} (P : StandardEtalePair (complexPolynomialRing n))

/-- Projection from a standard étale equation locus to its polynomial coordinates is a local
homeomorphism. -/
lemma isLocalHomeomorph_standardEtaleCoordinateProjection :
    IsLocalHomeomorph (fun z : standardEtaleCoordinateSpace P ↦ z.1.1) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  exact IsLocalHomeomorphOn.mk _ _ fun z _ ↦
    ⟨standardEtaleProjectionChart P z, standardEtale_mem_implicit_source P z, fun _ _ ↦ rfl⟩

end
end AlgebraicGeometry.ComplexAlgHom
end

@[expose] public section
open scoped Polynomial Topology ContDiff
open CategoryTheory Topology Filter
namespace AlgebraicGeometry.ComplexPoint
open ComplexAlgHom Point
noncomputable section
variable {n : ℕ} (P : StandardEtalePair (complexPolynomialRing n))

lemma specMap_algebraMap_comp_affineSpecStructureMap :
    Spec.map (CommRingCat.ofHom (algebraMap (complexPolynomialRing n) P.Ring)) ≫
        affineSpecStructureMap (complexPolynomialRing n) =
      affineSpecStructureMap P.Ring := by
  rw [← Spec.map_comp]
  congr 1

end
end AlgebraicGeometry.ComplexPoint
end
