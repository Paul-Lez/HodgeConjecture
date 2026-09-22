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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Points
public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularSubdivisionCochainSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothEquidimensional
import HodgeConjecture.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationHausdorff

/-!
# Paracompact open subsets of smooth projective analytifications

A smooth projective complex variety has a compact Hausdorff analytification and algebraic
coordinate charts modeled on a finite-dimensional complex vector space. Every open subset is
therefore paracompact. This supplies the hereditary-paracompactness input for the flasque
singular-cochain resolution.
-/

@[expose] public noncomputable section

open TopologicalSpace
open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))
  [IsProjective X.hom]

/-- Every open subset of the analytification of a projective scheme smooth of a fixed relative
dimension is paracompact.  Unlike the dimension-free specialization below, this does not require
integrality: the explicitly supplied smooth dimension already provides the manifold model. -/
theorem openParacompactSpace_of_smoothOfRelativeDimension (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (U : Opens (ComplexPoint X)) : ParacompactSpace U :=
  opens_paracompactSpace_of_compact_chartedSpace (H := Fin d → ℂ) U

/-- Every open subset of a smooth projective complex analytification is paracompact. -/
theorem openParacompactSpace [IsIntegral X.left] [Smooth X.hom]
    (U : Opens (ComplexPoint X)) : ParacompactSpace U :=
  openParacompactSpace_of_smoothOfRelativeDimension X (dim X.left) U

/-- Every term of the rational singular-cochain sheaf resolution on a projective
analytification smooth of a specified relative dimension is flasque.  This avoids the
unnecessary integrality hypothesis of the dimension-free specialization below. -/
theorem rationalSingularCochainSheafIsFlasque_of_smoothOfRelativeDimension (d n : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    TopCat.Sheaf.IsFlasque
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ
        (TopCat.of (ComplexPoint X)) n) := by
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U :=
    openParacompactSpace_of_smoothOfRelativeDimension X d
  infer_instance

/-- Every term of the rational singular-cochain sheaf resolution on a smooth projective
analytification is flasque. -/
theorem rationalSingularCochainSheafIsFlasque [IsIntegral X.left] [Smooth X.hom]
    (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ
        (TopCat.of (ComplexPoint X)) n) := by
  exact rationalSingularCochainSheafIsFlasque_of_smoothOfRelativeDimension X (dim X.left) n

/-- Ordinary rational singular cochains compute the global sections of the chosen
singular-cochain sheaf complex on a projective analytification smooth of a specified relative
dimension. -/
theorem rationalSingularCochain_globalComparison_quasiIso_of_smoothOfRelativeDimension
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X))) := by
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U :=
    openParacompactSpace_of_smoothOfRelativeDimension X d
  exact AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso

/-- Ordinary rational singular cochains compute the global sections of the chosen
singular-cochain sheaf complex on a smooth projective analytification. -/
theorem rationalSingularCochain_globalComparison_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X))) := by
  exact rationalSingularCochain_globalComparison_quasiIso_of_smoothOfRelativeDimension
    X (dim X.left)

end AlgebraicGeometry.ComplexPoint
