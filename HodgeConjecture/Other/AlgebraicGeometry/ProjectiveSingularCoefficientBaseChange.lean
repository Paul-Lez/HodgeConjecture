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
public import HodgeConjecture.Other.AlgebraicTopology.SingularCoefficientBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytificationConnected
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Degree-zero coefficient change for projective analytifications

A compact locally path-connected space has finitely many path components. Its zeroth singular
homology is therefore a finite coproduct of copies of the coefficient field and is
finite-dimensional. This discharges, in degree zero, the finiteness premise in the
rational-to-complex singular-cohomology base-change theorem.

Higher-degree base change still requires finite-dimensional singular homology. That conclusion
needs the finite-CW, triangulation, or finite-good-cover comparison which is not presently in
Mathlib.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.ComplexPoint

open Point

open AlgebraicTopology.Singular
open scoped TensorProduct

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)
  [IsProjective structureMap]

/-- Zeroth rational singular homology of a smooth projective complex analytification is
finite-dimensional, without assuming global connectedness. -/
theorem finiteRationalSingularHomologyZero [IsIntegral X] [Smooth structureMap] :
    Module.Finite ℚ (Homology ℚ (TopCat.of (ComplexPoint X structureMap)) 0) := by
  let : Finite (ZerothHomotopy (ComplexPoint X structureMap)) :=
    finiteZerothHomotopy structureMap
  have hfinite : Module.Finite ℚ
      (∐ fun _ : ZerothHomotopy (ComplexPoint X structureMap) ↦
        ModuleCat.of ℚ ℚ : ModuleCat ℚ) :=
    inferInstance
  exact Module.Finite.equiv
    (TopCat.singularHomology₀Iso (TopCat.of (ComplexPoint X structureMap))
      (ModuleCat.of ℚ ℚ)).symm.toLinearEquiv

/-- Rational-to-complex singular cohomology base change for projective analytifications in
degree zero. -/
def rationalToComplexCohomologyBaseChangeZero [IsIntegral X] [Smooth structureMap] :
    ℂ ⊗[ℚ] Cohomology ℚ (TopCat.of (ComplexPoint X structureMap)) 0 ≃ₗ[ℂ]
      Cohomology ℂ (TopCat.of (ComplexPoint X structureMap)) 0 :=
  letI : Module.Finite ℚ (Homology ℚ (TopCat.of (ComplexPoint X structureMap)) 0) :=
    finiteRationalSingularHomologyZero structureMap
  rationalToComplexCohomologyBaseChange (TopCat.of (ComplexPoint X structureMap)) 0

end AlgebraicGeometry.ComplexPoint
