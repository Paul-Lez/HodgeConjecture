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

public import HodgeConjecture.Definitions.Algebra.Homology.LinearDual

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace HomologicalComplex.HomotopyEquiv

variable {R : Type u} [Field R]
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- A chain-homotopy equivalence induces, contravariantly, a linear equivalence on the
cohomology of the algebraic-dual short complexes. -/
def linearDualCohomologyEquiv (h : HomotopyEquiv K L) (n : ℕ) :
    (L.sc n).linearDual.homology ≃ₗ[R] (K.sc n).linearDual.homology :=
  (L.sc n).linearDualHomologyEquiv |>.trans <|
    h.toHomologyIso n |>.toLinearEquiv.dualMap |>.trans <|
      (K.sc n).linearDualHomologyEquiv.symm

end HomologicalComplex.HomotopyEquiv
