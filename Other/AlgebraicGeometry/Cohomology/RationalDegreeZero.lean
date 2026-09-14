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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import Other.AlgebraicTopology.Sheaf.ConstantDegreeZero
public import Other.AlgebraicGeometry.Hodge.Filtration

/-!
# Degree-zero rational constant-sheaf complexes

Representation-independent degree-zero identifications for the constant-sheaf complexes.

The former computation through SmallShiftedHom belonged to the old presentation of
hypercohomology. It is intentionally not reproduced here: comparisons for the functorial
derived-global-sections construction should be developed directly from that construction.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- The natural-to-integer cochain embedding sends degree zero to degree zero. -/
lemma embeddingUpNat_zero : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl

/-- The extended integer constant-sheaf complex is the integer constant sheaf in degree zero. -/
def constantIntegerSheafComplexIntIsoSingleZero :
    constantIntegerSheafComplexInt X ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        𝓒(↧(ComplexPoint X); ℤ) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    𝓒(↧(ComplexPoint X); ℤ) 0 0 embeddingUpNat_zero

/-- The extended rational constant-sheaf complex is the rational constant sheaf in degree zero. -/
def constantRationalSheafComplexIntIsoSingleZero :
    constantFieldSheafComplexInt ℚ X ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        𝓒(↧(ComplexPoint X); ℚ) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    𝓒(↧(ComplexPoint X); ℚ) 0 0 embeddingUpNat_zero

end AlgebraicGeometry.ComplexPoint
