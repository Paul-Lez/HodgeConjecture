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

public import Other.AlgebraicGeometry.BorelMooreCycleClass

/-!
# A degree reduction for principal-divisor cycle classes

In maximal codimension, irreducible components are points.  If their normalized ordinary
classes are all one fixed class `m`, the componentwise class of a cycle is its coefficient sum
times `m`.  Consequently principal-divisor vanishing reduces to the scalar statement that the
coefficient sum of every pushed-forward principal divisor is zero.

The scalar map below only counts coefficients at points of the requested codimension.  This is
important because `PrincipalDivisor.pushforwardCycle` is an algebraic cycle and the current Chow
group API deliberately does not claim a dimension formula making it a pure codimension cycle.
For a proper integral curve over an algebraically closed field, the remaining scalar equality is
the usual theorem that a principal divisor has degree zero.  Neither that theorem nor the
Cartier-divisor/Thom--Gysin machinery needed for the general positive-codimension argument is
currently available in Mathlib, so no such result is assumed implicitly here.
-/

@[expose] public noncomputable section

open CategoryTheory Order

namespace AlgebraicGeometry

universe u

/-- The sum of the coefficients of an algebraic cycle at points of codimension `p`.

Applied after `AlgebraicCycle.map`, the coefficients already include the residue degrees used by
proper pushforward. -/
def codimensionCoefficientSum {X : Scheme.{u}} [CompactSpace X] (p : ℕ) :
    AlgebraicCycle X ℤ →+ ℤ :=
  cycleClassOnAlgebraicCyclesOfComponents (p := p) (fun (_ : X) _ ↦ 1)

/-- If all codimension-`p` component classes are one fixed class, their additive extension is
the codimension-`p` coefficient sum multiplied by that class. -/
lemma cycleClassOnAlgebraicCyclesOfComponents_eq_coefficientSum_smul
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (m : M)
    (hconstant : ∀ x hx, componentClass x hx = m)
    (c : AlgebraicCycle X ℤ) :
    cycleClassOnAlgebraicCyclesOfComponents componentClass c =
      codimensionCoefficientSum p c • m := by
  classical
  rw [cycleClassOnAlgebraicCyclesOfComponents_apply,
    codimensionCoefficientSum,
    cycleClassOnAlgebraicCyclesOfComponents_apply]
  simp_rw [Finsupp.sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxp : coheight x = p
  · simp [hxp, hconstant x hxp]
  · simp [hxp]

/-- For constant component classes, scalar coefficient-sum zero implies the required
cohomology-valued vanishing for one principal divisor. -/
lemma principalDivisor_class_eq_zero_of_coefficientSum_eq_zero
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (m : M)
    (hconstant : ∀ x hx, componentClass x hx = m)
    (D : PrincipalDivisor X p)
    (hdegree : codimensionCoefficientSum p D.pushforwardCycle = 0) :
    cycleClassOnAlgebraicCyclesOfComponents componentClass D.pushforwardCycle = 0 := by
  rw [cycleClassOnAlgebraicCyclesOfComponents_eq_coefficientSum_smul
    componentClass m hconstant D.pushforwardCycle, hdegree, zero_smul]

namespace ComplexPoint

/-- In the point-supported maximal-codimension case, the full cohomology-valued
principal-divisor hypothesis follows from two independent focused statements:

* all normalized ambient point classes agree with one fixed class; and
* every pushed-forward principal divisor has codimension-filtered coefficient sum zero.

The second item is precisely the scalar degree-zero theorem for principal divisors on the
one-dimensional carriers occurring here (together with the relevant dimension formula). -/
theorem maximalCodimensionPrincipalDivisorClassVanishes_of_coefficientSum
    (V : DimensionedSmoothProjectiveComplexVariety)
    (m : FieldCohomology ℚ V.structureMap (2 * (V.dimension : ℤ)))
    (hconstant : ∀ x hx, maximalCodimensionComponentClass V x hx = m)
    (hdegree : ∀ D : PrincipalDivisor V.scheme V.dimension,
      codimensionCoefficientSum V.dimension D.pushforwardCycle = 0) :
    MaximalCodimensionPrincipalDivisorClassVanishes V := by
  intro D
  exact principalDivisor_class_eq_zero_of_coefficientSum_eq_zero
    (maximalCodimensionComponentClass V) m hconstant D (hdegree D)

end ComplexPoint

end AlgebraicGeometry
