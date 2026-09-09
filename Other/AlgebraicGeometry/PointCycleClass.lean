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
# The unconditional class map on zero-dimensional cycles

On a smooth projective complex variety of dimension `d`, this file constructs an additive map
from integral codimension-`d` cycles to rational cohomology in degree `2 * d`, and its rational
scalar extension. The component classes come from the already constructed complex-oriented
Borel--Moore point classes. No duality map, local Thom-cap map, fundamental class, or
principal-divisor theorem is an argument to either construction.

The evaluation theorems identify the result with the existing normalized point coclass, with
the exact integer or rational multiplicity, not merely up to a nonzero scalar. The domain is
cycles, not Chow groups: this file does not prove rational-equivalence invariance. It also does
not construct the classes of positive-dimensional components.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option maxRecDepth 4096 in
/-- The fully constructed normalized-interface ordinary point class agrees exactly with the
previous point coclass construction. -/
@[simp] lemma maximalCodimensionComplexOrientedComponentClassData_ordinary
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : coheight x = V.dimension) :
    (maximalCodimensionComplexOrientedComponentClassData V x hx).ordinaryFundamentalClass =
      maximalCodimensionComponentClass V x hx :=
  rfl

/-- The unconditional additive cycle-class map in maximal codimension. It takes only the
geometric variety as input and uses its constructed complex-oriented point classes. -/
def pointCycleClassOnCycles (V : DimensionedSmoothProjectiveComplexVariety) :
    CodimensionCycle V.scheme V.dimension →+
      FieldCohomology ℚ V.over (2 * (V.dimension : ℤ)) :=
  cycleClassOnCyclesOfComponents (maximalCodimensionComponentClass V)

/-- An individual point with multiplicity `n` has exactly `n` times its normalized coclass. -/
@[simp] lemma pointCycleClassOnCycles_single
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : coheight x = V.dimension) (n : ℤ) :
    pointCycleClassOnCycles V (CodimensionCycle.single x hx n) =
      n • maximalCodimensionComponentClass V x hx := by
  simp [pointCycleClassOnCycles]

/-- A closed scheme point automatically has the required maximal codimension; no extra
dimension or purity certificate is needed to evaluate its cycle class. -/
lemma pointCycleClassOnCycles_single_closedPoint
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : IsClosed ({x} : Set V.scheme)) (n : ℤ) :
    let hcodim := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := V.structureMap) (d := V.dimension) x hx
    pointCycleClassOnCycles V (CodimensionCycle.single x hcodim n) =
      n • maximalCodimensionComponentClass V x hcodim :=
  pointCycleClassOnCycles_single V x _ n

/-- The point-cycle construction really uses the normalized supported point coclass before
forgetting support. This equality fixes its scale and sign. -/
lemma pointCycleClassOnCycles_single_eq_forgetSupport_pointCoclass
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : coheight x = V.dimension) (n : ℤ) :
    pointCycleClassOnCycles V (CodimensionCycle.single x hx n) =
      n • forgetSupport V.over
        (cycleComponentSupport V.over x) (2 * (V.dimension : ℤ))
        ((auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension
          V x hx).supportedComparison.symm (maximalCodimensionSupportedGenerator V x hx)) := by
  rw [pointCycleClassOnCycles_single,
    maximalCodimensionComponentClass_eq_forgetSupport_pointCoclass]

/-- Evaluation on an arbitrary finite linear combination of points, including repeated points
and negative multiplicities. -/
lemma pointCycleClassOnCycles_sum_single
    (V : DimensionedSmoothProjectiveComplexVariety) {ι : Type*} (s : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, coheight (x i) = V.dimension) (n : ι → ℤ) :
    pointCycleClassOnCycles V (∑ i ∈ s, CodimensionCycle.single (x i) (hx i) (n i)) =
      ∑ i ∈ s, n i • maximalCodimensionComponentClass V (x i) (hx i) := by
  simp

/-- The finite-support formula on every integral point cycle. The zero branch is unused at
every point with a nonzero coefficient, by the defining codimension condition on `c`. -/
lemma pointCycleClassOnCycles_apply
    (V : DimensionedSmoothProjectiveComplexVariety)
    (c : CodimensionCycle V.scheme V.dimension) :
    pointCycleClassOnCycles V c =
      (compactCycleToFinsupp c.1).sum fun x n ↦
        n • if hx : coheight x = V.dimension then
          maximalCodimensionComponentClass V x hx else 0 :=
  rfl

/-- The bilinear map used to extend the unconditional point-cycle map to rational
coefficients. Its second argument is an integral cycle, not a Chow class. -/
def pointCycleClassRationalExtensionBilinear
    (V : DimensionedSmoothProjectiveComplexVariety) :
    ℚ →ₗ[ℚ] CodimensionCycle V.scheme V.dimension →ₗ[ℤ]
      FieldCohomology ℚ V.over (2 * (V.dimension : ℤ)) where
  toFun q := q • (pointCycleClassOnCycles V).toIntLinearMap
  map_add' _ _ := by
    ext
    simp [add_smul]
  map_smul' _ _ := by
    ext
    simp [mul_smul]

/-- The unconditional rational linear class map on rational zero-dimensional cycles,
represented by `ℚ ⊗[ℤ] CodimensionCycle V.scheme V.dimension`. No rational-equivalence
quotient is taken here. -/
def rationalPointCycleClassOnCycles (V : DimensionedSmoothProjectiveComplexVariety) :
    TensorProduct ℤ ℚ (CodimensionCycle V.scheme V.dimension) →ₗ[ℚ]
      FieldCohomology ℚ V.over (2 * (V.dimension : ℤ)) :=
  TensorProduct.AlgebraTensorModule.lift (pointCycleClassRationalExtensionBilinear V)

/-- Rational extension agrees with the integral class map on pure tensors. -/
@[simp] lemma rationalPointCycleClassOnCycles_tmul
    (V : DimensionedSmoothProjectiveComplexVariety) (q : ℚ)
    (c : CodimensionCycle V.scheme V.dimension) :
    rationalPointCycleClassOnCycles V (q ⊗ₜ[ℤ] c) = q • pointCycleClassOnCycles V c :=
  rfl

/-- Exact evaluation of a point with arbitrary rational multiplicity. -/
@[simp] lemma rationalPointCycleClassOnCycles_tmul_single
    (V : DimensionedSmoothProjectiveComplexVariety) (q : ℚ) (x : V.scheme)
    (hx : coheight x = V.dimension) :
    rationalPointCycleClassOnCycles V (q ⊗ₜ[ℤ] CodimensionCycle.single x hx 1) =
      q • maximalCodimensionComponentClass V x hx := by
  simp

/-- Exact evaluation on every finite rational linear combination of points. -/
lemma rationalPointCycleClassOnCycles_sum_tmul_single
    (V : DimensionedSmoothProjectiveComplexVariety) {ι : Type*} (s : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, coheight (x i) = V.dimension) (q : ι → ℚ) :
    rationalPointCycleClassOnCycles V
        (∑ i ∈ s, q i ⊗ₜ[ℤ] CodimensionCycle.single (x i) (hx i) 1) =
      ∑ i ∈ s, q i • maximalCodimensionComponentClass V (x i) (hx i) := by
  simp

end AlgebraicGeometry.ComplexPoint
