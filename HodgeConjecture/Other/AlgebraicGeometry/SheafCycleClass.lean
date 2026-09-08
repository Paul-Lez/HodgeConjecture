/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSheafClass
public import HodgeConjecture.Other.AlgebraicGeometry.DimensionedSmoothProjective
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleClass

/-!
# Unconditional integral and rational algebraic-cycle class maps

An integral codimension-`p` cycle is sent to the sum of the constructed
component classes with its exact integer multiplicities. Rational scalar
extension then gives a rational linear map on `ℚ ⊗[ℤ] CodimensionCycle X p`.
The maps take only a smooth projective complex variety and a codimension;
no orientation, fundamental class, duality, or principal-divisor theorem is
an argument. Components may be singular and have arbitrary dimension.

These are maps on CYCLES, not Chow groups. Descent to the quotient still
requires proving that the constructed map kills principal-divisor relations.
Comparison with the older maximal-codimension ordinary coclass is a separate
normalization theorem, not the definition of a point branch of this map.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

/-- An actual additive map from algebraic cycles to ordinary rational cohomology,
using the constructed sheaf class in every codimension. -/
def sheafCycleClassOnCycles (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ) :
    CodimensionCycle V.scheme p →+ FieldCohomology ℚ V.structureMap (2 * (p : ℤ)) :=
  cycleClassOnCyclesOfComponents (cycleComponentSheafClass V.structureMap (d := V.dimension))

/-- An individual component carries its exact integer multiplicity. -/
@[simp]
theorem sheafCycleClassOnCycles_single
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ)
    (x : V.scheme) (hx : coheight x = p) (n : ℤ) :
    sheafCycleClassOnCycles V p (CodimensionCycle.single x hx n) =
      n • cycleComponentSheafClass V.structureMap x (d := V.dimension) hx := by
  simp [sheafCycleClassOnCycles]

/-- Evaluation on every finite integral linear combination, allowing repeated
components, negative multiplicities, and arbitrary codimension. -/
theorem sheafCycleClassOnCycles_sum_single
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ)
    {ι : Type*} (t : Finset ι) (x : ι → V.scheme)
    (hx : ∀ i, coheight (x i) = p) (n : ι → ℤ) :
    sheafCycleClassOnCycles V p (∑ i ∈ t, CodimensionCycle.single (x i) (hx i) (n i)) =
      ∑ i ∈ t, n i • cycleComponentSheafClass V.structureMap (x i) (d := V.dimension) (hx i) := by
  simp

/-- The explicit finite-support formula. The codimension test's zero branch
is never used for a nonzero coefficient of a codimension-`p` cycle. -/
theorem sheafCycleClassOnCycles_apply
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ) (c : CodimensionCycle V.scheme p) :
    sheafCycleClassOnCycles V p c =
      (compactCycleToFinsupp c.1).sum fun x n ↦
        n • if hx : coheight x = p then
          cycleComponentSheafClass V.structureMap x (d := V.dimension) hx else 0 := rfl

/-- The actual scalar-extension bilinear map, with integral cycles as its
second input, not a rational-equivalence quotient. -/
def sheafCycleClassRationalExtensionBilinear
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ) :
    ℚ →ₗ[ℚ] CodimensionCycle V.scheme p →ₗ[ℤ]
      FieldCohomology ℚ V.structureMap (2 * (p : ℤ)) where
  toFun q := q • (sheafCycleClassOnCycles V p).toIntLinearMap
  map_add' _ _ := by
    ext
    simp [add_smul]
  map_smul' _ _ := by
    ext
    simp [mul_smul]

/-- The unconditional rational linear map on rational algebraic cycles in
arbitrary codimension. No unproved geometric data are arguments. -/
def rationalSheafCycleClassOnCycles
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ) :
    TensorProduct ℤ ℚ (CodimensionCycle V.scheme p) →ₗ[ℚ]
      FieldCohomology ℚ V.structureMap (2 * (p : ℤ)) :=
  TensorProduct.AlgebraTensorModule.lift (sheafCycleClassRationalExtensionBilinear V p)

/-- Rational extension agrees with the constructed integral map on pure tensors. -/
@[simp]
theorem rationalSheafCycleClassOnCycles_tmul
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ) (q : ℚ)
    (c : CodimensionCycle V.scheme p) :
    rationalSheafCycleClassOnCycles V p (q ⊗ₜ[ℤ] c) = q • sheafCycleClassOnCycles V p c := rfl

/-- Exact evaluation of a component with rational multiplicity. -/
@[simp]
theorem rationalSheafCycleClassOnCycles_tmul_single
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ) (q : ℚ)
    (x : V.scheme) (hx : coheight x = p) :
    rationalSheafCycleClassOnCycles V p (q ⊗ₜ[ℤ] CodimensionCycle.single x hx 1) =
      q • cycleComponentSheafClass V.structureMap x (d := V.dimension) hx := by
  simp

/-- Every finite rational combination is sent to the corresponding exact
combination of the constructed ordinary cohomology classes. -/
theorem rationalSheafCycleClassOnCycles_sum_tmul_single
    (V : DimensionedSmoothProjectiveComplexVariety) (p : ℕ)
    {ι : Type*} (t : Finset ι) (x : ι → V.scheme)
    (hx : ∀ i, coheight (x i) = p) (q : ι → ℚ) :
    rationalSheafCycleClassOnCycles V p
      (∑ i ∈ t, q i ⊗ₜ[ℤ] CodimensionCycle.single (x i) (hx i) 1) =
      ∑ i ∈ t, q i • cycleComponentSheafClass V.structureMap (x i) (d := V.dimension) (hx i) := by
  simp

end AlgebraicGeometry.ComplexPoint
