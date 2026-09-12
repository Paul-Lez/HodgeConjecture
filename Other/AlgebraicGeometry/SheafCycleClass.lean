/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleClassOnCycles
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SheafClass
public import Other.AlgebraicGeometry.SmoothProjective
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.ClassSpan
/-!
# Unconditional integral and rational algebraic-cycle class maps

An integral codimension-`p` cycle is sent to the sum of the constructed
component classes with its exact integer multiplicities. Rational scalar
extension then gives a rational linear map on `ℚ ⊗[ℤ] codimensionCycleSubgroup X p`.
The maps take a smooth projective complex variety, its relative dimension, and
a codimension; no orientation, fundamental class, duality, or principal-divisor
theorem is an argument. Components may be singular and have arbitrary dimension.

These are the additive and rational extensions of the constructed component classes.
Comparison with the older maximal-codimension ordinary coclass is a separate
normalization theorem, not the definition of a point branch of this map.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (V : SmoothProjectiveComplexVariety) (d : ℕ)
  [SmoothOfRelativeDimension d V.structureMap]

/-- An actual additive map from algebraic cycles to ordinary rational cohomology,
using the constructed sheaf class in every codimension. -/
def sheafCycleClassOnCycles (p : ℕ) :
    codimensionCycleSubgroup V.scheme p →+ H^(2 * (p : ℤ))(V.over; ℚ) :=
  cycleClassOnCyclesOfComponents (cycleComponentSheafClass V.over (d := d))

/-- An individual component carries its exact integer multiplicity. -/
@[simp]
theorem sheafCycleClassOnCycles_single (p : ℕ)
    (x : V.scheme) (hx : coheight x = p) (n : ℤ) :
    sheafCycleClassOnCycles V d p (codimensionCycleSubgroup.single x hx n) =
      n • cycleComponentSheafClass V.over x (d := d) hx := by
  simp [sheafCycleClassOnCycles]

/-- Evaluation on every finite integral linear combination, allowing repeated
components, negative multiplicities, and arbitrary codimension. -/
theorem sheafCycleClassOnCycles_sum_single (p : ℕ)
    {ι : Type*} (t : Finset ι) (x : ι → V.scheme)
    (hx : ∀ i, coheight (x i) = p) (n : ι → ℤ) :
    sheafCycleClassOnCycles V d p (∑ i ∈ t, codimensionCycleSubgroup.single (x i) (hx i) (n i)) =
      ∑ i ∈ t, n i • cycleComponentSheafClass V.over (x i) (d := d) (hx i) := by
  simp

/-- The explicit finite-support formula. The codimension test's zero branch
is never used for a nonzero coefficient of a codimension-`p` cycle. -/
theorem sheafCycleClassOnCycles_apply (p : ℕ) (c : codimensionCycleSubgroup V.scheme p) :
    sheafCycleClassOnCycles V d p c =
      (compactCycleToFinsupp c.1).sum fun x n ↦
        n • if hx : coheight x = p then
          cycleComponentSheafClass V.over x (d := d) hx else 0 := rfl

/-- The actual scalar-extension bilinear map, with integral cycles as its
second input, not a rational-equivalence quotient. -/
def sheafCycleClassRationalExtensionBilinear (p : ℕ) :
    ℚ →ₗ[ℚ] codimensionCycleSubgroup V.scheme p →ₗ[ℤ]
      H^(2 * (p : ℤ))(V.over; ℚ) where
  toFun q := q • (sheafCycleClassOnCycles V d p).toIntLinearMap
  map_add' _ _ := by
    ext
    simp [add_smul]
  map_smul' _ _ := by
    ext
    simp [mul_smul]

/-- The unconditional rational linear map on rational algebraic cycles in
arbitrary codimension. No unproved geometric data are arguments. -/
def rationalSheafCycleClassOnCycles (p : ℕ) :
    TensorProduct ℤ ℚ (codimensionCycleSubgroup V.scheme p) →ₗ[ℚ]
      H^(2 * (p : ℤ))(V.over; ℚ) :=
  TensorProduct.AlgebraTensorModule.lift (sheafCycleClassRationalExtensionBilinear V d p)

/-- Rational extension agrees with the constructed integral map on pure tensors. -/
@[simp]
theorem rationalSheafCycleClassOnCycles_tmul (p : ℕ) (q : ℚ)
    (c : codimensionCycleSubgroup V.scheme p) :
    rationalSheafCycleClassOnCycles V d p (q ⊗ₜ[ℤ] c) =
      q • sheafCycleClassOnCycles V d p c := rfl

/-- Exact evaluation of a component with rational multiplicity. -/
@[simp]
theorem rationalSheafCycleClassOnCycles_tmul_single (p : ℕ) (q : ℚ)
    (x : V.scheme) (hx : coheight x = p) :
    rationalSheafCycleClassOnCycles V d p (q ⊗ₜ[ℤ] codimensionCycleSubgroup.single x hx 1) =
      q • cycleComponentSheafClass V.over x (d := d) hx := by
  simp

/-- Every finite rational combination is sent to the corresponding exact
combination of the constructed ordinary cohomology classes. -/
theorem rationalSheafCycleClassOnCycles_sum_tmul_single (p : ℕ)
    {ι : Type*} (t : Finset ι) (x : ι → V.scheme)
    (hx : ∀ i, coheight (x i) = p) (q : ι → ℚ) :
    rationalSheafCycleClassOnCycles V d p
      (∑ i ∈ t, q i ⊗ₜ[ℤ] codimensionCycleSubgroup.single (x i) (hx i) 1) =
      ∑ i ∈ t, q i • cycleComponentSheafClass V.over (x i) (d := d) (hx i) := by
  simp

/-- Every actually constructed component class belongs to the algebraic cycle-class span. -/
theorem cycleComponentSheafClass_mem_algebraicCycleClassSpan
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (p : ℕ) (x : X.left) (hx : coheight x = p) :
    cycleComponentSheafClass X x (d := dim X.left) hx ∈
      algebraicCycleClassSpan X p := by
  have hle :
      Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx} ≤
        algebraicCycleClassSpan X p := by
    unfold algebraicCycleClassSpan
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  exact hle (Submodule.subset_span (Set.mem_singleton _))

end AlgebraicGeometry.ComplexPoint
