/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierDataRepresents
public import Other.AlgebraicGeometry.CartierDataOfTrivializingCover
public import Other.AlgebraicGeometry.ChernRelativeFinalAssembly
public import Other.AlgebraicGeometry.Cycle.ChowClass
public import Other.AlgebraicGeometry.GAGAProper
public import Other.AlgebraicGeometry.HolomorphicUnitExtensionHodgeClass

/-!
# Cycle classes of principal divisors

This file proves the geometric input needed for the cycle-class map to respect rational
equivalence, beginning with the codimension-one principal-divisor case.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open Scheme.Modules

variable {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]

namespace Scheme.CartierData

variable (c : S.CartierData)

/-- Multiply every local equation of Cartier data by one nonzero rational function. -/
def mulFunctionField (f : S.functionField) (hf : f ≠ 0) : S.CartierData where
  ι := c.ι
  opens := c.opens
  nonempty := c.nonempty
  covers := c.covers
  fn i := c.fn i * f
  fn_ne_zero i := mul_ne_zero (c.fn_ne_zero i) hf
  ord_eq i j x hi hj := by
    rw [Scheme.ord_mul (c.fn_ne_zero i) hf, Scheme.ord_mul (c.fn_ne_zero j) hf,
      c.ord_eq i j x hi hj]

/-- Multiplying all local equations by one rational function does not change the represented
line bundle. -/
theorem mulFunctionField_represents {L : S.Modules} (hrep : c.Represents L)
    (f : S.functionField) (hf : f ≠ 0) :
    (c.mulFunctionField f hf).Represents L := by
  obtain ⟨g, hgen, htransition⟩ := hrep
  refine ⟨g, hgen, ?_⟩
  intro i j u hu hue
  let _ : Nonempty ((c.opens i ⊓ c.opens j : S.Opens)) := c.nonempty_inf i j
  change S.germToFunctionField (c.opens i ⊓ c.opens j) u * (c.fn j * f) = c.fn i * f
  rw [← mul_assoc, htransition i j u hu hue]

/-- Multiplying Cartier data by a rational function adds its principal divisor. -/
theorem mulFunctionField_divisor (f : S.functionField) (hf : f ≠ 0) :
    (c.mulFunctionField f hf).divisor =
      c.divisor + S.principalCodimensionOneDivisor f := by
  apply codimensionCycleSubgroup.ext
  intro x
  obtain ⟨i, hxi⟩ := c.covers x
  rw [(c.mulFunctionField f hf).divisor_apply_of_mem i x hxi]
  change S.ord (c.fn i * f) x =
    c.divisor x + S.principalCodimensionOneDivisor f x
  rw [c.divisor_apply_of_mem i x hxi, Scheme.principalCodimensionOneDivisor_apply,
    Scheme.ord_mul (c.fn_ne_zero i) hf]

end Scheme.CartierData

namespace ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- The constructed codimension-one cycle-class map kills principal divisors. -/
theorem sheafCycleClassOnCycles_principalCodimensionOneDivisor_eq_zero
    (f : X.left.functionField) (hf : f ≠ 0) :
    sheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1
      (X.left.principalCodimensionOneDivisor f) = 0 := by
  have hzero : integralToRationalCohomology X 2 (0 : H^2(X; ℤ)) ∈ hodgeClasses ℚ X 1 := by
    rw [map_zero]
    exact Submodule.zero_mem _
  obtain ⟨E, -⟩ := exists_holomorphicUnitExtension_of_integral_hodgeClass X 0 hzero
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    analyticLineBundlesAlgebraize X E.sectionSheafOfModules inferInstance
  let t := (nonempty_trivializingCover_of_isInvertible L hL).some
  let c := t.cartierData
  have hcRep : c.Represents L := t.cartierData_represents
  let c' := c.mulFunctionField f hf
  have hc'Rep : c'.Represents L := c.mulFunctionField_represents hcRep f hf
  have hc := hasDivisorClassOfCartierData (X := X) E L hL e c hcRep
  have hc' := hasDivisorClassOfCartierData (X := X) E L hL e c' hc'Rep
  apply add_left_cancel (a := sheafCycleClassOnCycles
    { scheme := X.left, structureMap := X.hom } 1 c.divisor)
  rw [add_zero, ← map_add, ← c.mulFunctionField_divisor f hf, hc', hc]

end ComplexPoint

end AlgebraicGeometry
