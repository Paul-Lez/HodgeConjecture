/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.ShortExactResolution
public import Other.AlgebraicGeometry.HolomorphicExponentialSequence
public import Other.AlgebraicGeometry.FilteredLogarithmicClass

import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# The exponential resolution and the de Rham comparison

The two-term complex of holomorphic functions and holomorphic units resolves the actual constant
integer sheaf, with augmentation `n ↦ 2πi n`. The identity in degree zero and `dlog` in degree one
give a cochain map to holomorphic de Rham forms. Its restriction to units is the logarithmic
class map already constructed with values in the Hodge filtration.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

/-- The two-term exponential resolution on the actual analytic variety. -/
abbrev holomorphicExponentialResolution : CochainComplex (AnalyticAdditiveSheaf s) ℕ :=
  (holomorphicExponentialSequence s d).rightResolution

/-- Integral periods augment the exponential resolution. -/
def holomorphicExponentialResolutionι :
    (CochainComplex.single₀ (AnalyticAdditiveSheaf s)).obj (constantIntegerSheaf s) ⟶
      holomorphicExponentialResolution s d :=
  (holomorphicExponentialSequence s d).rightResolutionι

instance holomorphicExponentialResolutionι_quasiIso :
    QuasiIso (holomorphicExponentialResolutionι s d) :=
  (holomorphicExponentialSequence s d).rightResolutionι_quasiIso
    (holomorphicExponentialSequence_shortExact s d)

/-- The analytic chain rule defines the cochain comparison to de Rham forms. -/
def holomorphicExponentialResolutionToDeRham :
    holomorphicExponentialResolution s d ⟶ holomorphicDeRhamComplex s d :=
  (holomorphicExponentialSequence s d).fromRightResolution
    (holomorphicFunctionToZeroFormSheaf s d) (holomorphicDlogSheaf s d)
    (by
      change holomorphicFunctionToZeroFormSheaf s d ≫ (holomorphicDeRhamComplex s d).d 0 1 =
        holomorphicExpSheaf s d ≫ holomorphicDlogSheaf s d
      rw [holomorphicDeRhamComplex_d]
      exact (holomorphicExpSheaf_comp_dlog s d).symm)
    (by
      rw [holomorphicDeRhamComplex_d]
      exact holomorphicDlogSheaf_comp_differential s d)

/-- Units placed in degree one map into the exponential resolution. -/
def holomorphicUnitsToExponentialResolution :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) 1).obj (holomorphicUnitsSheaf s d) ⟶
      holomorphicExponentialResolution s d :=
  HomologicalComplex.mkHomFromSingle (𝟙 (holomorphicUnitsSheaf s d)) (by
    intro k hk
    have hk' : k = 2 := by simpa using hk.symm
    subst k
    rw [Category.id_comp]
    exact (holomorphicExponentialSequence s d).rightResolution_d_succ 0)

/-- Restricting the comparison to units gives precisely the constructed logarithmic derivative. -/
@[reassoc (attr := simp)]
theorem holomorphicUnitsToExponentialResolution_comp_deRham :
    holomorphicUnitsToExponentialResolution s d ≫ holomorphicExponentialResolutionToDeRham s d =
      holomorphicDlogComplex s d := by
  apply HomologicalComplex.from_single_hom_ext
  simp [holomorphicUnitsToExponentialResolution, holomorphicExponentialResolutionToDeRham,
    holomorphicDlogComplex]

variable [IsIntegral X] [Smooth s]

/-- The exponential resolution extended by zero to integer cochain degrees. -/
def holomorphicExponentialResolutionInt : CochainComplex (AnalyticAdditiveSheaf s) ℤ :=
  (holomorphicExponentialResolution s (dim X)).extend ComplexShape.embeddingUpNat

/-- The integer-indexed augmentation uses exactly the repository's constant integer complex. -/
def holomorphicExponentialResolutionIntι :
    constantIntegerSheafComplexInt s ⟶ holomorphicExponentialResolutionInt s :=
  HomologicalComplex.extendMap (holomorphicExponentialResolutionι s (dim X))
    ComplexShape.embeddingUpNat

instance holomorphicExponentialResolutionIntι_quasiIso :
    QuasiIso (holomorphicExponentialResolutionIntι s) := by
  unfold holomorphicExponentialResolutionIntι
  infer_instance

/-- The integer-indexed comparison from the exponential resolution to de Rham forms. -/
def holomorphicExponentialResolutionToDeRhamInt :
    holomorphicExponentialResolutionInt s ⟶ holomorphicDeRhamComplexInt s :=
  HomologicalComplex.extendMap (holomorphicExponentialResolutionToDeRham s (dim X))
    ComplexShape.embeddingUpNat

/-- Units in degree one map into the integer-indexed exponential resolution. -/
def holomorphicUnitsToExponentialResolutionInt :
    holomorphicUnitsComplexInt s ⟶ holomorphicExponentialResolutionInt s :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (holomorphicUnitsSheaf s (dim X)) 1 1 rfl).inv ≫
      HomologicalComplex.extendMap (holomorphicUnitsToExponentialResolution s (dim X))
        ComplexShape.embeddingUpNat

/-- The integer-indexed comparison agrees with `dlog` on units. -/
@[reassoc (attr := simp)]
theorem holomorphicUnitsToExponentialResolutionInt_comp_deRham :
    holomorphicUnitsToExponentialResolutionInt s ≫ holomorphicExponentialResolutionToDeRhamInt s =
      holomorphicDlogComplexInt s := by
  unfold holomorphicUnitsToExponentialResolutionInt holomorphicExponentialResolutionToDeRhamInt
    holomorphicDlogComplexInt
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp,
    holomorphicUnitsToExponentialResolution_comp_deRham]

/-- The proved exponential resolution induces an additive equivalence on hypercohomology. -/
def exponentialResolutionCohomologyEquiv (n : ℤ) :
    Hypercohomology s (constantIntegerSheafComplexInt s) n ≃+
      Hypercohomology s (holomorphicExponentialResolutionInt s) n :=
  AddEquiv.ofBijective (hypercohomologyMap s (holomorphicExponentialResolutionIntι s) n)
    (Localization.SmallShiftedHom.postcompEquiv
      (holomorphicExponentialResolutionIntι s) (by
        change QuasiIso (holomorphicExponentialResolutionIntι s)
        infer_instance)).bijective

/-- The integral class obtained from units using the constructed exponential resolution.
In degree two its domain is the hypercohomology of units placed in degree one. -/
def integralExponentialClass (n : ℤ) :
    Hypercohomology s (holomorphicUnitsComplexInt s) n →+
      Hypercohomology s (constantIntegerSheafComplexInt s) n :=
  (exponentialResolutionCohomologyEquiv s n).symm.toAddMonoidHom.comp
    (hypercohomologyMap s (holomorphicUnitsToExponentialResolutionInt s) n)

/-- Rational coefficients applied to the integral exponential class. -/
def rationalExponentialClass (n : ℤ) :
    Hypercohomology s (holomorphicUnitsComplexInt s) n →+ FieldCohomology ℚ s n :=
  (hypercohomologyMap s (integerToFieldConstantSheafComplexInt ℚ s 1) n).comp
    (integralExponentialClass s n)

/-- Resolving an integral exponential class recovers the original units class in the resolution. -/
@[simp]
theorem augmentation_integralExponentialClass (n : ℤ)
    (α : Hypercohomology s (holomorphicUnitsComplexInt s) n) :
    hypercohomologyMap s (holomorphicExponentialResolutionIntι s) n
        (integralExponentialClass s n α) =
      hypercohomologyMap s (holomorphicUnitsToExponentialResolutionInt s) n α :=
  (exponentialResolutionCohomologyEquiv s n).apply_symm_apply _

/-- The comparison induced by the integral-period augmentation sends the integral exponential
class to the actual logarithmic class. -/
theorem integralExponentialClass_logarithmic_comparison (n : ℤ)
    (α : Hypercohomology s (holomorphicUnitsComplexInt s) n) :
    hypercohomologyMap s
        (holomorphicExponentialResolutionIntι s ≫ holomorphicExponentialResolutionToDeRhamInt s) n
        (integralExponentialClass s n α) = logarithmicClass s n α := by
  rw [hypercohomologyMap_comp_apply, augmentation_integralExponentialClass,
    ← hypercohomologyMap_comp_apply, holomorphicUnitsToExponentialResolutionInt_comp_deRham]
  rfl

end AlgebraicGeometry.ComplexPoint
