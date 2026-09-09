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

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The two-term exponential resolution on the actual analytic variety. -/
abbrev holomorphicExponentialResolution : CochainComplex (AnalyticAdditiveSheaf X) ℕ :=
  (holomorphicExponentialSequence X d).rightResolution

/-- Integral periods augment the exponential resolution. -/
def holomorphicExponentialResolutionι :
    (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj (constantIntegerSheaf X) ⟶
      holomorphicExponentialResolution X d :=
  (holomorphicExponentialSequence X d).rightResolutionι

instance holomorphicExponentialResolutionι_quasiIso :
    QuasiIso (holomorphicExponentialResolutionι X d) :=
  (holomorphicExponentialSequence X d).rightResolutionι_quasiIso
    (holomorphicExponentialSequence_shortExact X d)

/-- The analytic chain rule defines the cochain comparison to de Rham forms. -/
def holomorphicExponentialResolutionToDeRham :
    holomorphicExponentialResolution X d ⟶ holomorphicDeRhamComplex X d :=
  (holomorphicExponentialSequence X d).fromRightResolution
    (holomorphicFunctionToZeroFormSheaf X d) (holomorphicDlogSheaf X d)
    (by
      change holomorphicFunctionToZeroFormSheaf X d ≫ (holomorphicDeRhamComplex X d).d 0 1 =
        holomorphicExpSheaf X d ≫ holomorphicDlogSheaf X d
      rw [holomorphicDeRhamComplex_d]
      exact (holomorphicExpSheaf_comp_dlog X d).symm)
    (by
      rw [holomorphicDeRhamComplex_d]
      exact holomorphicDlogSheaf_comp_differential X d)

/-- Units placed in degree one map into the exponential resolution. -/
def holomorphicUnitsToExponentialResolution :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) 1).obj (holomorphicUnitsSheaf X d) ⟶
      holomorphicExponentialResolution X d :=
  HomologicalComplex.mkHomFromSingle (𝟙 (holomorphicUnitsSheaf X d)) (by
    intro k hk
    have hk' : k = 2 := by simpa using hk.symm
    subst k
    rw [Category.id_comp]
    exact (holomorphicExponentialSequence X d).rightResolution_d_succ 0)

/-- Restricting the comparison to units gives precisely the constructed logarithmic derivative. -/
@[reassoc (attr := simp)]
theorem holomorphicUnitsToExponentialResolution_comp_deRham :
    holomorphicUnitsToExponentialResolution X d ≫ holomorphicExponentialResolutionToDeRham X d =
      holomorphicDlogComplex X d := by
  apply HomologicalComplex.from_single_hom_ext
  simp [holomorphicUnitsToExponentialResolution, holomorphicExponentialResolutionToDeRham,
    holomorphicDlogComplex]

variable [IsIntegral X.left] [Smooth X.hom]

/-- The exponential resolution extended by zero to integer cochain degrees. -/
def holomorphicExponentialResolutionInt : CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (holomorphicExponentialResolution X (dim X.left)).extend ComplexShape.embeddingUpNat

/-- The integer-indexed augmentation uses exactly the repository's constant integer complex. -/
def holomorphicExponentialResolutionIntι :
    constantIntegerSheafComplexInt X ⟶ holomorphicExponentialResolutionInt X :=
  HomologicalComplex.extendMap (holomorphicExponentialResolutionι X (dim X.left))
    ComplexShape.embeddingUpNat

instance holomorphicExponentialResolutionIntι_quasiIso :
    QuasiIso (holomorphicExponentialResolutionIntι X) := by
  unfold holomorphicExponentialResolutionIntι
  infer_instance

/-- The integer-indexed comparison from the exponential resolution to de Rham forms. -/
def holomorphicExponentialResolutionToDeRhamInt :
    holomorphicExponentialResolutionInt X ⟶ holomorphicDeRhamComplexInt X :=
  HomologicalComplex.extendMap (holomorphicExponentialResolutionToDeRham X (dim X.left))
    ComplexShape.embeddingUpNat

/-- Units in degree one map into the integer-indexed exponential resolution. -/
def holomorphicUnitsToExponentialResolutionInt :
    holomorphicUnitsComplexInt X ⟶ holomorphicExponentialResolutionInt X :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (holomorphicUnitsSheaf X (dim X.left)) 1 1 rfl).inv ≫
      HomologicalComplex.extendMap (holomorphicUnitsToExponentialResolution X (dim X.left))
        ComplexShape.embeddingUpNat

/-- The integer-indexed comparison agrees with `dlog` on units. -/
@[reassoc (attr := simp)]
theorem holomorphicUnitsToExponentialResolutionInt_comp_deRham :
    holomorphicUnitsToExponentialResolutionInt X ≫ holomorphicExponentialResolutionToDeRhamInt X =
      holomorphicDlogComplexInt X := by
  unfold holomorphicUnitsToExponentialResolutionInt holomorphicExponentialResolutionToDeRhamInt
    holomorphicDlogComplexInt
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp,
    holomorphicUnitsToExponentialResolution_comp_deRham]

/-- The proved exponential resolution induces an additive equivalence on hypercohomology. -/
def exponentialResolutionCohomologyEquiv (n : ℤ) :
    Hypercohomology X (constantIntegerSheafComplexInt X) n ≃+
      Hypercohomology X (holomorphicExponentialResolutionInt X) n :=
  AddEquiv.ofBijective (hypercohomologyMap X (holomorphicExponentialResolutionIntι X) n)
    (Localization.SmallShiftedHom.postcompEquiv
      (holomorphicExponentialResolutionIntι X) (by
        change QuasiIso (holomorphicExponentialResolutionIntι X)
        infer_instance)).bijective

/-- The integral class obtained from units using the constructed exponential resolution.
In degree two its domain is the hypercohomology of units placed in degree one. -/
def integralExponentialClass (n : ℤ) :
    Hypercohomology X (holomorphicUnitsComplexInt X) n →+
      Hypercohomology X (constantIntegerSheafComplexInt X) n :=
  (exponentialResolutionCohomologyEquiv X n).symm.toAddMonoidHom.comp
    (hypercohomologyMap X (holomorphicUnitsToExponentialResolutionInt X) n)

/-- Rational coefficients applied to the integral exponential class. -/
def rationalExponentialClass (n : ℤ) :
    Hypercohomology X (holomorphicUnitsComplexInt X) n →+ FieldCohomology ℚ X n :=
  (hypercohomologyMap X (integerToFieldConstantSheafComplexInt ℚ X 1) n).comp
    (integralExponentialClass X n)

/-- Resolving an integral exponential class recovers the original units class in the resolution. -/
@[simp]
theorem augmentation_integralExponentialClass (n : ℤ)
    (α : Hypercohomology X (holomorphicUnitsComplexInt X) n) :
    hypercohomologyMap X (holomorphicExponentialResolutionIntι X) n
        (integralExponentialClass X n α) =
      hypercohomologyMap X (holomorphicUnitsToExponentialResolutionInt X) n α :=
  (exponentialResolutionCohomologyEquiv X n).apply_symm_apply _

/-- The comparison induced by the integral-period augmentation sends the integral exponential
class to the actual logarithmic class. -/
theorem integralExponentialClass_logarithmic_comparison (n : ℤ)
    (α : Hypercohomology X (holomorphicUnitsComplexInt X) n) :
    hypercohomologyMap X
        (holomorphicExponentialResolutionIntι X ≫ holomorphicExponentialResolutionToDeRhamInt X) n
        (integralExponentialClass X n α) = logarithmicClass X n α := by
  rw [hypercohomologyMap_comp_apply, augmentation_integralExponentialClass,
    ← hypercohomologyMap_comp_apply, holomorphicUnitsToExponentialResolutionInt_comp_deRham]
  rfl

end AlgebraicGeometry.ComplexPoint
