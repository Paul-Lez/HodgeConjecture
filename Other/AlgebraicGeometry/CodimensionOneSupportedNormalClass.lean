/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CodimensionOneNormalUnit
public import Other.AlgebraicGeometry.SupportedHolomorphicUnitLocalization

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension

/-!
# The supported filtered class of a punctured normal coordinate

This specializes the generic supported localization of a holomorphic unit to
the actual punctured normal coordinate of a smooth codimension-one closed
immersion.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X Y : Over (Spec (.of ℂ))) (i : Y ⟶ X) (m : ℕ)
  [IsIntegral X.left] [Smooth X.hom]
  [SmoothOfRelativeDimension m Y.hom]
  [SmoothOfRelativeDimension (m + 1) X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- The intrinsic dimension of the ambient variety agrees with the dimension
used by the codimension-one normal chart. -/
theorem dim_eq_codimensionOne_ambient : dim X.left = m + 1 := by
  rw [TopologicalSpace.dim_eq_krullDim,
    SmoothOfRelativeDimension.orderKrullDim_eq_complex
      (f := X.hom) (d := m + 1)]
  change WithBot.unbotD 0 (↑(m + 1) : WithBot ℕ) = m + 1
  exact WithBot.unbotD_coe 0 (m + 1)

/-- Transport a units-sheaf section across an equality of two displayed
smooth relative dimensions. The two smoothness witnesses are propositions,
so after eliminating the equality their choice is immaterial. -/
def holomorphicUnitsSheafSectionOfDimensionEq
    {d e : ℕ}
    (hd : SmoothOfRelativeDimension d X.hom)
    (he : SmoothOfRelativeDimension e X.hom)
    (h : d = e) (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (@holomorphicUnitsSheaf X d hd).obj.obj (.op U)) :
    (@holomorphicUnitsSheaf X e he).obj.obj (.op U) := by
  subst e
  exact u

/-- The punctured normal-coordinate unit as a section of the intrinsic units
sheaf used by the de Rham complex. -/
def codimensionOneNormalUnitSheafSection :
    (holomorphicUnitsSheaf X (dim X.left)).obj.obj
      (.op (codimensionOnePuncturedNormalOpen X Y i m z)) := by
  have hd : dim X.left = m + 1 :=
    dim_eq_codimensionOne_ambient (X := X) (m := m)
  exact holomorphicUnitsSheafSectionOfDimensionEq X
    (inferInstance : SmoothOfRelativeDimension (m + 1) X.hom)
    (inferInstance : SmoothOfRelativeDimension (dim X.left) X.hom)
    hd.symm (codimensionOnePuncturedNormalOpen X Y i m z)
    (Additive.ofMul (codimensionOneNormalCoordinateUnit X Y i m z))

/-- The actual supported-units localization class of the punctured normal
coordinate. -/
def codimensionOneNormalSupportedUnitsClass :
    SupportedHolomorphicUnitsHypercohomology X
      (codimensionOnePuncturedNormalOpen X Y i m z).compl 2 :=
  holomorphicUnitSupportedLocalizationClass X
    (codimensionOnePuncturedNormalOpen X Y i m z)
    (codimensionOneNormalUnitSheafSection X Y i m z)

/-- The explicit supported first-filtered normal-coordinate class. -/
def codimensionOneNormalSupportedFilteredClass :
    SupportedFilteredDeRhamHypercohomology X
      (codimensionOnePuncturedNormalOpen X Y i m z).compl 1 2 :=
  holomorphicUnitSupportedFilteredClass X
    (codimensionOnePuncturedNormalOpen X Y i m z)
    (codimensionOneNormalUnitSheafSection X Y i m z)

/-- The full supported de Rham normal-coordinate class. -/
def codimensionOneNormalSupportedDeRhamClass :
    SupportedDeRhamHypercohomology X
      (codimensionOnePuncturedNormalOpen X Y i m z).compl 2 :=
  holomorphicUnitSupportedDeRhamClass X
    (codimensionOnePuncturedNormalOpen X Y i m z)
    (codimensionOneNormalUnitSheafSection X Y i m z)

/-- The normalized integral exponential class of the normal coordinate equals
the full image of its explicit supported filtered lift. -/
theorem codimensionOneNormalSupportedIntegralClass_eq_filtered :
    supportedIntegerPeriodToDeRhamCohomology X
        (codimensionOnePuncturedNormalOpen X Y i m z).compl 2
        (supportedIntegralExponentialClass X
          (codimensionOnePuncturedNormalOpen X Y i m z).compl 2
          (codimensionOneNormalSupportedUnitsClass X Y i m z)) =
      supportedFilteredToDeRhamCohomology X
        (codimensionOnePuncturedNormalOpen X Y i m z).compl 1 2
        (codimensionOneNormalSupportedFilteredClass X Y i m z) :=
  holomorphicUnitSupportedIntegralClass_eq_filtered X
    (codimensionOnePuncturedNormalOpen X Y i m z)
    (codimensionOneNormalUnitSheafSection X Y i m z)

/-- Forgetting the filtration on the normal-coordinate class gives its full
supported logarithmic de Rham class. -/
theorem codimensionOneNormalSupportedFilteredClass_toDeRham :
    supportedFilteredToDeRhamCohomology X
        (codimensionOnePuncturedNormalOpen X Y i m z).compl 1 2
        (codimensionOneNormalSupportedFilteredClass X Y i m z) =
      codimensionOneNormalSupportedDeRhamClass X Y i m z :=
  holomorphicUnitSupportedFilteredClass_toDeRham X
    (codimensionOnePuncturedNormalOpen X Y i m z)
    (codimensionOneNormalUnitSheafSection X Y i m z)

end AlgebraicGeometry.ComplexPoint
