/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SingularSupportedRawOrdinaryComparison
public import Other.AlgebraicTopology.GlobalRawRelativeConnecting

/-!
# The exact ordinary sign of the original singular support comparison

The old singular support comparison, inverted and followed by `forgetSupport`,
is the negative of the actual positive dual-relative cochain inclusion, after the
prescribed raw-to-sheaf and singular-to-injective maps. This theorem computes a
sign already present in the definitions; it does not change an orientation or
rescale a cycle class. The comparison with the newer literal supported-section
kernel model is a separate theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]

/-- The original ordinary coclass of an actual relative class has the negative
of the positive relative cochain inclusion's sign. All augmentation, sheafification,
resolution, and degree-shift maps are the actual previously constructed ones. -/
theorem rationalCohomologyAmbient_forgetSupport_of_singular_signed
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ)
      (forgetSupport X Z (n : ℤ)
        ((rationalCohomologyWithSupportAddEquivSingular X Z hZ n).symm a)) =
    -(HomologicalComplex.homologyMap
      (globalRawToSingularSheafInt X ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (complexSingularToAmbientInjective X)) (n : ℤ)
      (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X)) Zᶜ n a)) := by
  rw [rationalCohomologyAmbient_forgetSupport_of_singular X Z hZ]
  have h := globalRawSingularRestrictionCone_connecting_of_relative ℚ
    (TopCat.of (ComplexPoint X)) Zᶜ n a
  change _ = _ at h
  erw [h]
  exact map_neg _ _

end AlgebraicGeometry.ComplexPoint
