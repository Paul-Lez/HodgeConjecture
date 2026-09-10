/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechProduct
public import Other.AlgebraicGeometry.ExplicitEllipticCurveDeRhamClass
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceFilteredClass
public import Other.AlgebraicGeometry.FirstHodgeObstruction

/-!
# Cech products in holomorphic-function cohomology

This file sends the explicit curve and surface Cech extension classes to the repository's
actual `HolomorphicFunctionCohomology` groups.  The displayed smooth dimensions in the Cech
construction are transported to the intrinsic scheme dimensions before applying the
sheaf-Ext/hypercohomology equivalence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance curveIntrinsicDimensionSmooth :
    SmoothOfRelativeDimension (dim curve) curveVariety.hom :=
  dim_curve_eq_one.symm ▸
    (inferInstance : SmoothOfRelativeDimension 1 curveVariety.hom)

local instance surfaceIntrinsicDimensionSmooth :
    SmoothOfRelativeDimension (dim surface) surfaceVariety.hom :=
  dim_surface_eq_two.symm ▸
    (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)

/-- The additive holomorphic-function sheaves associated with two equal displayed smooth
dimensions are canonically isomorphic.  Smoothness witnesses are propositions, so their
choice disappears after eliminating the dimension equality. -/
def holomorphicAdditiveFunctionSheafIsoOfDimensionEq
    (X : Over (Spec (.of ℂ))) {d e : ℕ}
    (hd : SmoothOfRelativeDimension d X.hom)
    (he : SmoothOfRelativeDimension e X.hom) (h : d = e) :
    @holomorphicAdditiveFunctionSheaf X d hd ≅
      @holomorphicAdditiveFunctionSheaf X e he := by
  subst e
  exact Iso.refl _

/-- The explicit dimension-one curve function sheaf, identified with the intrinsic function
sheaf used by `HolomorphicFunctionCohomology`. -/
def curveCechFunctionSheafIso :
    holomorphicAdditiveFunctionSheaf curveVariety 1 ≅
      holomorphicAdditiveFunctionSheaf curveVariety (dim curve) :=
  holomorphicAdditiveFunctionSheafIsoOfDimensionEq curveVariety
    (inferInstance : SmoothOfRelativeDimension 1 curveVariety.hom)
    (inferInstance : SmoothOfRelativeDimension (dim curve) curveVariety.hom)
    dim_curve_eq_one.symm

/-- The explicit dimension-two surface function sheaf, identified with the intrinsic function
sheaf used by `HolomorphicFunctionCohomology`. -/
def surfaceCechFunctionSheafIso :
    surfaceCechHolomorphicFunctionSheaf ≅
      holomorphicAdditiveFunctionSheaf surfaceVariety (dim surface) :=
  holomorphicAdditiveFunctionSheafIsoOfDimensionEq surfaceVariety
    (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)
    (inferInstance : SmoothOfRelativeDimension (dim surface) surfaceVariety.hom)
    dim_surface_eq_two.symm

/-- A curve overlap function as an actual degree-one holomorphic-function cohomology class. -/
def curveHolomorphicCechCohomologyClass
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    HolomorphicFunctionCohomology curveVariety 1 :=
  sheafExtHypercohomologyEquiv curveVariety
    (holomorphicAdditiveFunctionSheaf curveVariety (dim curve)) 0 1
    ((curveHolomorphicCechClass a).comp
      (Abelian.Ext.mk₀ curveCechFunctionSheafIso.hom)
      (show 1 + 0 = 1 from rfl))

/-- The nested product of two curve overlap functions as an actual degree-two
holomorphic-function cohomology class on the surface. -/
def surfaceHolomorphicCechExternalProductCohomologyClass
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    HolomorphicFunctionCohomology surfaceVariety 2 :=
  sheafExtHypercohomologyEquiv surfaceVariety
    (holomorphicAdditiveFunctionSheaf surfaceVariety (dim surface)) 0 2
    ((surfaceHolomorphicCechExternalProductClass a b).comp
      (Abelian.Ext.mk₀ surfaceCechFunctionSheafIso.hom)
      (show 2 + 0 = 2 from rfl))

/-- The cohomological product vanishes when the second curve representative is a Cech
coboundary. -/
theorem surfaceHolomorphicCechExternalProductCohomologyClass_right_coboundary
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap))
    (b₀ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 0)))
    (b₁ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 1))) :
    surfaceHolomorphicCechExternalProductCohomologyClass a
      (curveCechCoboundary b₀ b₁) = 0 := by
  unfold surfaceHolomorphicCechExternalProductCohomologyClass
  rw [surfaceHolomorphicCechExternalProductClass_right_coboundary,
    Abelian.Ext.zero_comp, sheafExtHypercohomologyEquiv_zero]

/-- The explicit surface Cech class is nonzero in holomorphic-function cohomology exactly when
its underlying degree-two sheaf extension is nonzero. -/
theorem surfaceHolomorphicCechExternalProductCohomologyClass_ne_zero_iff
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    surfaceHolomorphicCechExternalProductCohomologyClass a b ≠ 0 ↔
      surfaceHolomorphicCechExternalProductClass a b ≠ 0 := by
  apply not_congr
  constructor
  · intro h
    have hmap : (surfaceHolomorphicCechExternalProductClass a b).comp
        (Abelian.Ext.mk₀ surfaceCechFunctionSheafIso.hom)
        (show 2 + 0 = 2 from rfl) = 0 := by
      apply (sheafExtHypercohomologyEquiv surfaceVariety
      (holomorphicAdditiveFunctionSheaf surfaceVariety (dim surface)) 0 2).injective
      simpa only [surfaceHolomorphicCechExternalProductCohomologyClass,
        sheafExtHypercohomologyEquiv_zero] using h
    have hback := congrArg
      (fun z : Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
          (holomorphicAdditiveFunctionSheaf surfaceVariety (dim surface)) 2 =>
        z.comp (Abelian.Ext.mk₀ surfaceCechFunctionSheafIso.inv)
          (show 2 + 0 = 2 from rfl)) hmap
    simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id, Abelian.Ext.zero_comp] using hback
  · intro h
    unfold surfaceHolomorphicCechExternalProductCohomologyClass
    rw [h, Abelian.Ext.zero_comp, sheafExtHypercohomologyEquiv_zero]

end AlgebraicGeometry.ExplicitEllipticCandidate
