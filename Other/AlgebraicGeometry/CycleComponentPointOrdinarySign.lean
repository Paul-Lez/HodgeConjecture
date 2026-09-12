/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentPointClassNormalization
public import Other.AlgebraicGeometry.PointCycleClass
public import Other.AlgebraicGeometry.ComplexSupportedOrdinaryComparison

/-!
# Raw-cochain point normalization and the ordinary point sign

The general class is compared through pair maps and the positive raw relative-cochain
inclusion. The resulting agreement with the earlier ordinary point class is a theorem
about the existing definitions on both sides.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

universe u

/-- If two supports are actually equal, literal support enlargement is exactly
transport along that equality, with no scalar or orientation choice. -/
theorem enlargeSupport_eq_cast_of_eq (R : Type u) [Field R] (X : TopCat.{u})
    {Z W : Set X} (hZW : Z = W) (h : Z ⊆ W) (n : ℕ)
    (a : CohomologyWithSupport R X Z n) :
    enlargeSupport R X h n a =
      LinearEquiv.cast (R := R) (M := fun S => CohomologyWithSupport R X S n) hZW a := by
  subst W
  simp only [enlargeSupport, supportInclusionPairMap_rfl, relativeCohomologyMap_id]
  rfl

/-- The top-open projection followed by enlargement from the distinguished
point is literally the existing neighborhood-to-point pair map. -/
theorem topOpenNeighborhoodSupportPairIso_toPoint (X : TopCat.{0})
    (S : Closeds X) (z : X) (hz : z ∈ S) :
    (topOpenNeighborhoodSupportPairIso X S).hom ≫
      supportInclusionPairMap X (Set.singleton_subset_iff.mpr hz) =
        neighborhoodSupportToPointPairMap ((⊤ : Opens X) : Set X) S z hz := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

end AlgebraicTopology.Singular

namespace AlgebraicGeometry

/-- Negating every component negates the actual finite-support additive extension. -/
theorem cycleClassOnCyclesOfComponents_neg {X : Scheme} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (f : ∀ (x : X), Order.coheight x = p → M) :
    cycleClassOnCyclesOfComponents (fun x hx => -f x hx) =
      -cycleClassOnCyclesOfComponents f := by
  classical
  ext c
  change (compactCycleToFinsupp c.1).sum
      (fun x n => n • if hx : Order.coheight x = p then -f x hx else 0) =
    -((compactCycleToFinsupp c.1).sum
      (fun x n => n • if hx : Order.coheight x = p then f x hx else 0))
  rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs <;> simp

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]
  (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))

local instance cycleComponentPointOrdinarySignParacompact :
    ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X

/-- The old exactly normalized local point coclass enlarged to the actual global
component support by the literal inclusion of support-complement pairs. -/
def analyticComponentPointGlobalRelativeCoclass :
    CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * d) :=
  relativeCohomologyMap ℚ (2 * d)
    (supportInclusionPairMap (TopCat.of (ComplexPoint X))
      (Set.singleton_subset_iff.mpr (range_cycleComponentMap_subset X x ⟨z, rfl⟩)))
    (analyticPointLocalCoclass X d (cycleComponentMap X x z))

/-- Removing the top-open subtype witnesses gives the already normalized
relative point coclass by literal composition of the actual pair maps. -/
theorem analyticComponentPointGlobalRelativeCoclass_top :
    relativeCohomologyMap ℚ (2 * d)
      (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x)).hom
      (analyticComponentPointGlobalRelativeCoclass X x d z) =
        analyticComponentPointRelativeCoclass X x d z := by
  let Y := TopCat.of (ComplexPoint X)
  let S := cycleComponentAnalyticClosedSupport X x
  let y := cycleComponentMap X x z
  have hy : y ∈ S := range_cycleComponentMap_subset X x ⟨z, rfl⟩
  have h := congrArg (fun e => e (analyticPointLocalCoclass X d y))
    (relativeCohomologyMap_comp ℚ (2 * d)
      (topOpenNeighborhoodSupportPairIso Y S).hom
      (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr hy)))
  have h' := congrArg (fun f => relativeCohomologyMap ℚ (2 * d) f
      (analyticPointLocalCoclass X d y))
    (topOpenNeighborhoodSupportPairIso_toPoint Y S y hy)
  exact h.symm.trans h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 4096 in
/-- POSITIVE raw-cochain normalization: the literal supported-kernel point
target is the old exact point coclass included as an ordinary raw relative
cochain, then sent through actual sheafification and the ambient resolution. -/
theorem analyticComponentPointPositiveKernelClass_raw_positive :
    analyticComponentPointPositiveKernelClass X x d z =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (d : ℤ))).symm
        (HomologicalComplex.homologyMap
          (globalRawToSingularSheafInt X ≫
            ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
              (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
                (complexSingularToAmbientInjective X)) (2 * (d : ℤ))
          (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X))
            (cycleComponentAnalyticClosedSupport X x).compl (2 * d)
            (analyticComponentPointGlobalRelativeCoclass X x d z))) := by
  unfold analyticComponentPointPositiveKernelClass analyticComponentPointSupportedInjectiveCoclass
  rw [← analyticComponentPointGlobalRelativeCoclass_top]
  have h := complexSupportInjectiveSectionCohomologyEquiv_inclusion_positive X
    (cycleComponentAnalyticClosedSupport X x) (2 * d)
    (analyticComponentPointGlobalRelativeCoclass X x d z)
  exact congrArg
    (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (d : ℤ))).symm h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 4096 in
/-- The independent ordinary sign calculation specializes to the actual point
target. The negative sign is a theorem about the legacy cone convention. -/
theorem analyticComponentPointPositiveKernelClass_eq_neg_legacy :
    analyticComponentPointPositiveKernelClass X x d z =
      -(forgetSupport X (cycleComponentSupport X x) (2 * (d : ℤ))
        ((rationalCohomologyWithSupportAddEquivSingular X
          (cycleComponentSupport X x) (isClosed_cycleComponentSupport X x) (2 * d)).symm
            (analyticComponentPointGlobalRelativeCoclass X x d z))) := by
  unfold analyticComponentPointPositiveKernelClass analyticComponentPointSupportedInjectiveCoclass
  rw [← analyticComponentPointGlobalRelativeCoclass_top]
  exact complexSupportInjectiveSectionCohomologyEquiv_inclusion_eq_neg_legacy X
    (cycleComponentAnalyticClosedSupport X x) (2 * d)
    (analyticComponentPointGlobalRelativeCoclass X x d z)

/-- The ACTUAL general component class, with no point branch, has the positive
standard raw relative-cochain normalization at every point component. -/
theorem cycleComponentSheafClass_point_raw_positive (hx : Order.coheight x = d) :
    cycleComponentSheafClass X x (d := d) hx =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (d : ℤ))).symm
        (HomologicalComplex.homologyMap
          (globalRawToSingularSheafInt X ≫
            ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
              (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
                (complexSingularToAmbientInjective X)) (2 * (d : ℤ))
          (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X))
            (cycleComponentAnalyticClosedSupport X x).compl (2 * d)
            (analyticComponentPointGlobalRelativeCoclass X x d z))) := by
  rw [cycleComponentSheafClass_point_normalization X x d z hx,
    analyticComponentPointPositiveKernelClass_raw_positive]

/-- At the constructed geometric component point, the literal support-inclusion
class is the legacy supported generator's exact equality transport. -/
theorem analyticComponentPointGlobalRelativeCoclass_eq_maximalCodimensionSupportedGenerator
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] (x : V.scheme)
    (hx : Order.coheight x = d) :
    analyticComponentPointGlobalRelativeCoclass V.over x d
      (maximalCodimensionCycleComponentPoint V x) =
      maximalCodimensionSupportedGenerator V d x hx :=
  enlargeSupport_eq_cast_of_eq ℚ (TopCat.of (ComplexPoint V.over))
    (maximalCodimensionCycleComponentSupport_eq_singleton V d x hx).symm
    (Set.singleton_subset_iff.mpr (range_cycleComponentMap_subset V.over x
      ⟨maximalCodimensionCycleComponentPoint V x, rfl⟩)) (2 * d)
    (analyticPointLocalCoclass V.over d
      (cycleComponentMap V.over x (maximalCodimensionCycleComponentPoint V x)))

set_option maxRecDepth 4096 in
/-- The legacy component comparison is the literal existing singular-support
comparison, after its already proved supported-generator normalization. -/
theorem maximalCodimensionComponentClass_eq_directLegacyPoint
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] (x : V.scheme)
    (hx : Order.coheight x = d) :
    maximalCodimensionComponentClass V d x hx =
      forgetSupport V.over (cycleComponentSupport V.over x)
        (2 * (d : ℤ))
        ((rationalCohomologyWithSupportAddEquivSingular V.over
          (cycleComponentSupport V.over x)
          (isClosed_cycleComponentSupport V.over x) (2 * d)).symm
            (maximalCodimensionSupportedGenerator V d x hx)) := by
  rw [maximalCodimensionComponentClass_eq_forgetSupport_pointCoclass]
  rfl

/-- The independently constructed general point class is the NEGATIVE of the
legacy ordinary point class. This records the proved cone sign without changing
either definition or either exact local orientation. -/
theorem cycleComponentSheafClass_eq_neg_maximalCodimensionComponentClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] (x : V.scheme)
    (hx : Order.coheight x = d) :
    cycleComponentSheafClass V.over x (d := d) hx =
      -maximalCodimensionComponentClass V d x hx := by
  rw [cycleComponentSheafClass_point_normalization V.over x d
    (maximalCodimensionCycleComponentPoint V x) hx,
    analyticComponentPointPositiveKernelClass_eq_neg_legacy,
    analyticComponentPointGlobalRelativeCoclass_eq_maximalCodimensionSupportedGenerator V d x hx,
    maximalCodimensionComponentClass_eq_directLegacyPoint]

/-- The entire integral point-cycle map, not just an individual generator,
has the independently proved negative legacy comparison. -/
theorem sheafCycleClassOnCycles_eq_neg_pointCycleClassOnCycles
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] :
    sheafCycleClassOnCycles V d d = -pointCycleClassOnCycles V d := by
  have h : (fun (x : V.scheme) (hx : Order.coheight x = d) =>
      cycleComponentSheafClass V.over x (d := d) hx) =
        fun x hx => -maximalCodimensionComponentClass V d x hx := by
    funext x hx
    exact cycleComponentSheafClass_eq_neg_maximalCodimensionComponentClass V d x hx
  unfold sheafCycleClassOnCycles pointCycleClassOnCycles
  exact (congrArg cycleClassOnCyclesOfComponents h).trans
    (cycleClassOnCyclesOfComponents_neg (maximalCodimensionComponentClass V d))

/-- Scalar extension preserves the actual signed comparison on ALL rational
point cycles; in particular every finite rational combination has this sign. -/
theorem rationalSheafCycleClassOnCycles_eq_neg_rationalPointCycleClassOnCycles
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] :
    rationalSheafCycleClassOnCycles V d d = -rationalPointCycleClassOnCycles V d := by
  refine TensorProduct.AlgebraTensorModule.ext fun q c ↦ ?_
  change q • sheafCycleClassOnCycles V d d c = -(q • pointCycleClassOnCycles V d c)
  rw [sheafCycleClassOnCycles_eq_neg_pointCycleClassOnCycles]
  simp only [AddMonoidHom.neg_apply, smul_neg]

/-- A closed scheme point requires neither a supplied codimension proof nor a
chosen analytic point: both are constructed from the actual geometry. -/
theorem cycleComponentSheafClass_closedPoint_positiveKernel
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] (x : V.scheme)
    (hx : IsClosed ({x} : Set V.scheme)) :
    let hcodim := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := V.structureMap) (d := d) x hx
    cycleComponentSheafClass V.over x (d := d) hcodim =
      analyticComponentPointPositiveKernelClass V.over x d
        (maximalCodimensionCycleComponentPoint V x) :=
  cycleComponentSheafClass_point_normalization V.over x d
    (maximalCodimensionCycleComponentPoint V x) _

/-- The signed legacy comparison at a closed scheme point derives the needed
codimension from geometry. No point, purity, or comparison data are supplied. -/
theorem cycleComponentSheafClass_closedPoint_eq_neg_legacy
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] (x : V.scheme)
    (hx : IsClosed ({x} : Set V.scheme)) :
    let hcodim := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := V.structureMap) (d := d) x hx
    cycleComponentSheafClass V.over x (d := d) hcodim =
      -maximalCodimensionComponentClass V d x hcodim :=
  cycleComponentSheafClass_eq_neg_maximalCodimensionComponentClass V d x _

end AlgebraicGeometry.ComplexPoint
