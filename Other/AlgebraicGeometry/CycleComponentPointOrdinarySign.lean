/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentPointClassNormalization
public import Other.AlgebraicGeometry.PointCycleClass
public import Other.AlgebraicGeometry.ComplexSupportedOrdinaryComparison

/-!
# Actual raw-cochain point normalization and the legacy ordinary sign

The general class is compared through literal pair maps and the positive raw
relative-cochain inclusion. The comparison with the legacy ordinary point class
is a theorem about existing definitions, not a change of orientation or a point
branch in the general construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4096

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
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X) (d : ℕ)
  [SmoothOfRelativeDimension d s]
  (z : ComplexPoint (cycleComponent X x) (cycleComponentι X x ≫ s))

local instance cycleComponentPointOrdinarySignParacompact :
    ∀ W : Opens (ComplexPoint X s), ParacompactSpace W := openParacompactSpace s

/-- The old exactly normalized local point coclass enlarged to the actual global
component support by the literal inclusion of support-complement pairs. -/
def analyticComponentPointGlobalRelativeCoclass :
    CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X s)) (cycleComponentSupport s x) (2 * d) :=
  relativeCohomologyMap ℚ (2 * d)
    (supportInclusionPairMap (TopCat.of (ComplexPoint X s))
      (Set.singleton_subset_iff.mpr (range_cycleComponentMap_subset s x ⟨z, rfl⟩)))
    (analyticPointLocalCoclass s d (cycleComponentMap s x z))

/-- Removing the top-open subtype witnesses gives the already normalized
relative point coclass by literal composition of the actual pair maps. -/
theorem analyticComponentPointGlobalRelativeCoclass_top :
    relativeCohomologyMap ℚ (2 * d)
      (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X s))
        (cycleComponentAnalyticClosedSupport s x)).hom
      (analyticComponentPointGlobalRelativeCoclass s x d z) =
        analyticComponentPointRelativeCoclass s x d z := by
  let Y := TopCat.of (ComplexPoint X s)
  let S := cycleComponentAnalyticClosedSupport s x
  let y := cycleComponentMap s x z
  have hy : y ∈ S := range_cycleComponentMap_subset s x ⟨z, rfl⟩
  have h := congrArg (fun e => e (analyticPointLocalCoclass s d y))
    (relativeCohomologyMap_comp ℚ (2 * d)
      (topOpenNeighborhoodSupportPairIso Y S).hom
      (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr hy)))
  have h' := congrArg (fun f => relativeCohomologyMap ℚ (2 * d) f
      (analyticPointLocalCoclass s d y))
    (topOpenNeighborhoodSupportPairIso_toPoint Y S y hy)
  exact h.symm.trans h'

/-- POSITIVE raw-cochain normalization: the literal supported-kernel point
target is the old exact point coclass included as an ordinary raw relative
cochain, then sent through actual sheafification and the ambient resolution. -/
theorem analyticComponentPointPositiveKernelClass_raw_positive :
    analyticComponentPointPositiveKernelClass s x d z =
      (rationalCohomologyAddEquivAmbientInjectiveHomology s (2 * (d : ℤ))).symm
        (HomologicalComplex.homologyMap
          (globalRawToSingularSheafInt s ≫
            ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
              (TopCat.of (ComplexPoint X s))).mapHomologicalComplex (.up ℤ)).map
                (complexSingularToAmbientInjective s)) (2 * (d : ℤ))
          (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X s))
            (cycleComponentAnalyticClosedSupport s x).compl (2 * d)
            (analyticComponentPointGlobalRelativeCoclass s x d z))) := by
  unfold analyticComponentPointPositiveKernelClass analyticComponentPointSupportedInjectiveCoclass
  rw [← analyticComponentPointGlobalRelativeCoclass_top]
  have h := complexSupportInjectiveSectionCohomologyEquiv_inclusion_positive s
    (cycleComponentAnalyticClosedSupport s x) (2 * d)
    (analyticComponentPointGlobalRelativeCoclass s x d z)
  have h' := congrArg
    (rationalCohomologyAddEquivAmbientInjectiveHomology s (2 * (d : ℤ))).symm h
  exact h'

/-- The independent ordinary sign calculation specializes to the actual point
target. The negative sign is a theorem about the legacy cone convention. -/
theorem analyticComponentPointPositiveKernelClass_eq_neg_legacy :
    analyticComponentPointPositiveKernelClass s x d z =
      -(forgetSupport s (cycleComponentSupport s x) (2 * (d : ℤ))
        ((rationalCohomologyWithSupportAddEquivSingular s
          (cycleComponentSupport s x) (isClosed_cycleComponentSupport s x) (2 * d)).symm
            (analyticComponentPointGlobalRelativeCoclass s x d z))) := by
  unfold analyticComponentPointPositiveKernelClass analyticComponentPointSupportedInjectiveCoclass
  rw [← analyticComponentPointGlobalRelativeCoclass_top]
  exact complexSupportInjectiveSectionCohomologyEquiv_inclusion_eq_neg_legacy s
    (cycleComponentAnalyticClosedSupport s x) (2 * d)
    (analyticComponentPointGlobalRelativeCoclass s x d z)

/-- The ACTUAL general component class, with no point branch, has the positive
standard raw relative-cochain normalization at every point component. -/
theorem cycleComponentSheafClass_point_raw_positive (hx : Order.coheight x = d) :
    cycleComponentSheafClass s x (d := d) hx =
      (rationalCohomologyAddEquivAmbientInjectiveHomology s (2 * (d : ℤ))).symm
        (HomologicalComplex.homologyMap
          (globalRawToSingularSheafInt s ≫
            ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
              (TopCat.of (ComplexPoint X s))).mapHomologicalComplex (.up ℤ)).map
                (complexSingularToAmbientInjective s)) (2 * (d : ℤ))
          (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X s))
            (cycleComponentAnalyticClosedSupport s x).compl (2 * d)
            (analyticComponentPointGlobalRelativeCoclass s x d z))) := by
  rw [cycleComponentSheafClass_point_normalization s x d z hx,
    analyticComponentPointPositiveKernelClass_raw_positive]

/-- At the constructed geometric component point, the literal support-inclusion
class is the legacy supported generator's exact equality transport. -/
theorem analyticComponentPointGlobalRelativeCoclass_eq_maximalCodimensionSupportedGenerator
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : Order.coheight x = V.dimension) :
    analyticComponentPointGlobalRelativeCoclass V.structureMap x V.dimension
      (maximalCodimensionCycleComponentPoint V x) =
      maximalCodimensionSupportedGenerator V x hx := by
  exact enlargeSupport_eq_cast_of_eq ℚ (TopCat.of (ComplexPoint V.scheme V.structureMap))
    (maximalCodimensionCycleComponentSupport_eq_singleton V x hx).symm
    (Set.singleton_subset_iff.mpr (range_cycleComponentMap_subset V.structureMap x
      ⟨maximalCodimensionCycleComponentPoint V x, rfl⟩)) (2 * V.dimension)
    (analyticPointLocalCoclass V.structureMap V.dimension
      (cycleComponentMap V.structureMap x (maximalCodimensionCycleComponentPoint V x)))

set_option maxRecDepth 4096 in
/-- The legacy component comparison is the literal existing Betti-support
comparison, after its already proved supported-generator normalization. -/
theorem maximalCodimensionComponentClass_eq_directLegacyPoint
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : Order.coheight x = V.dimension) :
    maximalCodimensionComponentClass V x hx =
      forgetSupport V.structureMap (cycleComponentSupport V.structureMap x)
        (2 * (V.dimension : ℤ))
        ((rationalCohomologyWithSupportAddEquivSingular V.structureMap
          (cycleComponentSupport V.structureMap x)
          (isClosed_cycleComponentSupport V.structureMap x) (2 * V.dimension)).symm
            (maximalCodimensionSupportedGenerator V x hx)) := by
  rw [maximalCodimensionComponentClass_eq_forgetSupport_pointCoclass]
  rfl

/-- The independently constructed general point class is the NEGATIVE of the
legacy ordinary point class. This records the proved cone sign without changing
either definition or either exact local orientation. -/
theorem cycleComponentSheafClass_eq_neg_maximalCodimensionComponentClass
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : Order.coheight x = V.dimension) :
    cycleComponentSheafClass V.structureMap x (d := V.dimension) hx =
      -maximalCodimensionComponentClass V x hx := by
  rw [cycleComponentSheafClass_point_normalization V.structureMap x V.dimension
    (maximalCodimensionCycleComponentPoint V x) hx,
    analyticComponentPointPositiveKernelClass_eq_neg_legacy,
    analyticComponentPointGlobalRelativeCoclass_eq_maximalCodimensionSupportedGenerator V x hx,
    maximalCodimensionComponentClass_eq_directLegacyPoint]

/-- The entire integral point-cycle map, not just an individual generator,
has the independently proved negative legacy comparison. -/
theorem sheafCycleClassOnCycles_eq_neg_pointCycleClassOnCycles
    (V : DimensionedSmoothProjectiveComplexVariety) :
    sheafCycleClassOnCycles V V.dimension = -pointCycleClassOnCycles V := by
  have h : (fun (x : V.scheme) (hx : Order.coheight x = V.dimension) =>
      cycleComponentSheafClass V.structureMap x (d := V.dimension) hx) =
        fun x hx => -maximalCodimensionComponentClass V x hx := by
    funext x hx
    exact cycleComponentSheafClass_eq_neg_maximalCodimensionComponentClass V x hx
  unfold sheafCycleClassOnCycles pointCycleClassOnCycles
  rw [h, cycleClassOnCyclesOfComponents_neg]

/-- Scalar extension preserves the actual signed comparison on ALL rational
point cycles; in particular every finite rational combination has this sign. -/
theorem rationalSheafCycleClassOnCycles_eq_neg_rationalPointCycleClassOnCycles
    (V : DimensionedSmoothProjectiveComplexVariety) :
    rationalSheafCycleClassOnCycles V V.dimension = -rationalPointCycleClassOnCycles V := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q c
  change q • sheafCycleClassOnCycles V V.dimension c = -(q • pointCycleClassOnCycles V c)
  rw [sheafCycleClassOnCycles_eq_neg_pointCycleClassOnCycles]
  simp only [AddMonoidHom.neg_apply, smul_neg]

/-- A closed scheme point requires neither a supplied codimension proof nor a
chosen analytic point: both are constructed from the actual geometry. -/
theorem cycleComponentSheafClass_closedPoint_positiveKernel
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : IsClosed ({x} : Set V.scheme)) :
    let hcodim := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := V.structureMap) (d := V.dimension) x hx
    cycleComponentSheafClass V.structureMap x (d := V.dimension) hcodim =
      analyticComponentPointPositiveKernelClass V.structureMap x V.dimension
        (maximalCodimensionCycleComponentPoint V x) := by
  exact cycleComponentSheafClass_point_normalization V.structureMap x V.dimension
    (maximalCodimensionCycleComponentPoint V x) _

/-- The signed legacy comparison at a closed scheme point derives the needed
codimension from geometry. No point, purity, or comparison data are supplied. -/
theorem cycleComponentSheafClass_closedPoint_eq_neg_legacy
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : IsClosed ({x} : Set V.scheme)) :
    let hcodim := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := V.structureMap) (d := V.dimension) x hx
    cycleComponentSheafClass V.structureMap x (d := V.dimension) hcodim =
      -maximalCodimensionComponentClass V x hcodim := by
  exact cycleComponentSheafClass_eq_neg_maximalCodimensionComponentClass V x _

end AlgebraicGeometry.ComplexPoint
