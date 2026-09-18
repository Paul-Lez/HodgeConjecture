/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportHypercohomology
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.FundamentalClass
public import Other.AlgebraicGeometry.Cycle.Component.BorelMoore
public import Other.AlgebraicGeometry.Cycle.Component.PointPurity
public import Other.AlgebraicGeometry.SmoothProjectiveVariety
public import Other.AlgebraicGeometry.Cycle.ClassOnCycles
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact
import Lean.Elab.Tactic.Omega
public import Other.AlgebraicGeometry.Cohomology.SupportHypercohomology
public import Other.AlgebraicGeometry.Cycle.Local.Purity
public import Other.AlgebraicGeometry.Cycle.Support

/-!
# Borel--Moore comparison scaffolds for cycle classes

For an irreducible codimension-`p` component `Z` of a smooth projective complex `d`-fold, the
complex orientation fixes a unique class

`[Z]ᴮᴹ ∈ Hᴮᴹ_{2(d-p)}(Z; ℚ)`.

Transporting this class to ambient supported cohomology requires normalized
Alexander--Poincaré duality. Mathlib does not yet provide the Thom/costalk operation needed to
state that normalization without additional input. This file therefore separates:

* an explicitly auxiliary, rescalable comparison API;
* a conditional complex-oriented API normalized by a named local Thom-cap operation and a
  commuting-square theorem; and
* the maximal-codimension point case, where the supported point coclass is independently
  constructed and the normalized comparison is unconditional.

Nothing produced solely from an auxiliary comparison is claimed to be the standard cycle class.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular


/-- Auxiliary comparison data for one codimension-`p` closed subvariety.

The Borel--Moore class is exactly normalized, but `auxiliaryComparison` is an arbitrary linear
equivalence and may be rescaled. Consequently its images below are explicitly auxiliary and are
not asserted to be the standard supported or ordinary cycle classes. -/
structure AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = p) where
  /-- The uniquely normalized Borel--Moore fundamental class construction. -/
  borelMoore : RationalClosedEmbeddingBorelMooreData V i d p hi
  /-- An unnormalized, rescalable comparison with supported cohomology. -/
  auxiliaryComparison :
    ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p)

namespace AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData

variable {V : SmoothProjectiveComplexVariety} {d p : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over} [IsIntegral Y.left] [IsClosedImmersion i.left] {hi : coheight (closedEmbeddingGenericPoint i) = p}

/-- The exact Borel--Moore fundamental class of the component. -/
def fundamentalClass
    (D : AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi) :
    ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - p)) :=
  D.borelMoore.fundamentalClass

/-- The comparison-dependent singular supported class. -/
def auxiliarySingularSupportedClass
    (D : AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi) :
    RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p) :=
  D.auxiliaryComparison D.fundamentalClass

/-- The comparison between rational constant-sheaf cohomology with support and rational
singular cohomology with support in the component's cycle-class degree. -/
def supportedComparison
    (_D : AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi) :
    RationalCohomologyWithSupport V.over
        (closedEmbeddingSupport i) (2 * (p : ℤ)) ≃+
      RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p) :=
  letI : TopologicalSpace V.analyticPoint := Point.analyticTopology
  letI : T2Space V.analyticPoint := inferInstance
  letI : CompactSpace V.analyticPoint := inferInstance
  letI : ChartedSpace (Fin d → ℂ) V.analyticPoint :=
    inferInstance
  letI : ∀ U : Opens V.analyticPoint, ParacompactSpace U := fun U =>
    opens_paracompactSpace_of_compact_chartedSpace
      (H := Fin d → ℂ) U
  (show ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) by omega) ▸
    rationalCohomologyWithSupportAddEquivSingular
      V.over
        (closedEmbeddingSupport i)
        (isClosed_closedEmbeddingSupport i) (2 * p)

/-- The supported comparison depends only on the component, not on the surrounding data. -/
lemma supportedComparison_eq
    (D D' : AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi) :
    D.supportedComparison = D'.supportedComparison := rfl

/-- The comparison-dependent rational constant-sheaf class with support. -/
def auxiliarySupportedClass
    (D : AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi) :
    RationalCohomologyWithSupport V.over
      (closedEmbeddingSupport i) (2 * (p : ℤ)) :=
  D.supportedComparison.symm D.auxiliarySingularSupportedClass

/-- The comparison-dependent ordinary rational cohomology class. -/
def auxiliaryOrdinaryClass
    (D : AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi) :
    H^(2 * (p : ℤ))(V.over; ℚ) :=
  forgetSupport V.over
    (closedEmbeddingSupport i) (2 * (p : ℤ))
    D.auxiliarySupportedClass

end AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData

/-! ### Conditional complex-oriented normalization -/

/-- The missing local Thom-cap input for a general component.

`capWithAmbientComplexOrientation` is intended to be the triad-cap/Thom/costalk operation already
specialized to the exact ambient complex orientation. `local_ext` is the corresponding purity or
local-detection theorem. Neither field is constructed here, and canonicity is conditional on
instantiating this structure with the actual geometric operations. -/
structure RationalClosedEmbeddingLocalThomCapInput
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = p) where
  /-- Cap a supported coclass with the ambient complex orientation and restrict to the component's
  local homology at a smooth point. -/
  capWithAmbientComplexOrientation :
    ∀ (z : ClosedEmbeddingAnalyticPoint V i)
      (_hz : z ∈ closedEmbeddingSmoothAnalyticLocus i),
      RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p) →ₗ[ℚ]
        RelativeHomology ℚ (pointComplementPair z) (2 * (d - p))
  /-- Supported classes are detected by all complex-oriented local Thom-cap evaluations. -/
  local_ext : ∀
      (α β : RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p)),
    (∀ (z : ClosedEmbeddingAnalyticPoint V i)
      (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i),
      capWithAmbientComplexOrientation z hz α =
        capWithAmbientComplexOrientation z hz β) → α = β

/-- A comparison is complex-oriented when its local Thom-cap square agrees with the already
constructed Borel--Moore localization map at every smooth point. -/
def IsComplexOrientedAlexanderPoincare
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over} [IsIntegral Y.left] [IsClosedImmersion i.left] {hi : coheight (closedEmbeddingGenericPoint i) = p}
    (_D : RationalClosedEmbeddingBorelMooreData V i d p hi)
    (T : RationalClosedEmbeddingLocalThomCapInput V d p i hi)
    (e : ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p)) : Prop :=
  ∀ (c) (z : ClosedEmbeddingAnalyticPoint V i)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i),
    T.capWithAmbientComplexOrientation z hz (e c) =
      closedEmbeddingBorelMooreToLocal ℚ V i (2 * (d - p)) z c

/-- For a fixed local Thom-cap input, its square and local detection determine the entire
comparison, not merely the image of the fundamental class. This does not compare different
choices of the supplied Thom-cap operation. -/
theorem complexOrientedAlexanderPoincare_unique
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over} [IsIntegral Y.left] [IsClosedImmersion i.left] {hi : coheight (closedEmbeddingGenericPoint i) = p}
    (D : RationalClosedEmbeddingBorelMooreData V i d p hi)
    (T : RationalClosedEmbeddingLocalThomCapInput V d p i hi)
    (e e' : ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p))
    (he : IsComplexOrientedAlexanderPoincare D T e)
    (he' : IsComplexOrientedAlexanderPoincare D T e') : e = e' :=
  LinearEquiv.ext fun c ↦ T.local_ext _ _ fun z hz ↦ (he c z hz).trans (he' c z hz).symm

/-- Conditional normalized component cycle-class data.

The comparison is required to satisfy a square relative to the supplied local Thom-cap maps.
Those maps, their local-detection theorem, the comparison, and the existence and uniqueness
of a global Borel--Moore fundamental class remain inputs. Only the exact local orientation
itself is already constructed here. Simultaneously rescaling the supplied comparison and
Thom-cap maps is not excluded; canonicity requires instantiating them geometrically. -/
structure ComplexOrientedRationalClosedEmbeddingClassData
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = p) where
  borelMoore : RationalClosedEmbeddingBorelMooreData V i d p hi
  localThomCap : RationalClosedEmbeddingLocalThomCapInput V d p i hi
  comparison :
    ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p)
  comparison_isComplexOriented :
    IsComplexOrientedAlexanderPoincare borelMoore localThomCap comparison

namespace ComplexOrientedRationalClosedEmbeddingClassData

variable {V : SmoothProjectiveComplexVariety} {d p : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over} [IsIntegral Y.left] [IsClosedImmersion i.left] {hi : coheight (closedEmbeddingGenericPoint i) = p}

/-- The exact compactification-relative Borel--Moore fundamental class. -/
def fundamentalClass (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi) :=
  D.borelMoore.fundamentalClass

/-- The normalized Alexander--Poincaré comparison, conditional on the supplied Thom-cap square. -/
def alexanderPoincare
    (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi) :=
  D.comparison

/-- The singular supported fundamental class normalized by the local Thom-cap square. -/
def supportedFundamentalClass
    (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi) :=
  D.alexanderPoincare D.fundamentalClass

/-- The normalized supported class has the exact constructed complex local orientation at every
smooth point. -/
theorem alexanderPoincare_fundamentalClass_local
    (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi)
    (z : ClosedEmbeddingAnalyticPoint V i)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    D.localThomCap.capWithAmbientComplexOrientation z hz D.supportedFundamentalClass =
      closedEmbeddingComplexLocalOrientation V i d p hi z hz :=
  (D.comparison_isComplexOriented D.fundamentalClass z hz).trans
    (D.borelMoore.toLocal_fundamentalClass z hz)

/-- Local Thom-cap normalization uniquely determines the supported fundamental class. -/
theorem supportedFundamentalClass_unique
    (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi)
    (α : RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * p))
    (hα : ∀ (z : ClosedEmbeddingAnalyticPoint V i)
      (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i),
      D.localThomCap.capWithAmbientComplexOrientation z hz α =
        closedEmbeddingComplexLocalOrientation V i d p hi z hz) :
    α = D.supportedFundamentalClass :=
  D.localThomCap.local_ext _ _ fun z hz ↦
    (hα z hz).trans (D.alexanderPoincare_fundamentalClass_local z hz).symm

/-- Forgetting the conditional wrapper recovers only auxiliary comparison data. -/
def toAuxiliaryComparisonData
    (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi) :
    AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi where
  borelMoore := D.borelMoore
  auxiliaryComparison := D.alexanderPoincare

/-- The rational constant-sheaf supported fundamental class, obtained through the proved singular
comparison after local Thom-cap normalization. -/
def constantSheafSupportedFundamentalClass
    (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi) :
    RationalCohomologyWithSupport V.over
      (closedEmbeddingSupport i) (2 * (p : ℤ)) :=
  D.toAuxiliaryComparisonData.supportedComparison.symm D.supportedFundamentalClass

/-- The conditional normalized ordinary rational component class. -/
def ordinaryFundamentalClass
    (D : ComplexOrientedRationalClosedEmbeddingClassData V d p i hi) :
    H^(2 * (p : ℤ))(V.over; ℚ) :=
  forgetSupport V.over
    (closedEmbeddingSupport i) (2 * (p : ℤ))
      D.constantSheafSupportedFundamentalClass

end ComplexOrientedRationalClosedEmbeddingClassData

/-- Complex-oriented component class data yields auxiliary comparison data by forgetting the
Thom-cap square, so inhabitation transfers along `toAuxiliaryComparisonData`. -/
theorem nonempty_auxiliaryRationalClosedEmbeddingBorelMooreComparisonData_of_complexOriented
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over} [IsIntegral Y.left] [IsClosedImmersion i.left] {hi : coheight (closedEmbeddingGenericPoint i) = p}
    (h : Nonempty (ComplexOrientedRationalClosedEmbeddingClassData V d p i hi)) :
    Nonempty (AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d p i hi) :=
  h.map ComplexOrientedRationalClosedEmbeddingClassData.toAuxiliaryComparisonData

/-! ### The complete construction in maximal codimension -/

/-- A canonical smooth analytic point of a maximal-codimension closed subvariety. -/
def maximalCodimensionClosedEmbeddingPoint
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    ClosedEmbeddingAnalyticPoint V i :=
  Classical.choose (exists_closedEmbedding_smooth_complexPoint i)

/-- The selected point belongs to the smooth analytic locus. -/
lemma maximalCodimensionClosedEmbeddingPoint_mem_smooth
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    maximalCodimensionClosedEmbeddingPoint V i ∈
      closedEmbeddingSmoothAnalyticLocus i :=
  Classical.choose_spec (exists_closedEmbedding_smooth_complexPoint i)

/-- A maximal-codimension subvariety's support is the singleton containing its selected point. -/
lemma maximalCodimensionClosedEmbeddingSupport_eq_singleton
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    closedEmbeddingSupport i =
      {Point.map i
        (maximalCodimensionClosedEmbeddingPoint V i)} :=
  closedEmbeddingSupport_eq_singleton_of_coheight_eq_dimension
    V.over d i hi
    (maximalCodimensionClosedEmbeddingPoint V i)

/-- The normalized ambient point coclass, transported to the subvariety support. -/
def maximalCodimensionSupportedGenerator
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * d) :=
  let F := fun Z : Set V.analyticPoint ↦ ↥(CohomologyWithSupport ℚ
    (@TopCat.of V.analyticPoint Point.analyticTopology) Z (2 * d))
  LinearEquiv.cast (R := ℚ) (M := F)
    (maximalCodimensionClosedEmbeddingSupport_eq_singleton V d i hi).symm
      (analyticPointLocalCoclass V.over d
        (Point.map i
          (maximalCodimensionClosedEmbeddingPoint V i)))

/-- The supported point coclass generates the maximal-codimension target. -/
lemma span_maximalCodimensionSupportedGenerator_eq_top
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    Submodule.span ℚ {maximalCodimensionSupportedGenerator V d i hi} = ⊤ := by
  let z := maximalCodimensionClosedEmbeddingPoint V i
  let y := Point.map i z
  let F := fun Z : Set V.analyticPoint ↦ ↥(CohomologyWithSupport ℚ
    (@TopCat.of V.analyticPoint Point.analyticTopology) Z (2 * d))
  let e := LinearEquiv.cast (R := ℚ) (M := F)
    (maximalCodimensionClosedEmbeddingSupport_eq_singleton V d i hi).symm
  change Submodule.span ℚ {e
    (analyticPointLocalCoclass V.over d y)} = ⊤
  rw [Submodule.span_singleton_eq_top_iff]
  intro w
  obtain ⟨a, ha⟩ :=
    (Submodule.span_singleton_eq_top_iff ℚ
      (analyticPointLocalCoclass V.over d y)).mp
        (span_analyticPointLocalCoclass_eq_top V.over d y)
        (e.symm w)
  refine ⟨a, ?_⟩
  rw [← e.map_smul, ha, e.apply_symm_apply]

/-- The supported point coclass is nonzero. -/
lemma maximalCodimensionSupportedGenerator_ne_zero
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    maximalCodimensionSupportedGenerator V d i hi ≠ 0 := by
  let z := maximalCodimensionClosedEmbeddingPoint V i
  let y := Point.map i z
  let F := fun Z : Set V.analyticPoint ↦ ↥(CohomologyWithSupport ℚ
    (@TopCat.of V.analyticPoint Point.analyticTopology) Z (2 * d))
  let e := LinearEquiv.cast (R := ℚ) (M := F)
    (maximalCodimensionClosedEmbeddingSupport_eq_singleton V d i hi).symm
  change e (analyticPointLocalCoclass V.over d y) ≠ 0
  have hsource :
      analyticPointLocalCoclass V.over d y ≠ 0 := by
    intro hzero
    have hone :=
      analyticPointLocalCoclass_apply_localClass V.over d y
    unfold analyticPointLocalCoclassDual at hone
    rw [hzero, map_zero, LinearMap.zero_apply] at hone
    exact zero_ne_one hone
  intro hzero
  exact hsource (e.injective (by simpa using hzero))

/-- The explicitly constructed Borel--Moore fundamental class of a maximal-codimension
component. -/
def maximalCodimensionBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - d)) :=
  (rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi).fundamentalClass

/-- The maximal-codimension Borel--Moore fundamental class is nonzero. -/
lemma maximalCodimensionBorelMooreFundamentalClass_ne_zero
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    maximalCodimensionBorelMooreFundamentalClass V d i hi ≠ 0 := by
  let z := maximalCodimensionClosedEmbeddingPoint V i
  let hz := maximalCodimensionClosedEmbeddingPoint_mem_smooth V i
  let D := rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi
  let : TopologicalSpace (ClosedEmbeddingAnalyticPoint V i) := Point.analyticTopology
  let : Subsingleton (ClosedEmbeddingAnalyticPoint V i) :=
    closedEmbeddingAnalyticPoint_subsingleton_of_coheight_eq_dimension V i d hi
  let e := compactificationBorelMooreToLocalEquivOfSubsingleton
    ℚ z (2 * (d - d))
  change D.fundamentalClass ≠ 0
  intro hzero
  have hlocal := D.toLocal_fundamentalClass z hz
  change e D.fundamentalClass = D.localOrientation z hz at hlocal
  rw [hzero, map_zero] at hlocal
  exact (closedEmbeddingComplexLocalOrientation_ne_zero V i d d hi z hz) hlocal.symm

/-- The maximal-codimension Borel--Moore fundamental class generates its homology group. -/
lemma span_maximalCodimensionBorelMooreFundamentalClass_eq_top
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    Submodule.span ℚ {maximalCodimensionBorelMooreFundamentalClass V d i hi} = ⊤ := by
  let z := maximalCodimensionClosedEmbeddingPoint V i
  let hz := maximalCodimensionClosedEmbeddingPoint_mem_smooth V i
  let D := rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi
  let : TopologicalSpace (ClosedEmbeddingAnalyticPoint V i) := Point.analyticTopology
  let : Subsingleton (ClosedEmbeddingAnalyticPoint V i) :=
    closedEmbeddingAnalyticPoint_subsingleton_of_coheight_eq_dimension V i d hi
  let e := compactificationBorelMooreToLocalEquivOfSubsingleton
    ℚ z (2 * (d - d))
  change Submodule.span ℚ {D.fundamentalClass} = ⊤
  rw [Submodule.span_singleton_eq_top_iff]
  intro w
  obtain ⟨a, ha⟩ :=
    (Submodule.span_singleton_eq_top_iff ℚ (D.localOrientation z hz)).mp
      (D.span_localOrientation_eq_top z hz) (e w)
  refine ⟨a, ?_⟩
  have hlocal : e D.fundamentalClass = D.localOrientation z hz := by
    change closedEmbeddingBorelMooreToLocal ℚ V i
      (2 * (d - d)) z D.fundamentalClass = D.localOrientation z hz
    exact D.toLocal_fundamentalClass z hz
  apply e.injective
  rw [e.map_smul, hlocal, ha]

/-- Alexander--Poincaré duality for a zero-dimensional component, characterized by sending
its oriented Borel--Moore generator to the normalized ambient point coclass. -/
def maximalCodimensionAlexanderDuality
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - d)) ≃ₗ[ℚ]
      RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * d) :=
  linearEquivOfNormalizedGenerators
    (maximalCodimensionBorelMooreFundamentalClass V d i hi)
    (maximalCodimensionBorelMooreFundamentalClass_ne_zero V d i hi)
    (span_maximalCodimensionBorelMooreFundamentalClass_eq_top V d i hi)
    (maximalCodimensionSupportedGenerator V d i hi)
    (maximalCodimensionSupportedGenerator_ne_zero V d i hi)
    (span_maximalCodimensionSupportedGenerator_eq_top V d i hi)

/-- Maximal-codimension duality sends the oriented Borel--Moore generator to the normalized
ambient point coclass. -/
@[simp] lemma maximalCodimensionAlexanderDuality_fundamentalClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    maximalCodimensionAlexanderDuality V d i hi
        (maximalCodimensionBorelMooreFundamentalClass V d i hi) =
      maximalCodimensionSupportedGenerator V d i hi :=
  linearEquivOfNormalizedGenerators_apply_generator _ _ _ _ _ _

/-- The point-case duality equivalence is uniquely determined by its orientation
normalization. -/
lemma maximalCodimensionAlexanderDuality_unique
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d)
    (e : ClosedEmbeddingBorelMooreHomology ℚ V i (2 * (d - d)) ≃ₗ[ℚ]
        RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * d))
    (he : e (maximalCodimensionBorelMooreFundamentalClass V d i hi) =
      maximalCodimensionSupportedGenerator V d i hi) :
    e = maximalCodimensionAlexanderDuality V d i hi :=
  linearEquivOfNormalizedGenerators_unique
    (maximalCodimensionBorelMooreFundamentalClass V d i hi)
    (maximalCodimensionBorelMooreFundamentalClass_ne_zero V d i hi)
    (span_maximalCodimensionBorelMooreFundamentalClass_eq_top V d i hi)
    (maximalCodimensionSupportedGenerator V d i hi)
    (maximalCodimensionSupportedGenerator_ne_zero V d i hi)
    (span_maximalCodimensionSupportedGenerator_eq_top V d i hi) e he

/-- In maximal codimension, cap with the ambient complex orientation is the uniquely normalized
equivalence from the point-supported coclass to local homology.  The one-dimensional argument is
used only in this explicitly labeled point case. -/
def maximalCodimensionLocalThomCapEquiv
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d)
    (z : ClosedEmbeddingAnalyticPoint V i)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    RationalSingularClosedEmbeddingCohomologyWithSupport i (2 * d) ≃ₗ[ℚ]
      RelativeHomology ℚ (pointComplementPair z) (2 * (d - d)) :=
  let D := rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi
  linearEquivOfNormalizedGenerators
    (maximalCodimensionSupportedGenerator V d i hi)
    (maximalCodimensionSupportedGenerator_ne_zero V d i hi)
    (span_maximalCodimensionSupportedGenerator_eq_top V d i hi)
    (D.localOrientation z hz)
    (closedEmbeddingComplexLocalOrientation_ne_zero V i d d hi z hz)
    (D.span_localOrientation_eq_top z hz)

/-- Point-case Thom cap sends the normalized ambient coclass to the exact complex local class. -/
@[simp] lemma maximalCodimensionLocalThomCapEquiv_supportedGenerator
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d)
    (z : ClosedEmbeddingAnalyticPoint V i)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    maximalCodimensionLocalThomCapEquiv V d i hi z hz
        (maximalCodimensionSupportedGenerator V d i hi) =
      closedEmbeddingComplexLocalOrientation V i d d hi z hz := by
  let D := rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi
  change maximalCodimensionLocalThomCapEquiv V d i hi z hz
      (maximalCodimensionSupportedGenerator V d i hi) = D.localOrientation z hz
  exact linearEquivOfNormalizedGenerators_apply_generator
    (maximalCodimensionSupportedGenerator V d i hi)
    (maximalCodimensionSupportedGenerator_ne_zero V d i hi)
    (span_maximalCodimensionSupportedGenerator_eq_top V d i hi)
    (D.localOrientation z hz)
    (closedEmbeddingComplexLocalOrientation_ne_zero V i d d hi z hz)
    (D.span_localOrientation_eq_top z hz)

/-- The actual local Thom-cap package is completely constructed for a point component. -/
def maximalCodimensionLocalThomCapInput
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    RationalClosedEmbeddingLocalThomCapInput V d d i hi where
  capWithAmbientComplexOrientation z hz :=
    (maximalCodimensionLocalThomCapEquiv V d i hi z hz).toLinearMap
  local_ext α β h := by
    let z := maximalCodimensionClosedEmbeddingPoint V i
    let hz := maximalCodimensionClosedEmbeddingPoint_mem_smooth V i
    exact (maximalCodimensionLocalThomCapEquiv V d i hi z hz).injective (h z hz)

/-- A maximal-codimension component carries a local Thom-cap package, built from the normalized
point-coclass equivalence of `maximalCodimensionLocalThomCapEquiv`. -/
theorem nonempty_rationalClosedEmbeddingLocalThomCapInput_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    Nonempty (RationalClosedEmbeddingLocalThomCapInput V d d i hi) :=
  ⟨maximalCodimensionLocalThomCapInput V d i hi⟩

/-- The constructed point-case duality satisfies the full exact local Thom-cap square. -/
lemma maximalCodimensionAlexanderDuality_isComplexOriented
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    IsComplexOrientedAlexanderPoincare
      (rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi)
      (maximalCodimensionLocalThomCapInput V d i hi)
      (maximalCodimensionAlexanderDuality V d i hi) := by
  intro c z hz
  let D := rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi
  change maximalCodimensionLocalThomCapEquiv V d i hi z hz
      (maximalCodimensionAlexanderDuality V d i hi c) =
    closedEmbeddingBorelMooreToLocal ℚ V i (2 * (d - d)) z c
  obtain ⟨a, ha⟩ :=
    (Submodule.span_singleton_eq_top_iff ℚ
      (maximalCodimensionBorelMooreFundamentalClass V d i hi)).mp
        (span_maximalCodimensionBorelMooreFundamentalClass_eq_top V d i hi) c
  rw [← ha, map_smul, map_smul, map_smul,
    maximalCodimensionAlexanderDuality_fundamentalClass,
    maximalCodimensionLocalThomCapEquiv_supportedGenerator]
  simpa only [RationalClosedEmbeddingBorelMooreData.localOrientation,
    maximalCodimensionBorelMooreFundamentalClass] using
      congrArg (a • ·) (D.toLocal_fundamentalClass z hz).symm

/-- The fully constructed point case, now expressed through the same locally normalized interface
used by the conditional general theory. -/
def maximalCodimensionComplexOrientedComponentClassData
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    ComplexOrientedRationalClosedEmbeddingClassData V d d i hi where
  borelMoore := rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi
  localThomCap := maximalCodimensionLocalThomCapInput V d i hi
  comparison := maximalCodimensionAlexanderDuality V d i hi
  comparison_isComplexOriented :=
    maximalCodimensionAlexanderDuality_isComplexOriented V d i hi

/-- The normalized-interface point class is exactly the previously constructed ambient point
coclass, not merely a nonzero rational multiple of it. -/
@[simp] lemma maximalCodimensionComplexOrientedComponentClassData_supported
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    (maximalCodimensionComplexOrientedComponentClassData V d i hi).supportedFundamentalClass =
      maximalCodimensionSupportedGenerator V d i hi :=
  maximalCodimensionAlexanderDuality_fundamentalClass V d i hi

/-- A maximal-codimension component carries complex-oriented class data, with the Thom-cap square
supplied by `maximalCodimensionAlexanderDuality_isComplexOriented`. -/
theorem nonempty_complexOrientedRationalClosedEmbeddingClassData_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    Nonempty (ComplexOrientedRationalClosedEmbeddingClassData V d d i hi) :=
  ⟨maximalCodimensionComplexOrientedComponentClassData V d i hi⟩

/-- The complete Borel--Moore and point-duality package in maximal codimension. -/
def auxiliaryRationalClosedEmbeddingBorelMooreComparisonDataOfCoheightEqDimension
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d d i hi where
  borelMoore := rationalClosedEmbeddingBorelMooreDataOfCoheightEqDimension V i d hi
  auxiliaryComparison := maximalCodimensionAlexanderDuality V d i hi

/-- The supported class in the maximal-codimension package is the normalized point coclass. -/
@[simp] lemma auxiliaryRationalClosedEmbeddingBorelMooreComparisonDataOfCoheightEqDimension_supported
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData.auxiliarySingularSupportedClass
        (auxiliaryRationalClosedEmbeddingBorelMooreComparisonDataOfCoheightEqDimension V d i hi) =
      maximalCodimensionSupportedGenerator V d i hi :=
  maximalCodimensionAlexanderDuality_fundamentalClass V d i hi

/-- A maximal-codimension component carries auxiliary comparison data, with the comparison given
by the normalized point-case Alexander duality. -/
theorem nonempty_auxiliaryRationalClosedEmbeddingBorelMooreComparisonData_of_coheight_eq_dimension
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    Nonempty (AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData V d d i hi) :=
  ⟨auxiliaryRationalClosedEmbeddingBorelMooreComparisonDataOfCoheightEqDimension V d i hi⟩

/-- The fully constructed ordinary class of a maximal-codimension irreducible component. -/
def maximalCodimensionComponentClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    H^(2 * (d : ℤ))(V.over; ℚ) :=
  AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData.auxiliaryOrdinaryClass
    (auxiliaryRationalClosedEmbeddingBorelMooreComparisonDataOfCoheightEqDimension V d i hi)

/-- The maximal-codimension ordinary class is obtained by transporting the normalized singular
point coclass through the proved support comparison and then forgetting support. -/
lemma maximalCodimensionComponentClass_eq_forgetSupport_pointCoclass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over) [IsIntegral Y.left] [IsClosedImmersion i.left] (hi : coheight (closedEmbeddingGenericPoint i) = d) :
    maximalCodimensionComponentClass V d i hi =
      forgetSupport V.over
        (closedEmbeddingSupport i)
        (2 * (d : ℤ))
        ((auxiliaryRationalClosedEmbeddingBorelMooreComparisonDataOfCoheightEqDimension V d i hi).supportedComparison.symm
          (maximalCodimensionSupportedGenerator V d i hi)) := by
  unfold maximalCodimensionComponentClass
  rw [AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData.auxiliaryOrdinaryClass,
    AuxiliaryRationalClosedEmbeddingBorelMooreComparisonData.auxiliarySupportedClass,
    auxiliaryRationalClosedEmbeddingBorelMooreComparisonDataOfCoheightEqDimension_supported]

end AlgebraicGeometry.ComplexPoint
