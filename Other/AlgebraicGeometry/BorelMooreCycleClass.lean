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

public import HodgeConjecture.Definitions.AlgebraicGeometry.BettiSupportSingularHypercohomologyComparison
public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleClass
public import Other.AlgebraicGeometry.CycleComponentBorelMoore
public import Other.AlgebraicGeometry.CycleComponentPointPurity
public import Other.AlgebraicGeometry.DimensionedSmoothProjective
public import Other.AlgebraicGeometry.PrincipalDivisorCycleClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationParacompact
import Lean.Elab.Tactic.Omega

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

noncomputable local instance cycleComponentBorelMooreClassTopology
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    TopologicalSpace (CycleComponentAnalyticPoint V x) :=
  Point.analyticTopology

/-- Auxiliary comparison data for one irreducible codimension-`p` component.

The Borel--Moore class is exactly normalized, but `auxiliaryComparison` is an arbitrary linear
equivalence and may be rescaled. Consequently its images below are explicitly auxiliary and are
not asserted to be the standard supported or ordinary cycle classes. -/
structure AuxiliaryRationalCycleComponentBorelMooreComparisonData
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = p) where
  /-- The uniquely normalized Borel--Moore fundamental class construction. -/
  borelMoore : RationalCycleComponentBorelMooreData V x d p hx
  /-- An unnormalized, rescalable comparison with supported cohomology. -/
  auxiliaryComparison :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularComponentCohomologyWithSupport V.over x (2 * p)

namespace AuxiliaryRationalCycleComponentBorelMooreComparisonData

variable {V : SmoothProjectiveComplexVariety} {d p : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  {x : V.scheme} {hx : coheight x = p}

/-- The exact Borel--Moore fundamental class of the component. -/
def fundamentalClass
    (D : AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx) :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) :=
  D.borelMoore.fundamentalClass

/-- The comparison-dependent singular supported class. -/
def auxiliarySingularSupportedClass
    (D : AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx) :
    RationalSingularComponentCohomologyWithSupport V.over x (2 * p) :=
  D.auxiliaryComparison D.fundamentalClass

/-- The comparison between rational constant-sheaf cohomology with support and rational
singular cohomology with support in the component's cycle-class degree. -/
def supportedComparison
    (_D : AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx) :
    RationalCohomologyWithSupport V.over
        (cycleComponentSupport V.over x) (2 * (p : ℤ)) ≃+
      RationalSingularComponentCohomologyWithSupport V.over x (2 * p) := by
  let : TopologicalSpace V.analyticPoint := Point.analyticTopology
  let : T2Space V.analyticPoint := inferInstance
  let : CompactSpace V.analyticPoint := inferInstance
  let : ChartedSpace (Fin d → ℂ) V.analyticPoint :=
    inferInstance
  let : ∀ U : Opens V.analyticPoint, ParacompactSpace U := fun U =>
    opens_paracompactSpace_of_compact_chartedSpace
      (H := Fin d → ℂ) U
  rw [show 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) by omega]
  exact rationalCohomologyWithSupportAddEquivSingular
    V.over
      (cycleComponentSupport V.over x)
      (isClosed_cycleComponentSupport V.over x) (2 * p)

/-- The comparison-dependent rational constant-sheaf class with support. -/
def auxiliarySupportedClass
    (D : AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx) :
    RationalCohomologyWithSupport V.over
      (cycleComponentSupport V.over x) (2 * (p : ℤ)) :=
  D.supportedComparison.symm D.auxiliarySingularSupportedClass

/-- The comparison-dependent ordinary rational cohomology class. -/
def auxiliaryOrdinaryClass
    (D : AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx) :
    H^(2 * (p : ℤ))(V.over; ℚ) :=
  forgetSupport V.over
    (cycleComponentSupport V.over x) (2 * (p : ℤ))
    D.auxiliarySupportedClass

end AuxiliaryRationalCycleComponentBorelMooreComparisonData

/-! ### Conditional complex-oriented normalization -/

/-- The missing local Thom-cap input for a general component.

`capWithAmbientComplexOrientation` is intended to be the triad-cap/Thom/costalk operation already
specialized to the exact ambient complex orientation. `local_ext` is the corresponding purity or
local-detection theorem. Neither field is constructed here, and canonicity is conditional on
instantiating this structure with the actual geometric operations. -/
structure RationalCycleComponentLocalThomCapInput
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = p) where
  /-- Cap a supported coclass with the ambient complex orientation and restrict to the component's
  local homology at a smooth point. -/
  capWithAmbientComplexOrientation :
    ∀ (z : CycleComponentAnalyticPoint V x)
      (_hz : z ∈ cycleComponentSmoothAnalyticLocus
        V.over x),
      RationalSingularComponentCohomologyWithSupport V.over x (2 * p) →ₗ[ℚ]
        RelativeHomology ℚ (pointComplementPair z) (2 * (d - p))
  /-- Supported classes are detected by all complex-oriented local Thom-cap evaluations. -/
  local_ext : ∀
      (α β : RationalSingularComponentCohomologyWithSupport V.over x (2 * p)),
    (∀ (z : CycleComponentAnalyticPoint V x)
      (hz : z ∈ cycleComponentSmoothAnalyticLocus
        V.over x),
      capWithAmbientComplexOrientation z hz α =
        capWithAmbientComplexOrientation z hz β) → α = β

/-- A comparison is complex-oriented when its local Thom-cap square agrees with the already
constructed Borel--Moore localization map at every smooth point. -/
def IsComplexOrientedAlexanderPoincare
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    {x : V.scheme} {hx : coheight x = p}
    (_D : RationalCycleComponentBorelMooreData V x d p hx)
    (T : RationalCycleComponentLocalThomCapInput V d p x hx)
    (e : CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularComponentCohomologyWithSupport V.over x (2 * p)) : Prop :=
  ∀ (c) (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x),
    T.capWithAmbientComplexOrientation z hz (e c) =
      cycleComponentBorelMooreToLocal ℚ V x (2 * (d - p)) z c

/-- For a fixed local Thom-cap input, its square and local detection determine the entire
comparison, not merely the image of the fundamental class. This does not compare different
choices of the supplied Thom-cap operation. -/
theorem complexOrientedAlexanderPoincare_unique
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    {x : V.scheme} {hx : coheight x = p}
    (D : RationalCycleComponentBorelMooreData V x d p hx)
    (T : RationalCycleComponentLocalThomCapInput V d p x hx)
    (e e' : CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularComponentCohomologyWithSupport V.over x (2 * p))
    (he : IsComplexOrientedAlexanderPoincare D T e)
    (he' : IsComplexOrientedAlexanderPoincare D T e') : e = e' :=
  LinearEquiv.ext fun c ↦ T.local_ext _ _ fun z hz ↦ (he c z hz).trans (he' c z hz).symm

/-- Conditional normalized component cycle-class data.

The comparison is required to satisfy a square relative to the supplied local Thom-cap maps.
Those maps, their local-detection theorem, the comparison, and the existence and uniqueness
of a global Borel--Moore fundamental class remain inputs. Only the exact local orientation
itself is already constructed here. Simultaneously rescaling the supplied comparison and
Thom-cap maps is not excluded; canonicity requires instantiating them geometrically. -/
structure ComplexOrientedRationalCycleComponentClassData
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = p) where
  borelMoore : RationalCycleComponentBorelMooreData V x d p hx
  localThomCap : RationalCycleComponentLocalThomCapInput V d p x hx
  comparison :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - p)) ≃ₗ[ℚ]
      RationalSingularComponentCohomologyWithSupport V.over x (2 * p)
  comparison_isComplexOriented :
    IsComplexOrientedAlexanderPoincare borelMoore localThomCap comparison

namespace ComplexOrientedRationalCycleComponentClassData

variable {V : SmoothProjectiveComplexVariety} {d p : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  {x : V.scheme} {hx : coheight x = p}

/-- The exact compactification-relative Borel--Moore fundamental class. -/
def fundamentalClass (D : ComplexOrientedRationalCycleComponentClassData V d p x hx) :=
  D.borelMoore.fundamentalClass

/-- The normalized Alexander--Poincaré comparison, conditional on the supplied Thom-cap square. -/
def alexanderPoincare
    (D : ComplexOrientedRationalCycleComponentClassData V d p x hx) :=
  D.comparison

/-- The singular supported fundamental class normalized by the local Thom-cap square. -/
def supportedFundamentalClass
    (D : ComplexOrientedRationalCycleComponentClassData V d p x hx) :=
  D.alexanderPoincare D.fundamentalClass

/-- The normalized supported class has the exact constructed complex local orientation at every
smooth point. -/
theorem alexanderPoincare_fundamentalClass_local
    (D : ComplexOrientedRationalCycleComponentClassData V d p x hx)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus
      V.over x) :
    D.localThomCap.capWithAmbientComplexOrientation z hz D.supportedFundamentalClass =
      cycleComponentComplexLocalOrientation V x d p hx z hz :=
  (D.comparison_isComplexOriented D.fundamentalClass z hz).trans
    (D.borelMoore.toLocal_fundamentalClass z hz)

/-- Local Thom-cap normalization uniquely determines the supported fundamental class. -/
theorem supportedFundamentalClass_unique
    (D : ComplexOrientedRationalCycleComponentClassData V d p x hx)
    (α : RationalSingularComponentCohomologyWithSupport V.over x (2 * p))
    (hα : ∀ (z : CycleComponentAnalyticPoint V x)
      (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x),
      D.localThomCap.capWithAmbientComplexOrientation z hz α =
        cycleComponentComplexLocalOrientation V x d p hx z hz) :
    α = D.supportedFundamentalClass :=
  D.localThomCap.local_ext _ _ fun z hz ↦
    (hα z hz).trans (D.alexanderPoincare_fundamentalClass_local z hz).symm

/-- Forgetting the conditional wrapper recovers only auxiliary comparison data. -/
def toAuxiliaryComparisonData
    (D : ComplexOrientedRationalCycleComponentClassData V d p x hx) :
    AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx where
  borelMoore := D.borelMoore
  auxiliaryComparison := D.alexanderPoincare

/-- The rational constant-sheaf supported fundamental class, obtained through the proved Betti
comparison after local Thom-cap normalization. -/
def constantSheafSupportedFundamentalClass
    (D : ComplexOrientedRationalCycleComponentClassData V d p x hx) :
    RationalCohomologyWithSupport V.over
      (cycleComponentSupport V.over x) (2 * (p : ℤ)) :=
  D.toAuxiliaryComparisonData.supportedComparison.symm D.supportedFundamentalClass

/-- The conditional normalized ordinary rational component class. -/
def ordinaryFundamentalClass
    (D : ComplexOrientedRationalCycleComponentClassData V d p x hx) :
    H^(2 * (p : ℤ))(V.over; ℚ) :=
  forgetSupport V.over
    (cycleComponentSupport V.over x) (2 * (p : ℤ))
      D.constantSheafSupportedFundamentalClass

end ComplexOrientedRationalCycleComponentClassData

/-! ### The complete construction in maximal codimension -/

/-- A canonical smooth analytic point of a maximal-codimension cycle component. -/
def maximalCodimensionCycleComponentPoint
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    CycleComponentAnalyticPoint V x :=
  Classical.choose (exists_cycleComponent_smooth_complexPoint
    V.over x)

/-- The selected point belongs to the component's smooth analytic locus. -/
lemma maximalCodimensionCycleComponentPoint_mem_smooth
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    maximalCodimensionCycleComponentPoint V x ∈
      cycleComponentSmoothAnalyticLocus V.over x :=
  Classical.choose_spec (exists_cycleComponent_smooth_complexPoint
    V.over x)

/-- A maximal-codimension component's support is the singleton containing its selected point. -/
lemma maximalCodimensionCycleComponentSupport_eq_singleton
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    cycleComponentSupport V.over x =
      {cycleComponentMap V.over x
        (maximalCodimensionCycleComponentPoint V x)} :=
  cycleComponentSupport_eq_singleton_of_coheight_eq_dimension
    V.over d x hx
    (maximalCodimensionCycleComponentPoint V x)

/-- The normalized ambient point coclass, transported to the component support. -/
def maximalCodimensionSupportedGenerator
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    RationalSingularComponentCohomologyWithSupport V.over x (2 * d) := by
  let F := fun Z : Set V.analyticPoint ↦ CohomologyWithSupport ℚ
    (@TopCat.of V.analyticPoint Point.analyticTopology) Z (2 * d)
  exact LinearEquiv.cast (R := ℚ) (M := F)
    (maximalCodimensionCycleComponentSupport_eq_singleton V d x hx).symm
      (analyticPointLocalCoclass V.over d
        (cycleComponentMap V.over x
          (maximalCodimensionCycleComponentPoint V x)))

/-- The supported point coclass generates the maximal-codimension target. -/
lemma span_maximalCodimensionSupportedGenerator_eq_top
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    Submodule.span ℚ {maximalCodimensionSupportedGenerator V d x hx} = ⊤ := by
  let z := maximalCodimensionCycleComponentPoint V x
  let y := cycleComponentMap V.over x z
  let F := fun Z : Set V.analyticPoint ↦ CohomologyWithSupport ℚ
    (@TopCat.of V.analyticPoint Point.analyticTopology) Z (2 * d)
  let e := LinearEquiv.cast (R := ℚ) (M := F)
    (maximalCodimensionCycleComponentSupport_eq_singleton V d x hx).symm
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
    (x : V.scheme) (hx : coheight x = d) :
    maximalCodimensionSupportedGenerator V d x hx ≠ 0 := by
  let z := maximalCodimensionCycleComponentPoint V x
  let y := cycleComponentMap V.over x z
  let F := fun Z : Set V.analyticPoint ↦ CohomologyWithSupport ℚ
    (@TopCat.of V.analyticPoint Point.analyticTopology) Z (2 * d)
  let e := LinearEquiv.cast (R := ℚ) (M := F)
    (maximalCodimensionCycleComponentSupport_eq_singleton V d x hx).symm
  change e (analyticPointLocalCoclass V.over d y) ≠ 0
  have hsource :
      analyticPointLocalCoclass V.over d y ≠ 0 := by
    intro hzero
    have hone :=
      analyticPointLocalCoclass_apply_localClass V.over d y
    rw [hzero, LinearMap.zero_apply] at hone
    exact zero_ne_one hone
  intro hzero
  exact hsource (e.injective (by simpa using hzero))

/-- The explicitly constructed Borel--Moore fundamental class of a maximal-codimension
component. -/
def maximalCodimensionBorelMooreFundamentalClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - d)) :=
  (rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx).fundamentalClass

/-- The maximal-codimension Borel--Moore fundamental class is nonzero. -/
lemma maximalCodimensionBorelMooreFundamentalClass_ne_zero
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    maximalCodimensionBorelMooreFundamentalClass V d x hx ≠ 0 := by
  let z := maximalCodimensionCycleComponentPoint V x
  let hz := maximalCodimensionCycleComponentPoint_mem_smooth V x
  let D := rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx
  let : TopologicalSpace (CycleComponentAnalyticPoint V x) := Point.analyticTopology
  let : Subsingleton (CycleComponentAnalyticPoint V x) :=
    cycleComponentAnalyticPoint_subsingleton_of_coheight_eq_dimension V x d hx
  let e := compactificationBorelMooreToLocalEquivOfSubsingleton
    ℚ z (2 * (d - d))
  change D.fundamentalClass ≠ 0
  intro hzero
  have hlocal := D.toLocal_fundamentalClass z hz
  change e D.fundamentalClass = D.localOrientation z hz at hlocal
  rw [hzero, map_zero] at hlocal
  exact (cycleComponentComplexLocalOrientation_ne_zero V x d d hx z hz) hlocal.symm

/-- The maximal-codimension Borel--Moore fundamental class generates its homology group. -/
lemma span_maximalCodimensionBorelMooreFundamentalClass_eq_top
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    Submodule.span ℚ {maximalCodimensionBorelMooreFundamentalClass V d x hx} = ⊤ := by
  let z := maximalCodimensionCycleComponentPoint V x
  let hz := maximalCodimensionCycleComponentPoint_mem_smooth V x
  let D := rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx
  let : TopologicalSpace (CycleComponentAnalyticPoint V x) := Point.analyticTopology
  let : Subsingleton (CycleComponentAnalyticPoint V x) :=
    cycleComponentAnalyticPoint_subsingleton_of_coheight_eq_dimension V x d hx
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
    change cycleComponentBorelMooreToLocal ℚ V x
      (2 * (d - d)) z D.fundamentalClass = D.localOrientation z hz
    exact D.toLocal_fundamentalClass z hz
  apply e.injective
  rw [e.map_smul, hlocal, ha]

/-- Alexander--Poincaré duality for a zero-dimensional component, characterized by sending
its oriented Borel--Moore generator to the normalized ambient point coclass. -/
def maximalCodimensionAlexanderDuality
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    CycleComponentBorelMooreHomology ℚ V x (2 * (d - d)) ≃ₗ[ℚ]
      RationalSingularComponentCohomologyWithSupport V.over x (2 * d) :=
  linearEquivOfNormalizedGenerators
    (maximalCodimensionBorelMooreFundamentalClass V d x hx)
    (maximalCodimensionBorelMooreFundamentalClass_ne_zero V d x hx)
    (span_maximalCodimensionBorelMooreFundamentalClass_eq_top V d x hx)
    (maximalCodimensionSupportedGenerator V d x hx)
    (maximalCodimensionSupportedGenerator_ne_zero V d x hx)
    (span_maximalCodimensionSupportedGenerator_eq_top V d x hx)

/-- Maximal-codimension duality sends the oriented Borel--Moore generator to the normalized
ambient point coclass. -/
@[simp] lemma maximalCodimensionAlexanderDuality_fundamentalClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    maximalCodimensionAlexanderDuality V d x hx
        (maximalCodimensionBorelMooreFundamentalClass V d x hx) =
      maximalCodimensionSupportedGenerator V d x hx :=
  linearEquivOfNormalizedGenerators_apply_generator _ _ _ _ _ _

/-- The point-case duality equivalence is uniquely determined by its orientation
normalization. -/
lemma maximalCodimensionAlexanderDuality_unique
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d)
    (e : CycleComponentBorelMooreHomology ℚ V x (2 * (d - d)) ≃ₗ[ℚ]
        RationalSingularComponentCohomologyWithSupport V.over x (2 * d))
    (he : e (maximalCodimensionBorelMooreFundamentalClass V d x hx) =
      maximalCodimensionSupportedGenerator V d x hx) :
    e = maximalCodimensionAlexanderDuality V d x hx :=
  linearEquivOfNormalizedGenerators_unique
    (maximalCodimensionBorelMooreFundamentalClass V d x hx)
    (maximalCodimensionBorelMooreFundamentalClass_ne_zero V d x hx)
    (span_maximalCodimensionBorelMooreFundamentalClass_eq_top V d x hx)
    (maximalCodimensionSupportedGenerator V d x hx)
    (maximalCodimensionSupportedGenerator_ne_zero V d x hx)
    (span_maximalCodimensionSupportedGenerator_eq_top V d x hx) e he

/-- In maximal codimension, cap with the ambient complex orientation is the uniquely normalized
equivalence from the point-supported coclass to local homology.  The one-dimensional argument is
used only in this explicitly labeled point case. -/
def maximalCodimensionLocalThomCapEquiv
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus
      V.over x) :
    RationalSingularComponentCohomologyWithSupport V.over x (2 * d) ≃ₗ[ℚ]
      RelativeHomology ℚ (pointComplementPair z) (2 * (d - d)) :=
  let D := rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx
  linearEquivOfNormalizedGenerators
    (maximalCodimensionSupportedGenerator V d x hx)
    (maximalCodimensionSupportedGenerator_ne_zero V d x hx)
    (span_maximalCodimensionSupportedGenerator_eq_top V d x hx)
    (D.localOrientation z hz)
    (cycleComponentComplexLocalOrientation_ne_zero V x d d hx z hz)
    (D.span_localOrientation_eq_top z hz)

/-- Point-case Thom cap sends the normalized ambient coclass to the exact complex local class. -/
@[simp] lemma maximalCodimensionLocalThomCapEquiv_supportedGenerator
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d)
    (z : CycleComponentAnalyticPoint V x)
    (hz : z ∈ cycleComponentSmoothAnalyticLocus
      V.over x) :
    maximalCodimensionLocalThomCapEquiv V d x hx z hz
        (maximalCodimensionSupportedGenerator V d x hx) =
      cycleComponentComplexLocalOrientation V x d d hx z hz := by
  let D := rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx
  change maximalCodimensionLocalThomCapEquiv V d x hx z hz
      (maximalCodimensionSupportedGenerator V d x hx) = D.localOrientation z hz
  exact linearEquivOfNormalizedGenerators_apply_generator
    (maximalCodimensionSupportedGenerator V d x hx)
    (maximalCodimensionSupportedGenerator_ne_zero V d x hx)
    (span_maximalCodimensionSupportedGenerator_eq_top V d x hx)
    (D.localOrientation z hz)
    (cycleComponentComplexLocalOrientation_ne_zero V x d d hx z hz)
    (D.span_localOrientation_eq_top z hz)

/-- The actual local Thom-cap package is completely constructed for a point component. -/
def maximalCodimensionLocalThomCapInput
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    RationalCycleComponentLocalThomCapInput V d d x hx where
  capWithAmbientComplexOrientation z hz :=
    (maximalCodimensionLocalThomCapEquiv V d x hx z hz).toLinearMap
  local_ext α β h := by
    let z := maximalCodimensionCycleComponentPoint V x
    let hz := maximalCodimensionCycleComponentPoint_mem_smooth V x
    exact (maximalCodimensionLocalThomCapEquiv V d x hx z hz).injective (h z hz)

/-- The constructed point-case duality satisfies the full exact local Thom-cap square. -/
lemma maximalCodimensionAlexanderDuality_isComplexOriented
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    IsComplexOrientedAlexanderPoincare
      (rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx)
      (maximalCodimensionLocalThomCapInput V d x hx)
      (maximalCodimensionAlexanderDuality V d x hx) := by
  intro c z hz
  let D := rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx
  change maximalCodimensionLocalThomCapEquiv V d x hx z hz
      (maximalCodimensionAlexanderDuality V d x hx c) =
    cycleComponentBorelMooreToLocal ℚ V x (2 * (d - d)) z c
  obtain ⟨a, ha⟩ :=
    (Submodule.span_singleton_eq_top_iff ℚ
      (maximalCodimensionBorelMooreFundamentalClass V d x hx)).mp
        (span_maximalCodimensionBorelMooreFundamentalClass_eq_top V d x hx) c
  rw [← ha, map_smul, map_smul, map_smul,
    maximalCodimensionAlexanderDuality_fundamentalClass,
    maximalCodimensionLocalThomCapEquiv_supportedGenerator]
  simpa only [RationalCycleComponentBorelMooreData.localOrientation,
    maximalCodimensionBorelMooreFundamentalClass] using
      congrArg (a • ·) (D.toLocal_fundamentalClass z hz).symm

/-- The fully constructed point case, now expressed through the same locally normalized interface
used by the conditional general theory. -/
def maximalCodimensionComplexOrientedComponentClassData
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    ComplexOrientedRationalCycleComponentClassData V d d x hx where
  borelMoore := rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx
  localThomCap := maximalCodimensionLocalThomCapInput V d x hx
  comparison := maximalCodimensionAlexanderDuality V d x hx
  comparison_isComplexOriented :=
    maximalCodimensionAlexanderDuality_isComplexOriented V d x hx

/-- The normalized-interface point class is exactly the previously constructed ambient point
coclass, not merely a nonzero rational multiple of it. -/
@[simp] lemma maximalCodimensionComplexOrientedComponentClassData_supported
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    (maximalCodimensionComplexOrientedComponentClassData V d x hx).supportedFundamentalClass =
      maximalCodimensionSupportedGenerator V d x hx :=
  maximalCodimensionAlexanderDuality_fundamentalClass V d x hx

/-- The complete Borel--Moore and point-duality package in maximal codimension. -/
def auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    AuxiliaryRationalCycleComponentBorelMooreComparisonData V d d x hx where
  borelMoore := rationalCycleComponentBorelMooreDataOfCoheightEqDimension V x d hx
  auxiliaryComparison := maximalCodimensionAlexanderDuality V d x hx

/-- The supported class in the maximal-codimension package is the normalized point coclass. -/
@[simp] lemma auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension_supported
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    AuxiliaryRationalCycleComponentBorelMooreComparisonData.auxiliarySingularSupportedClass
        (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension V d x hx) =
      maximalCodimensionSupportedGenerator V d x hx :=
  maximalCodimensionAlexanderDuality_fundamentalClass V d x hx

/-- The fully constructed ordinary class of a maximal-codimension irreducible component. -/
def maximalCodimensionComponentClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    H^(2 * (d : ℤ))(V.over; ℚ) :=
  AuxiliaryRationalCycleComponentBorelMooreComparisonData.auxiliaryOrdinaryClass
    (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension V d x hx)

/-- The maximal-codimension ordinary class is obtained by transporting the normalized singular
point coclass through the proved support comparison and then forgetting support. -/
lemma maximalCodimensionComponentClass_eq_forgetSupport_pointCoclass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (x : V.scheme) (hx : coheight x = d) :
    maximalCodimensionComponentClass V d x hx =
      forgetSupport V.over
        (cycleComponentSupport V.over x)
        (2 * (d : ℤ))
        ((auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension V d x hx).supportedComparison.symm
          (maximalCodimensionSupportedGenerator V d x hx)) := by
  unfold maximalCodimensionComponentClass
  rw [AuxiliaryRationalCycleComponentBorelMooreComparisonData.auxiliaryOrdinaryClass,
    AuxiliaryRationalCycleComponentBorelMooreComparisonData.auxiliarySupportedClass,
    auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension_supported]

/-- The exact remaining geometric statement for descending the constructed
maximal-codimension component classes to the Chow group. -/
def MaximalCodimensionPrincipalDivisorClassVanishes
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] : Prop :=
  ∀ D : PrincipalDivisor V.scheme d,
    cycleClassOnAlgebraicCyclesOfComponents
        (maximalCodimensionComponentClass V d) D.pushforwardCycle = 0

/-- Auxiliary descent data for comparison-dependent component classes.

Although each source Borel--Moore class is exactly normalized, the comparison used for each
component may be independently rescaled.  Thus this structure and `auxiliaryCycleClass` do not
define the standard general cycle-class map.  The quotient descent itself is constructed from
the stated principal-divisor vanishing theorem. -/
structure AuxiliaryRationalBorelMooreCycleClassDescent
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] where
  /-- The normalized Borel--Moore source and an auxiliary comparison for every component. -/
  component : ∀ (x : V.scheme) (hx : coheight x = p),
    AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx
  /-- Principal divisors have zero comparison-dependent componentwise class. -/
  principalDivisor_class : ∀ D : PrincipalDivisor V.scheme p,
    cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (component x hx).auxiliaryOrdinaryClass)
        D.pushforwardCycle = 0

namespace AuxiliaryRationalBorelMooreCycleClassDescent

/-- Build an auxiliary comparison descent from the two intrinsic geometric statements
for principal divisors: compatibility with proper pushforward from the carrier, and vanishing of
the divisor class on that carrier.  The ambient principal-divisor theorem is derived by applying
the Gysin compatibility to the intrinsic vanishing theorem; it is not an additional field of the
input.

This is the data-oriented entry point for a future Thom--Gysin construction.  All quotient and
scalar-extension steps remain part of `auxiliaryCycleClass` below. -/
def ofCarrierDivisors
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (component : ∀ (x : V.scheme) (hx : coheight x = p),
      AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx)
    (carrierClass : ∀ D : PrincipalDivisor V.scheme p,
      AlgebraicCycle D.carrier ℤ →+
        H^(2 * (p : ℤ))(V.over; ℚ))
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (component x hx).auxiliaryOrdinaryClass)))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    AuxiliaryRationalBorelMooreCycleClassDescent V d p where
  component := component
  principalDivisor_class := fun D ↦
    principalDivisor_class_eq_zero_of_carrier_divisor_class_eq_zero
      D (carrierClass D)
        (cycleClassOnAlgebraicCyclesOfComponents
          (fun x hx ↦ (component x hx).auxiliaryOrdinaryClass))
        (hpush D) (hdivisor D)

/-- A version of `ofCarrierDivisors` in which the intrinsic divisor class and its Gysin map have
separate targets.  This matches the geometric construction literally: first construct the
codimension-one class on each integral carrier, then push it into ambient cohomology.  The target
is allowed to depend on the principal-divisor datum, as carrier cohomology naturally does. -/
def ofCarrierDivisorsViaGysin
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (component : ∀ (x : V.scheme) (hx : coheight x = p),
      AuxiliaryRationalCycleComponentBorelMooreComparisonData V d p x hx)
    (carrierTarget : PrincipalDivisor V.scheme p → Type*)
    [∀ D, AddCommGroup (carrierTarget D)]
    (carrierClass : ∀ D : PrincipalDivisor V.scheme p,
      AlgebraicCycle D.carrier ℤ →+ carrierTarget D)
    (gysin : ∀ D : PrincipalDivisor V.scheme p,
      carrierTarget D →+
        H^(2 * (p : ℤ))(V.over; ℚ))
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforwardVia D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (component x hx).auxiliaryOrdinaryClass))
      (gysin D))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    AuxiliaryRationalBorelMooreCycleClassDescent V d p where
  component := component
  principalDivisor_class := fun D ↦
    principalDivisor_class_eq_zero_of_gysin_carrier_divisor_class_eq_zero
      D (carrierClass D)
        (cycleClassOnAlgebraicCyclesOfComponents
          (fun x hx ↦ (component x hx).auxiliaryOrdinaryClass))
        (gysin D) (hpush D) (hdivisor D)

/-- In maximal codimension all componentwise Borel--Moore and duality data are constructed.
Consequently the only input to the Chow-level construction is the intrinsic geometric theorem
that principal divisors have zero class. -/
def ofMaximalCodimension
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hprincipal : MaximalCodimensionPrincipalDivisorClassVanishes V d) :
    AuxiliaryRationalBorelMooreCycleClassDescent V d d where
  component := auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension V d
  principalDivisor_class := hprincipal

/-- In maximal codimension, construct the entire package from carrierwise Gysin compatibility
and intrinsic principal-divisor vanishing.  Local orientations, Borel--Moore fundamental
classes, and point Alexander duality are already constructed, while the two arguments here are
exactly the remaining functorial divisor theorems. -/
def ofMaximalCodimensionOfCarrierDivisors
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (carrierClass : ∀ D : PrincipalDivisor V.scheme d,
      AlgebraicCycle D.carrier ℤ →+
        H^(2 * (d : ℤ))(V.over; ℚ))
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension
          V d x hx).auxiliaryOrdinaryClass)))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    AuxiliaryRationalBorelMooreCycleClassDescent V d d :=
  ofCarrierDivisors
    (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension V d)
    carrierClass hpush hdivisor

/-- Maximal-codimension construction with the intrinsic carrier class and the Gysin map kept
separate.  This is the closest interface to the usual proof that a principal Cartier divisor has
zero first Chern class before proper pushforward. -/
def ofMaximalCodimensionViaGysin
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (carrierTarget : PrincipalDivisor V.scheme d → Type*)
    [∀ D, AddCommGroup (carrierTarget D)]
    (carrierClass : ∀ D : PrincipalDivisor V.scheme d,
      AlgebraicCycle D.carrier ℤ →+ carrierTarget D)
    (gysin : ∀ D : PrincipalDivisor V.scheme d,
      carrierTarget D →+
        H^(2 * (d : ℤ))(V.over; ℚ))
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforwardVia D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension
          V d x hx).auxiliaryOrdinaryClass))
      (gysin D))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    AuxiliaryRationalBorelMooreCycleClassDescent V d d :=
  ofCarrierDivisorsViaGysin
    (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension V d)
    carrierTarget carrierClass gysin hpush hdivisor

/-- The auxiliary ordinary class assigned to an irreducible codimension-`p` component. -/
def auxiliaryComponentClass
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : AuxiliaryRationalBorelMooreCycleClassDescent V d p)
    (x : V.scheme) (hx : coheight x = p) :
    H^(2 * (p : ℤ))(V.over; ℚ) :=
  (C.component x hx).auxiliaryOrdinaryClass

@[simp] lemma ofMaximalCodimension_auxiliaryComponentClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hprincipal : MaximalCodimensionPrincipalDivisorClassVanishes V d)
    (x : V.scheme) (hx : coheight x = d) :
    (ofMaximalCodimension V d hprincipal).auxiliaryComponentClass x hx =
      maximalCodimensionComponentClass V d x hx :=
  rfl

/-- The auxiliary rational Chow-group map derived from the rescalable comparison classes. Its
construction performs the genuine quotient descent, but it is not identified with the standard
cycle-class map outside cases where the comparisons are independently normalized. -/
def auxiliaryCycleClass
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : AuxiliaryRationalBorelMooreCycleClassDescent V d p) :
    RationalChowGroup V.scheme p →ₗ[ℚ]
      H^(2 * (p : ℤ))(V.over; ℚ) :=
  ChowGroup.rationalCycleClassOfComponents C.auxiliaryComponentClass C.principalDivisor_class

/-- The auxiliary descended map sends a component to its comparison-dependent ordinary class. -/
@[simp] theorem auxiliaryCycleClass_component
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : AuxiliaryRationalBorelMooreCycleClassDescent V d p)
    (x : V.scheme) (hx : coheight x = p) :
    C.auxiliaryCycleClass (rationalComponentChowClass
      V.over p x hx) = C.auxiliaryComponentClass x hx :=
  ChowGroup.rationalCycleClassOfComponents_component
    C.auxiliaryComponentClass C.principalDivisor_class x hx

/-- The maximal-codimension rational Chow cycle-class map, with every local, Borel--Moore, and
duality ingredient constructed.  Its sole argument is the remaining principal-divisor theorem.
-/
def maximalCodimensionCycleClass
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hprincipal : MaximalCodimensionPrincipalDivisorClassVanishes V d) :
    RationalChowGroup V.scheme d →ₗ[ℚ]
      H^(2 * (d : ℤ))(V.over; ℚ) :=
  (ofMaximalCodimension V d hprincipal).auxiliaryCycleClass

/-- The maximal-codimension rational Chow cycle-class map constructed from the carrierwise
geometric inputs, without asking separately for an ambient rational-equivalence theorem. -/
def maximalCodimensionCycleClassOfCarrierDivisors
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (carrierClass : ∀ D : PrincipalDivisor V.scheme d,
      AlgebraicCycle D.carrier ℤ →+
        H^(2 * (d : ℤ))(V.over; ℚ))
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension
          V d x hx).auxiliaryOrdinaryClass)))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    RationalChowGroup V.scheme d →ₗ[ℚ]
      H^(2 * (d : ℤ))(V.over; ℚ) :=
  (ofMaximalCodimensionOfCarrierDivisors V d carrierClass hpush hdivisor).auxiliaryCycleClass

/-- The resulting maximal-codimension Chow map sends a component to the explicitly normalized
Borel--Moore point class. -/
@[simp] lemma maximalCodimensionCycleClass_component
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hprincipal : MaximalCodimensionPrincipalDivisorClassVanishes V d)
    (x : V.scheme) (hx : coheight x = d) :
    maximalCodimensionCycleClass V d hprincipal
        (rationalComponentChowClass V.over d x hx) =
      maximalCodimensionComponentClass V d x hx :=
  (ofMaximalCodimension V d hprincipal).auxiliaryCycleClass_component x hx

/-- The carrierwise construction has the same normalized component formula. -/
@[simp] lemma maximalCodimensionCycleClassOfCarrierDivisors_component
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (carrierClass : ∀ D : PrincipalDivisor V.scheme d,
      AlgebraicCycle D.carrier ℤ →+
        H^(2 * (d : ℤ))(V.over; ℚ))
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (auxiliaryRationalCycleComponentBorelMooreComparisonDataOfCoheightEqDimension
          V d x hx).auxiliaryOrdinaryClass)))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0)
    (x : V.scheme) (hx : coheight x = d) :
    maximalCodimensionCycleClassOfCarrierDivisors V d carrierClass hpush hdivisor
        (rationalComponentChowClass V.over d x hx) =
      maximalCodimensionComponentClass V d x hx :=
  (ofMaximalCodimensionOfCarrierDivisors V d carrierClass hpush
    hdivisor).auxiliaryCycleClass_component x hx

/-- The auxiliary component class is in the range of the auxiliary descended map. -/
lemma auxiliaryOrdinaryClass_mem_range
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : AuxiliaryRationalBorelMooreCycleClassDescent V d p)
    (x : V.scheme) (hx : coheight x = p) :
    (C.component x hx).auxiliaryOrdinaryClass ∈ LinearMap.range C.auxiliaryCycleClass :=
  ⟨rationalComponentChowClass V.over p x hx, C.auxiliaryCycleClass_component x hx⟩

end AuxiliaryRationalBorelMooreCycleClassDescent

/-! ### Descent of normalized component classes -/

/-- The remaining geometric input for descending the conditionally normalized component classes
to the rational Chow group.

The component field retains the global fundamental-class existence theorem and the supplied
Thom-cap, local-detection, and comparison inputs of
`ComplexOrientedRationalCycleComponentClassData`. Its normalization is relative to those
supplied maps, not an unconditional protection against simultaneous rescaling. In addition,
principal-divisor vanishing is supplied here. The additive extension, quotient descent,
and rational scalar extension are constructed below from these explicit inputs. -/
structure ComplexOrientedRationalBorelMooreCycleClassConstruction
    (V : SmoothProjectiveComplexVariety) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] where
  component : ∀ (x : V.scheme) (hx : coheight x = p),
    ComplexOrientedRationalCycleComponentClassData V d p x hx
  principalDivisor_class : ∀ D : PrincipalDivisor V.scheme p,
    cycleClassOnAlgebraicCyclesOfComponents
        (fun x hx ↦ (component x hx).ordinaryFundamentalClass)
        D.pushforwardCycle = 0

namespace ComplexOrientedRationalBorelMooreCycleClassConstruction

/-- The normalized ordinary class assigned to an irreducible codimension-`p` component. -/
def componentClass
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : ComplexOrientedRationalBorelMooreCycleClassConstruction V d p)
    (x : V.scheme) (hx : coheight x = p) :
    H^(2 * (p : ℤ))(V.over; ℚ) :=
  (C.component x hx).ordinaryFundamentalClass

/-- Descent of the locally normalized component classes to a rational linear map on the Chow
group.  This map is constructed by the quotient universal property; it is not stored as data. -/
def cycleClass
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : ComplexOrientedRationalBorelMooreCycleClassConstruction V d p) :
    RationalChowGroup V.scheme p →ₗ[ℚ]
      H^(2 * (p : ℤ))(V.over; ℚ) :=
  ChowGroup.rationalCycleClassOfComponents C.componentClass C.principalDivisor_class

/-- The descended map sends an irreducible component to its locally normalized class. -/
@[simp] theorem cycleClass_component
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : ComplexOrientedRationalBorelMooreCycleClassConstruction V d p)
    (x : V.scheme) (hx : coheight x = p) :
    C.cycleClass (rationalComponentChowClass
      V.over p x hx) = C.componentClass x hx :=
  ChowGroup.rationalCycleClassOfComponents_component
    C.componentClass C.principalDivisor_class x hx

/-- Every normalized component class lies in the range of the descended Chow map. -/
theorem componentClass_mem_range
    {V : SmoothProjectiveComplexVariety} {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap]
    (C : ComplexOrientedRationalBorelMooreCycleClassConstruction V d p)
    (x : V.scheme) (hx : coheight x = p) :
    C.componentClass x hx ∈ LinearMap.range C.cycleClass :=
  ⟨rationalComponentChowClass V.over p x hx, C.cycleClass_component x hx⟩

end ComplexOrientedRationalBorelMooreCycleClassConstruction

end AlgebraicGeometry.ComplexPoint
