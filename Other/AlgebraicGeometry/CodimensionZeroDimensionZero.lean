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

public import Other.AlgebraicGeometry.CodimensionZeroClassComparison
public import Other.AlgebraicGeometry.CycleComponentPointClassNormalization
public import Other.AlgebraicGeometry.CycleComponentPointPurity
public import Other.AlgebraicGeometry.SmoothClosedPointCoclassSectionNormalization

import Other.AlgebraicGeometry.HodgeCodimensionZero
import Other.AlgebraicGeometry.ProjectiveAnalytificationConnected

/-!
# The Hodge conjecture for smooth projective complex varieties of dimension zero

On a variety of complex dimension zero the generic point is also its unique point of maximal
codimension, so the constructed component class is the transported chart-local point coclass.
That coclass is normalized to take the value one on the chart-local fundamental class, and the
pair comparison it is transported along is an isomorphism because the component support is the
single analytic point. The generic-point component class is therefore nonzero, which identifies
the two codimension-zero span constructions and proves the Hodge-conjecture inclusion in every
codimension.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

/-- The inverse of the whole-space support comparison at a singleton support. -/
def pointToUnivSupportPairMap (x : M) :
    pointComplementPair x ⟶
      neighborhoodSupportComplementPair (Set.univ : Set M) ({x} : Set M) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun m => ⟨m, Set.mem_univ m⟩, continuous_id.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨w.1, Set.mem_univ _⟩, w.2⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩) rfl

/-- At a singleton support the whole-space comparison retracts onto the point pair. -/
theorem pointToUnivSupportPairMap_comp (x : M) (hx : x ∈ ({x} : Set M)) :
    pointToUnivSupportPairMap x ≫
        neighborhoodSupportToPointPairMap (Set.univ : Set M) ({x} : Set M) x hx =
      𝟙 (pointComplementPair x) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- Pulling back along the whole-space support comparison is injective when the support is the
single distinguished point. -/
theorem relativeCohomologyMap_neighborhoodSupportToPointPairMap_injective
    (V S : Set M) (x : M) (hx : x ∈ S) (hV : V = Set.univ) (hS : S = ({x} : Set M)) (n : ℕ) :
    Function.Injective
      (relativeCohomologyMap ℚ n (neighborhoodSupportToPointPairMap V S x hx)) := by
  subst hV
  subst hS
  have hid : (relativeCohomologyMap ℚ n (pointToUnivSupportPairMap x)).comp
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportToPointPairMap (Set.univ : Set M) ({x} : Set M) x hx)) =
      LinearMap.id := by
    rw [← relativeCohomologyMap_comp, pointToUnivSupportPairMap_comp x hx,
      relativeCohomologyMap_id]
  exact Function.LeftInverse.injective
    (g := relativeCohomologyMap ℚ n (pointToUnivSupportPairMap x))
    fun a ↦ congrFun (congrArg (fun f : _ →ₗ[ℚ] _ ↦ (f : _ → _)) hid) a

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The chart-local point coclass is nonzero: it takes the value one on the chart-local
fundamental class. -/
theorem analyticPointLocalCoclass_ne_zero (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    analyticPointLocalCoclass X d z ≠ 0 := by
  intro h
  have h1 := analyticPointLocalCoclass_apply_localClass X d z
  rw [h] at h1
  simp at h1

/-- On a variety of complex dimension zero the constructed generic-point component class is
nonzero. -/
theorem cycleComponentSheafClass_genericPoint_ne_zero_of_dimension_eq_zero
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (hd : d = 0) :
    cycleComponentSheafClass X (genericPoint X.left) (d := d)
      (coheight_genericPoint_eq_zero X) ≠ 0 := by
  subst hd
  intro hzero
  obtain ⟨z, -⟩ := exists_cycleComponent_smooth_complexPoint X (genericPoint X.left)
  have hinj :=
    (cycleComponentSheafClass_genericPoint_eq_zero_iff_supportedInjectiveClass X 0).mp hzero
  rw [cycleComponentSupportedInjectiveClass_point_normalization X (genericPoint X.left) 0 z
    (coheight_genericPoint_eq_zero X)] at hinj
  have hrel : analyticComponentPointRelativeCoclass X (genericPoint X.left) 0 z = 0 := by
    rw [← analyticComponentPointSupportedInjectiveCoclass_relative X (genericPoint X.left) 0 z,
      hinj]
    exact AddEquiv.map_zero _
  have hsupport : cycleComponentSupport X (genericPoint X.left) =
      {cycleComponentMap X (genericPoint X.left) z} :=
    cycleComponentSupport_eq_singleton_of_coheight_eq_dimension X 0 (genericPoint X.left)
      (coheight_genericPoint_eq_zero X) z
  refine analyticPointLocalCoclass_ne_zero X 0 (cycleComponentMap X (genericPoint X.left) z) ?_
  refine relativeCohomologyMap_neighborhoodSupportToPointPairMap_injective
    ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
    (cycleComponentSupport X (genericPoint X.left))
    (cycleComponentMap X (genericPoint X.left) z)
    (range_cycleComponentMap_subset X (genericPoint X.left) ⟨z, rfl⟩)
    Opens.coe_top hsupport (2 * 0) ?_
  rw [map_zero]
  exact hrel

/-- The two codimension-zero span constructions agree on a variety of complex dimension zero. -/
theorem algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan_of_dimension_eq_zero
    (hd : dim X.left = 0) :
    algebraicCycleClassSpan X 0 = codimensionZeroCycleClassSpan X := by
  let : ConnectedSpace (ComplexPoint X) :=
    connectedSpaceOfDimensionEqZero X (dim X.left) hd
  exact (algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan_iff X).mpr
    (cycleComponentSheafClass_genericPoint_ne_zero_of_dimension_eq_zero X (dim X.left) hd)

/-- The Hodge-conjecture inclusion holds in every codimension for a smooth projective complex
variety of complex dimension zero. -/
theorem rationalHodgeClasses_le_algebraicCycleClassSpan_of_dimension_zero
    (hd : dim X.left = 0) (p : ℕ) :
    Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p :=
  rationalHodgeClasses_le_algebraicCycleClassSpan_of_dimension_eq_zero X hd
    (algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan_of_dimension_eq_zero X hd) p

end AlgebraicGeometry.ComplexPoint
