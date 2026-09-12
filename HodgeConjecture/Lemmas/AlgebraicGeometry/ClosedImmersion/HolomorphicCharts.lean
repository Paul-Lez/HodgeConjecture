/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

/-!
# Actual holomorphic support-flattening charts

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- At every selected ambient source point, the underlying normal coordinate change and
its inverse are analytic, not only at the initially distinguished center. -/
private theorem closedImmersionHolomorphicFlatteningChart_analytic (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z)
      (localChart X d (Point.map i z) y) ∧
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z).symm
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) :=
  ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hy.1.2).2

private theorem closedImmersionNormalCoordinateChange_symm_at_chart (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    (closedImmersionNormalCoordinateChange X Y i m d z).symm
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) =
        localChart X d (Point.map i z) y :=
  (closedImmersionNormalCoordinateChange X Y i m d z).left_inv hy.1.2.1

variable (z' : ComplexPoint Y)

/-- The genuine transition between two constructed holomorphic support-flattening charts. -/
def closedImmersionNormalTransition :
    OpenPartialHomeomorph ((Fin m → ℂ) × (Fin (d - m) → ℂ))
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans
    (closedImmersionHolomorphicFlatteningChart X Y i m d z')

/-- These actual transitions are holomorphic throughout their domains. -/
theorem analyticAt_closedImmersionNormalTransition
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (closedImmersionNormalTransition X Y i m d z z').source) :
    AnalyticAt ℂ (closedImmersionNormalTransition X Y i m d z z') v := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := closedImmersionHolomorphicFlatteningChart X Y i m d z'
  let C := localChart X d (Point.map i z)
  let C' := localChart X d (Point.map i z')
  let A := closedImmersionNormalCoordinateChange X Y i m d z
  let A' := closedImmersionNormalCoordinateChange X Y i m d z'
  let y := e.symm v
  have hyv : y ∈ e.source := e.map_target hv.1
  have hyv' : y ∈ e'.source := hv.2
  have hyC : y ∈ C.source := hyv.1.1
  have hyC' : y ∈ C'.source := hyv'.1.1
  have hAv := closedImmersionNormalCoordinateChange_symm_at_chart
    X Y i m d z y hyv
  change A.symm (e (e.symm v)) = C y at hAv
  rw [e.right_inv hv.1] at hAv
  have hA := (closedImmersionHolomorphicFlatteningChart_analytic
    X Y i m d z y hyv).2
  change AnalyticAt ℂ A.symm (e (e.symm v)) at hA
  rw [e.right_inv hv.1] at hA
  have hA' := (closedImmersionHolomorphicFlatteningChart_analytic
    X Y i m d z' y hyv').1
  have hCC : AnalyticAt ℂ (fun w => C' (C.symm w)) (C y) := by
    apply analyticAt_localChart_transition X d (Point.map i z) (Point.map i z')
    refine ⟨C.map_source hyC, ?_⟩
    change C.symm (C y) ∈ C'.source
    rw [C.left_inv hyC]
    exact hyC'
  have hCC' : AnalyticAt ℂ (fun w => C' (C.symm w)) (A.symm v) := hAv ▸ hCC
  have hmiddle := hCC'.comp hA
  have himage : C' (C.symm (A.symm v)) = C' y := by rw [hAv, C.left_inv hyC]
  have hlast : AnalyticAt ℂ A' (C' (C.symm (A.symm v))) := himage ▸ hA'
  exact hlast.comp (f := fun w => C' (C.symm (A.symm w))) (x := v) hmiddle

/-- The actual transition preserves the zero-normal plane in both directions. -/
theorem closedImmersionNormalTransition_preserves_support
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (closedImmersionNormalTransition X Y i m d z z').source) :
    (closedImmersionNormalTransition X Y i m d z z' v).2 = 0 ↔ v.2 = 0 := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := closedImmersionHolomorphicFlatteningChart X Y i m d z'
  have hy := e.map_target hv.1
  have h1 := closedImmersionHolomorphicFlatteningChart_mem_range_iff
    X Y i m d z (e.symm v) hy
  have h2 := closedImmersionHolomorphicFlatteningChart_mem_range_iff
    X Y i m d z' (e.symm v) hv.2
  change e.symm v ∈ Set.range (Point.map i) ↔ (e (e.symm v)).2 = 0 at h1
  rw [e.right_inv hv.1] at h1
  exact h2.symm.trans h1

/-- The actual inverse transition is holomorphic at the image of every source point. -/
theorem analyticAt_closedImmersionNormalTransition_symm
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (closedImmersionNormalTransition X Y i m d z z').source) :
    AnalyticAt ℂ (closedImmersionNormalTransition X Y i m d z z').symm
      (closedImmersionNormalTransition X Y i m d z z' v) :=
  analyticAt_closedImmersionNormalTransition X Y i m d z' z
    (closedImmersionNormalTransition X Y i m d z z' v)
    ((closedImmersionNormalTransition X Y i m d z z').map_source hv)

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

@[simp] theorem biAnalyticRestrict_apply (x : E) : e.biAnalyticRestrict x = e x := rfl
@[simp] theorem biAnalyticRestrict_symm_apply (y : F) : e.biAnalyticRestrict.symm y = e.symm y := rfl

end OpenPartialHomeomorph

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

theorem closedImmersionNormalCoordinateChange_mem_source :
    localChart X d (Point.map i z) (Point.map i z) ∈
      (closedImmersionNormalCoordinateChange X Y i m d z).source :=
  ⟨closedImmersionNormalChart_mem_target X Y i m d z, trivial⟩

@[simp] theorem closedImmersionNormalCoordinateChange_center :
    closedImmersionNormalCoordinateChange X Y i m d z
      (localChart X d (Point.map i z) (Point.map i z)) =
        (localChart Y m z z, 0) := by
  change closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
    ((closedImmersionNormalChart X Y i m d z).symm _) = _
  rw [closedImmersionNormalChart_symm_center]
  simp [closedImmersionNormalCoordinatesLinearEquiv]

theorem analyticAt_closedImmersionNormalCoordinateChange :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z)
      (localChart X d (Point.map i z) (Point.map i z)) :=
  ((closedImmersionNormalCoordinatesLinearEquiv X Y i m d z).toContinuousLinearMap.analyticAt
    _).comp (analyticAt_closedImmersionNormalChart_symm X Y i m d z)

theorem analyticAt_closedImmersionNormalCoordinateChange_symm :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z).symm
      (localChart Y m z z, 0) := by
  let K := closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
  have hK : K.symm (localChart Y m z z, 0) = (localChart Y m z z, 0) := by
    simp [K, closedImmersionNormalCoordinatesLinearEquiv]
  have hA' : AnalyticAt ℂ (closedImmersionNormalChart X Y i m d z)
      (K.symm (localChart Y m z z, 0)) := hK ▸ analyticAt_closedImmersionNormalChart X Y i m d z
  exact hA'.comp (K.symm.toContinuousLinearMap.analyticAt _)

@[simp] theorem closedImmersionHolomorphicFlatteningChart_apply (y : ComplexPoint X) :
    closedImmersionHolomorphicFlatteningChart X Y i m d z y =
      closedImmersionStandardFlatteningChart X Y i m d z y := rfl

@[simp] theorem closedImmersionHolomorphicFlatteningChart_symm_apply
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ)) :
    (closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v =
      (localChart X d (Point.map i z)).symm
        ((closedImmersionNormalCoordinateChange X Y i m d z).symm v) := rfl

theorem closedImmersionHolomorphicFlatteningChart_mem_source :
    Point.map i z ∈
      (closedImmersionHolomorphicFlatteningChart X Y i m d z).source := by
  refine ⟨⟨mem_localChart_source X d (Point.map i z), ?_⟩,
    closedImmersionStandardFlatteningChart_mem_source X Y i m d z⟩
  apply (OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mpr
  refine ⟨closedImmersionNormalCoordinateChange_mem_source X Y i m d z,
    analyticAt_closedImmersionNormalCoordinateChange X Y i m d z, ?_⟩
  simp only [OpenPartialHomeomorph.symm_symm]
  rw [closedImmersionNormalCoordinateChange_center]
  exact analyticAt_closedImmersionNormalCoordinateChange_symm X Y i m d z

@[simp] theorem closedImmersionHolomorphicFlatteningChart_center :
    closedImmersionHolomorphicFlatteningChart X Y i m d z (Point.map i z) =
      (localChart Y m z z, 0) :=
  closedImmersionStandardFlatteningChart_center X Y i m d z

variable (z' : ComplexPoint Y)

/-- On a smaller transverse normal neighborhood in a genuine overlap, transition and
inclusion have exactly the same top relative-cohomology pullback. All holomorphic and
normal-derivative facts are obtained from the constructed closed-immersion charts. -/
theorem exists_open_closedImmersionNormalTransition_coclass_invariance (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition X Y i m d z z').source) :
    let T := closedImmersionNormalTransition X Y i m d z z'
    ∃ (W : Set (Fin (d - m) → ℂ)) (hW : W ⊆ normalTransitionDomain (d - m) T a)
      (hne : ∀ v, v ∈ W → v ≠ 0 → normalTransitionMap (d - m) T a v ≠ 0),
      IsOpen W ∧ 0 ∈ W ∧
      relativeCohomologyMap ℚ (2 * (d - m))
        (complexNeighborhoodPuncturedPairMapOf (d - m) W (normalTransitionMap (d - m) T a)
          ((normalTransitionMap_continuousOn (d - m) T a).mono hW) hne) =
        relativeCohomologyMap ℚ (2 * (d - m)) (neighborhoodPointComplementPairMap W 0) :=
  exists_open_normalTransition_relativeCohomologyMap_eq (d - m)
    (closedImmersionNormalTransition X Y i m d z z') a ha
    (closedImmersionNormalTransition_preserves_support X Y i m d z z')
    (analyticAt_closedImmersionNormalTransition X Y i m d z z' (a, 0) ha)
    (analyticAt_closedImmersionNormalTransition_symm X Y i m d z z' (a, 0) ha)

end AlgebraicGeometry.ComplexPoint
