/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.ClosedImmersionNormalCoordinates
public import HodgeConjecture.Other.AlgebraicTopology.HolomorphicNormalTransition

/-!
# Actual holomorphic support-flattening charts

Restricting to the open loci where a normal coordinate change and its inverse are analytic
upgrades centerwise analyticity to analyticity throughout each selected chart. All coordinate
changes come from the previously constructed smooth closed immersion; no holomorphic chart
compatibility or normal-orientation coherence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

/-- The actual open locus on which both directions of a coordinate change are analytic. -/
def biAnalyticLocus : Set E :=
  {x | AnalyticAt ℂ e x} ∩ (e.source ∩ e ⁻¹' {y | AnalyticAt ℂ e.symm y})

theorem biAnalyticLocus_isOpen : IsOpen e.biAnalyticLocus :=
  (isOpen_analyticAt ℂ e).inter (e.isOpen_inter_preimage (isOpen_analyticAt ℂ e.symm))

/-- Restricting to this proved open set introduces no analytic-equivalence input. -/
def biAnalyticRestrict : OpenPartialHomeomorph E F :=
  e.restrOpen e.biAnalyticLocus e.biAnalyticLocus_isOpen

@[simp] theorem biAnalyticRestrict_apply (x : E) : e.biAnalyticRestrict x = e x := rfl
@[simp] theorem biAnalyticRestrict_symm_apply (y : F) : e.biAnalyticRestrict.symm y = e.symm y := rfl

theorem biAnalyticRestrict_mem_source_iff (x : E) :
    x ∈ e.biAnalyticRestrict.source ↔
      x ∈ e.source ∧ AnalyticAt ℂ e x ∧ AnalyticAt ℂ e.symm (e x) := by
  change (x ∈ e.source ∧ AnalyticAt ℂ e x ∧ x ∈ e.source ∧ AnalyticAt ℂ e.symm (e x)) ↔ _
  aesop

end OpenPartialHomeomorph

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X Y : Scheme}
  (structureMapX : X ⟶ Spec (.of ℂ)) (structureMapY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ structureMapX = structureMapY) (m d : ℕ)
  [SmoothOfRelativeDimension m structureMapY] [SmoothOfRelativeDimension d structureMapX]
  [IsClosedImmersion i] (z : ComplexPoint Y structureMapY)

/-- The actual complex-linear identification of tangent and normal product coordinates. -/
def closedImmersionNormalCoordinatesLinearEquiv :
    ((Fin m → ℂ) ×
      (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z).ker) ≃L[ℂ]
        ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
    (closedImmersionNormalKernelEquiv structureMapX structureMapY i hi m d z)

/-- The normal coordinate change inside the canonical ambient complex chart. -/
def closedImmersionNormalCoordinateChange :
    OpenPartialHomeomorph (Fin d → ℂ) ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm.trans
    (closedImmersionNormalCoordinatesLinearEquiv structureMapX structureMapY i hi m d z).toHomeomorph.toOpenPartialHomeomorph

theorem closedImmersionNormalCoordinateChange_mem_source :
    localChart structureMapX d (Point.map i hi z) (Point.map i hi z) ∈
      (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z).source :=
  ⟨closedImmersionNormalChart_mem_target structureMapX structureMapY i hi m d z, trivial⟩

@[simp] theorem closedImmersionNormalCoordinateChange_center :
    closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z
      (localChart structureMapX d (Point.map i hi z) (Point.map i hi z)) =
        (localChart structureMapY m z z, 0) := by
  change closedImmersionNormalCoordinatesLinearEquiv structureMapX structureMapY i hi m d z
    ((closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm _) = _
  rw [closedImmersionNormalChart_symm_center]
  simp [closedImmersionNormalCoordinatesLinearEquiv]

theorem analyticAt_closedImmersionNormalCoordinateChange :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z)
      (localChart structureMapX d (Point.map i hi z) (Point.map i hi z)) := by
  exact ((closedImmersionNormalCoordinatesLinearEquiv structureMapX structureMapY i hi m d z).toContinuousLinearMap.analyticAt _).comp
    (analyticAt_closedImmersionNormalChart_symm structureMapX structureMapY i hi m d z)

theorem analyticAt_closedImmersionNormalCoordinateChange_symm :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z).symm
      (localChart structureMapY m z z, 0) := by
  let K := closedImmersionNormalCoordinatesLinearEquiv structureMapX structureMapY i hi m d z
  have hK : K.symm (localChart structureMapY m z z, 0) = (localChart structureMapY m z z, 0) := by
    simp [K, closedImmersionNormalCoordinatesLinearEquiv]
  have hA := analyticAt_closedImmersionNormalChart structureMapX structureMapY i hi m d z
  have hA' : AnalyticAt ℂ (closedImmersionNormalChart structureMapX structureMapY i hi m d z)
      (K.symm (localChart structureMapY m z z, 0)) := hK ▸ hA
  exact hA'.comp (K.symm.toContinuousLinearMap.analyticAt _)

/-- An actual support-flattening chart whose normal coordinate change is holomorphic in
both directions throughout its source. It contains the distinguished support point. -/
def closedImmersionHolomorphicFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint X structureMapX)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  ((localChart structureMapX d (Point.map i hi z)).trans
    (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z).biAnalyticRestrict).restrOpen
      (closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z).source
      (closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z).open_source

@[simp] theorem closedImmersionHolomorphicFlatteningChart_apply (y : ComplexPoint X structureMapX) :
    closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z y =
      closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z y := rfl

@[simp] theorem closedImmersionHolomorphicFlatteningChart_symm_apply
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ)) :
    (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).symm v =
      (localChart structureMapX d (Point.map i hi z)).symm
        ((closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z).symm v) := rfl

theorem closedImmersionHolomorphicFlatteningChart_mem_source :
    Point.map i hi z ∈
      (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source := by
  refine ⟨⟨mem_localChart_source structureMapX d (Point.map i hi z), ?_⟩,
    closedImmersionStandardFlatteningChart_mem_source structureMapX structureMapY i hi m d z⟩
  apply (OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mpr
  refine ⟨closedImmersionNormalCoordinateChange_mem_source structureMapX structureMapY i hi m d z,
    analyticAt_closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z, ?_⟩
  simp only [OpenPartialHomeomorph.symm_symm]
  rw [closedImmersionNormalCoordinateChange_center]
  exact analyticAt_closedImmersionNormalCoordinateChange_symm structureMapX structureMapY i hi m d z

@[simp] theorem closedImmersionHolomorphicFlatteningChart_center :
    closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z (Point.map i hi z) =
      (localChart structureMapY m z z, 0) :=
  closedImmersionStandardFlatteningChart_center structureMapX structureMapY i hi m d z

theorem closedImmersionHolomorphicFlatteningChart_mem_range_iff (y : ComplexPoint X structureMapX)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source) :
    y ∈ Set.range (Point.map i hi) ↔
      (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z y).2 = 0 :=
  closedImmersionStandardFlatteningChart_mem_range_iff structureMapX structureMapY i hi m d z y hy.2

/-- At every selected ambient source point, the underlying normal coordinate change and
its inverse are analytic, not only at the initially distinguished center. -/
theorem closedImmersionHolomorphicFlatteningChart_analytic (y : ComplexPoint X structureMapX)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source) :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z)
      (localChart structureMapX d (Point.map i hi z) y) ∧
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z).symm
      (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z y) :=
  ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hy.1.2).2

theorem closedImmersionNormalCoordinateChange_symm_at_chart (y : ComplexPoint X structureMapX)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source) :
    (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z).symm
      (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z y) =
        localChart structureMapX d (Point.map i hi z) y :=
  (closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z).left_inv hy.1.2.1

variable (z' : ComplexPoint Y structureMapY)

/-- The genuine transition between two constructed holomorphic support-flattening charts. -/
def closedImmersionNormalTransition :
    OpenPartialHomeomorph ((Fin m → ℂ) × (Fin (d - m) → ℂ))
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).symm.trans
    (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z')

/-- These actual transitions are holomorphic throughout their domains. -/
theorem analyticAt_closedImmersionNormalTransition
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').source) :
    AnalyticAt ℂ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z') v := by
  let e := closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z
  let e' := closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z'
  let C := localChart structureMapX d (Point.map i hi z)
  let C' := localChart structureMapX d (Point.map i hi z')
  let A := closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z
  let A' := closedImmersionNormalCoordinateChange structureMapX structureMapY i hi m d z'
  let y := e.symm v
  have hyv : y ∈ e.source := e.map_target hv.1
  have hyv' : y ∈ e'.source := hv.2
  have hyC : y ∈ C.source := hyv.1.1
  have hyC' : y ∈ C'.source := hyv'.1.1
  have hAv := closedImmersionNormalCoordinateChange_symm_at_chart
    structureMapX structureMapY i hi m d z y hyv
  change A.symm (e (e.symm v)) = C y at hAv
  rw [e.right_inv hv.1] at hAv
  have hA := (closedImmersionHolomorphicFlatteningChart_analytic
    structureMapX structureMapY i hi m d z y hyv).2
  change AnalyticAt ℂ A.symm (e (e.symm v)) at hA
  rw [e.right_inv hv.1] at hA
  have hA' := (closedImmersionHolomorphicFlatteningChart_analytic
    structureMapX structureMapY i hi m d z' y hyv').1
  have hCC : AnalyticAt ℂ (fun w => C' (C.symm w)) (C y) := by
    apply analyticAt_localChart_transition structureMapX d (Point.map i hi z) (Point.map i hi z')
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
    (hv : v ∈ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').source) :
    (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z' v).2 = 0 ↔ v.2 = 0 := by
  let e := closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z
  let e' := closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z'
  have hy := e.map_target hv.1
  have h1 := closedImmersionHolomorphicFlatteningChart_mem_range_iff
    structureMapX structureMapY i hi m d z (e.symm v) hy
  have h2 := closedImmersionHolomorphicFlatteningChart_mem_range_iff
    structureMapX structureMapY i hi m d z' (e.symm v) hv.2
  change e.symm v ∈ Set.range (Point.map i hi) ↔ (e (e.symm v)).2 = 0 at h1
  rw [e.right_inv hv.1] at h1
  exact h2.symm.trans h1

/-- The actual inverse transition is holomorphic at the image of every source point. -/
theorem analyticAt_closedImmersionNormalTransition_symm
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').source) :
    AnalyticAt ℂ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').symm
      (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z' v) := by
  have h := analyticAt_closedImmersionNormalTransition structureMapX structureMapY i hi m d z' z
    (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z' v)
    ((closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').map_source hv)
  exact h

/-- For a point in a genuine overlap, the normal derivative has a constructed complex
linear inverse. Only membership in the actual overlap is required. -/
def closedImmersionNormalTransitionDerivativeEquiv (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').source) :
    (Fin (d - m) → ℂ) ≃L[ℂ] (Fin (d - m) → ℂ) :=
  normalTransitionDerivativeEquiv
    (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z') a ha
    (closedImmersionNormalTransition_preserves_support structureMapX structureMapY i hi m d z z')
    (analyticAt_closedImmersionNormalTransition structureMapX structureMapY i hi m d z z' (a, 0) ha)
    (analyticAt_closedImmersionNormalTransition_symm structureMapX structureMapY i hi m d z z' (a, 0) ha)

@[simp] theorem closedImmersionNormalTransitionDerivativeEquiv_apply (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').source)
    (v : Fin (d - m) → ℂ) :
    closedImmersionNormalTransitionDerivativeEquiv structureMapX structureMapY i hi m d z z' a ha v =
      (fderiv ℂ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z')
        (a, 0) (0, v)).2 := rfl

/-- On a smaller transverse normal neighborhood in a genuine overlap, transition and
inclusion have exactly the same top relative-cohomology pullback. All holomorphic and
normal-derivative facts are obtained from the constructed closed-immersion charts. -/
theorem exists_open_closedImmersionNormalTransition_coclass_invariance (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').source) :
    let T := closedImmersionNormalTransition structureMapX structureMapY i hi m d z z'
    let h0 : normalTransitionMap (d - m) T a 0 = 0 :=
      (closedImmersionNormalTransition_preserves_support structureMapX structureMapY i hi m d z z'
        (a, 0) ha).mpr rfl
    ∃ (W : Set (Fin (d - m) → ℂ)) (hW : W ⊆ normalTransitionDomain (d - m) T a)
      (hne : ∀ v, v ∈ W → v ≠ 0 → normalTransitionMap (d - m) T a v ≠ 0),
      IsOpen W ∧ 0 ∈ W ∧
      relativeCohomologyMap ℚ (2 * (d - m))
        (complexNeighborhoodPuncturedPairMapOf (d - m) W (normalTransitionMap (d - m) T a)
          ((normalTransitionMap_continuousOn (d - m) T a).mono hW) h0 hne) =
        relativeCohomologyMap ℚ (2 * (d - m)) (neighborhoodPointComplementPairMap W 0) :=
  exists_open_normalTransition_relativeCohomologyMap_eq (d - m)
    (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z') a ha
    (closedImmersionNormalTransition_preserves_support structureMapX structureMapY i hi m d z z')
    (analyticAt_closedImmersionNormalTransition structureMapX structureMapY i hi m d z z' (a, 0) ha)
    (analyticAt_closedImmersionNormalTransition_symm structureMapX structureMapY i hi m d z z' (a, 0) ha)

end AlgebraicGeometry.ComplexPoint
