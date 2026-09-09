/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ClosedImmersionAnalyticLeftInverse
public import Other.AlgebraicGeometry.ProjectiveAnalytification
public import Other.AlgebraicTopology.SplitDerivativeNormalChart

/-!
# Constructed normal coordinates for smooth closed immersions

The derivative projection here comes from lifted algebraic coordinate sections. The normal
chart is then constructed by the inverse function theorem. Finally the actual topological
embedding theorem excludes remote branches and identifies the whole local analytic support
with zero normal coordinate. No analytic immersion or flattening equivalence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Scheme}
  (structureMapX : X ⟶ Spec (.of ℂ)) (structureMapY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ structureMapX = structureMapY) (m d : ℕ)
  [SmoothOfRelativeDimension m structureMapY] [SmoothOfRelativeDimension d structureMapX]
  [IsClosedImmersion i] (z : ComplexPoint Y structureMapY)

/-- The actual derivative left inverse obtained from lifted intrinsic coordinates. -/
def closedImmersionDerivativeProjection : (Fin d → ℂ) →L[ℂ] (Fin m → ℂ) :=
  (exists_leftInverse_fderiv_inclusionInComplexCharts
    structureMapX structureMapY i hi m d z).choose

theorem closedImmersionDerivativeProjection_leftInverse :
    (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z).comp
      (fderiv ℂ (inclusionInComplexCharts structureMapX structureMapY i hi m d z)
        (localChart structureMapY m z z)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) :=
  (exists_leftInverse_fderiv_inclusionInComplexCharts
    structureMapX structureMapY i hi m d z).choose_spec

/-- Actual normal-coordinate parametrization, with the kernel of the constructed
derivative projection as its complex normal space. -/
def closedImmersionNormalChart :
    OpenPartialHomeomorph
      ((Fin m → ℂ) ×
        (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z).ker)
      (Fin d → ℂ) :=
  (analyticAt_inclusionInComplexCharts structureMapX structureMapY i hi m d z).hasStrictFDerivAt.normalChart
    (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z)
    (closedImmersionDerivativeProjection_leftInverse structureMapX structureMapY i hi m d z)

@[simp] theorem closedImmersionNormalChart_apply
    (v : (Fin m → ℂ) ×
      (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z).ker) :
    closedImmersionNormalChart structureMapX structureMapY i hi m d z v =
      inclusionInComplexCharts structureMapX structureMapY i hi m d z v.1 + v.2 := rfl

theorem closedImmersionNormalChart_mem_source :
    (localChart structureMapY m z z, 0) ∈
      (closedImmersionNormalChart structureMapX structureMapY i hi m d z).source :=
  (analyticAt_inclusionInComplexCharts structureMapX structureMapY i hi m d z).hasStrictFDerivAt.normalChart_mem_source _ _

theorem closedImmersionNormalChart_mem_target :
    localChart structureMapX d (Point.map i hi z) (Point.map i hi z) ∈
      (closedImmersionNormalChart structureMapX structureMapY i hi m d z).target := by
  simpa only [closedImmersionNormalChart, inclusionInComplexCharts_at_center] using
    (analyticAt_inclusionInComplexCharts structureMapX structureMapY i hi m d z).hasStrictFDerivAt.normalChart_mem_target
      (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z)
      (closedImmersionDerivativeProjection_leftInverse structureMapX structureMapY i hi m d z)

@[simp] theorem closedImmersionNormalChart_symm_center :
    (closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm
      (localChart structureMapX d (Point.map i hi z) (Point.map i hi z)) =
        (localChart structureMapY m z z, 0) := by
  simpa using
    (closedImmersionNormalChart structureMapX structureMapY i hi m d z).left_inv
      (closedImmersionNormalChart_mem_source structureMapX structureMapY i hi m d z)

/-- The normal space has the actual complex codimension, by the constructed linear
splitting; algebraic dimension is not substituted for a topological dimension theorem. -/
theorem closedImmersionNormalKernel_finrank :
    Module.finrank ℂ
      (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z).ker =
        d - m := by
  have hdim :=
    ((fderiv ℂ (inclusionInComplexCharts structureMapX structureMapY i hi m d z)
      (localChart structureMapY m z z)).splitKernelEquiv
      (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z)
      (closedImmersionDerivativeProjection_leftInverse structureMapX structureMapY i hi m d z)).toLinearEquiv.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- The constructed normal parametrization is complex analytic at its center. -/
theorem analyticAt_closedImmersionNormalChart :
    AnalyticAt ℂ (closedImmersionNormalChart structureMapX structureMapY i hi m d z)
      (localChart structureMapY m z z, 0) := by
  let P := closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z
  change AnalyticAt ℂ
    (fun v : (Fin m → ℂ) × P.ker =>
      inclusionInComplexCharts structureMapX structureMapY i hi m d z v.1 + v.2) _
  exact ((analyticAt_inclusionInComplexCharts structureMapX structureMapY i hi m d z).comp
    (f := (ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker))
    (x := (localChart structureMapY m z z, 0))
    ((ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker).analyticAt _)).add
      ((P.ker.subtypeL.analyticAt _).comp
        ((ContinuousLinearMap.snd ℂ (Fin m → ℂ) P.ker).analyticAt _))

/-- The inverse normal coordinates are complex analytic as well, by the analytic inverse
function theorem applied to the actual invertible complex derivative. -/
theorem analyticAt_closedImmersionNormalChart_symm :
    AnalyticAt ℂ (closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm
      (localChart structureMapX d (Point.map i hi z) (Point.map i hi z)) := by
  let P := closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z
  let : CompleteSpace P.ker := FiniteDimensional.complete ℂ P.ker
  let e := closedImmersionNormalChart structureMapX structureMapY i hi m d z
  have ha := analyticAt_inclusionInComplexCharts structureMapX structureMapY i hi m d z
  have hd := ha.hasStrictFDerivAt.add_kernel P
    (closedImmersionDerivativeProjection_leftInverse structureMapX structureMapY i hi m d z)
  have hder : fderiv ℂ e (localChart structureMapY m z z, 0) =
      ((fderiv ℂ (inclusionInComplexCharts structureMapX structureMapY i hi m d z)
        (localChart structureMapY m z z)).splitKernelEquiv P
        (closedImmersionDerivativeProjection_leftInverse structureMapX structureMapY i hi m d z)).toContinuousLinearMap :=
    hd.hasFDerivAt.fderiv
  have h := e.analyticAt_symm'
    (closedImmersionNormalChart_mem_source structureMapX structureMapY i hi m d z)
    (analyticAt_closedImmersionNormalChart structureMapX structureMapY i hi m d z) hder
  simpa only [e, closedImmersionNormalChart_apply, Submodule.coe_zero, add_zero,
    inclusionInComplexCharts_at_center] using h

/-- Near the selected ambient point, membership in the entire actual image is equivalent
to having zero normal coordinate. The forward direction uses the proved induced topology
to exclude image points whose intrinsic parameters are outside the coordinate neighborhood. -/
theorem eventually_mem_range_iff_normal_eq_zero :
    ∀ᶠ y in 𝓝 (Point.map i hi z),
      y ∈ Set.range (Point.map i hi) ↔
        ((closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm
          (localChart structureMapX d (Point.map i hi z) y)).2 = 0 := by
  let eY := localChart structureMapY m z
  let eX := localChart structureMapX d (Point.map i hi z)
  let eN := closedImmersionNormalChart structureMapX structureMapY i hi m d z
  let g := Point.map i hi
  have hzY : z ∈ eY.source := mem_localChart_source structureMapY m z
  have hzX : g z ∈ eX.source := mem_localChart_source structureMapX d (g z)
  have hzN : (eY z, 0) ∈ eN.source :=
    closedImmersionNormalChart_mem_source structureMapX structureMapY i hi m d z
  have hzNt : eX (g z) ∈ eN.target :=
    closedImmersionNormalChart_mem_target structureMapX structureMapY i hi m d z
  have hcenter : eN.symm (eX (g z)) = (eY z, 0) :=
    closedImmersionNormalChart_symm_center structureMapX structureMapY i hi m d z
  have hparam : ∀ᶠ w in 𝓝 z, w ∈ eY.source ∧ (eY w, 0) ∈ eN.source := by
    filter_upwards [eY.open_source.mem_nhds hzY,
      ((eY.continuousAt hzY).prodMk continuousAt_const)
        (eN.open_source.mem_nhds hzN)] with w hwY hwN
    exact ⟨hwY, hwN⟩
  rw [(isInducing_map_of_closedImmersion hi).nhds_eq_comap z, eventually_comap] at hparam
  have hN : ∀ᶠ y in 𝓝 (g z), eX y ∈ eN.target :=
    (eX.continuousAt hzX) (eN.open_target.mem_nhds hzNt)
  have hc : ContinuousAt (fun y => (eN.symm (eX y)).1) (g z) :=
    ((eN.continuousAt_symm hzNt).comp (eX.continuousAt hzX)).fst
  have hback : ∀ᶠ y in 𝓝 (g z),
      g (eY.symm (eN.symm (eX y)).1) ∈ eX.source := by
    have hcont : ContinuousAt (fun y => g (eY.symm (eN.symm (eX y)).1)) (g z) := by
      apply (Point.continuous_map i hi).continuousAt.comp
      apply ContinuousAt.comp _ hc
      change ContinuousAt eY.symm (eN.symm (eX (g z))).1
      rw [hcenter]
      exact eY.continuousAt_symm (eY.map_source hzY)
    apply hcont (eX.open_source.mem_nhds _)
    change g (eY.symm (eN.symm (eX (g z))).1) ∈ eX.source
    rw [hcenter, eY.left_inv hzY]
    exact hzX
  filter_upwards [hparam, hN, hback, eX.open_source.mem_nhds hzX] with y hpre hyN hyback hyX
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨hwY, hwN⟩ := hpre w rfl
    have hφ : eN (eY w, 0) = eX (g w) := by
      change eX (g (eY.symm (eY w))) + 0 = _
      rw [eY.left_inv hwY, add_zero]
    have heq := eN.left_inv hwN
    rw [hφ] at heq
    exact congrArg Prod.snd heq
  · intro hn
    change (eN.symm (eX y)).2 = 0 at hn
    refine ⟨eY.symm (eN.symm (eX y)).1, ?_⟩
    apply eX.injOn hyback hyX
    have hright := eN.right_inv hyN
    change eX (g (eY.symm (eN.symm (eX y)).1)) + (eN.symm (eX y)).2 = eX y at hright
    rw [hn] at hright
    simpa only [Submodule.coe_zero, add_zero] using hright

/-- An actual open ambient neighborhood on which normal coordinates detect the full
closed-immersion image, extracted from the proved neighborhood assertion. -/
theorem exists_open_normalCriterion :
    ∃ W : Set (ComplexPoint X structureMapX), IsOpen W ∧ Point.map i hi z ∈ W ∧
      ∀ y ∈ W, y ∈ Set.range (Point.map i hi) ↔
        ((closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm
          (localChart structureMapX d (Point.map i hi z) y)).2 = 0 := by
  obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp
    (eventually_mem_range_iff_normal_eq_zero structureMapX structureMapY i hi m d z)
  exact ⟨W, hWopen, hzW, hWsub⟩

/-- The ambient flattening chart, restricted so that its zero-normal locus is exactly
the actual embedded support on its entire source. Every ingredient has been constructed
from the given smooth closed immersion. -/
def closedImmersionFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint X structureMapX)
      ((Fin m → ℂ) ×
        (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z).ker) :=
  ((localChart structureMapX d (Point.map i hi z)).trans
    (closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm).restrOpen
      (exists_open_normalCriterion structureMapX structureMapY i hi m d z).choose
      (exists_open_normalCriterion structureMapX structureMapY i hi m d z).choose_spec.1

@[simp] theorem closedImmersionFlatteningChart_apply (y : ComplexPoint X structureMapX) :
    closedImmersionFlatteningChart structureMapX structureMapY i hi m d z y =
      (closedImmersionNormalChart structureMapX structureMapY i hi m d z).symm
        (localChart structureMapX d (Point.map i hi z) y) := rfl

theorem closedImmersionFlatteningChart_mem_source :
    Point.map i hi z ∈
      (closedImmersionFlatteningChart structureMapX structureMapY i hi m d z).source :=
  ⟨⟨mem_localChart_source structureMapX d (Point.map i hi z),
      closedImmersionNormalChart_mem_target structureMapX structureMapY i hi m d z⟩,
    (exists_open_normalCriterion structureMapX structureMapY i hi m d z).choose_spec.2.1⟩

@[simp] theorem closedImmersionFlatteningChart_center :
    closedImmersionFlatteningChart structureMapX structureMapY i hi m d z (Point.map i hi z) =
      (localChart structureMapY m z z, 0) :=
  closedImmersionNormalChart_symm_center structureMapX structureMapY i hi m d z

/-- The complete geometric support is flattened, not merely a parametrized sub-piece. -/
theorem closedImmersionFlatteningChart_mem_range_iff (y : ComplexPoint X structureMapX)
    (hy : y ∈ (closedImmersionFlatteningChart structureMapX structureMapY i hi m d z).source) :
    y ∈ Set.range (Point.map i hi) ↔
      (closedImmersionFlatteningChart structureMapX structureMapY i hi m d z y).2 = 0 :=
  (exists_open_normalCriterion structureMapX structureMapY i hi m d z).choose_spec.2.2 y hy.2

/-- Identifying the actual normal space with standard complex coordinates uses only its
proved complex dimension. This is a complex-linear coordinate choice, not a choice of
homology generator or an orientation class. -/
def closedImmersionNormalKernelEquiv :
    (closedImmersionDerivativeProjection structureMapX structureMapY i hi m d z).ker ≃L[ℂ]
      (Fin (d - m) → ℂ) :=
  (LinearEquiv.ofFinrankEq _ _ (by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      closedImmersionNormalKernel_finrank structureMapX structureMapY i hi m d z)).toContinuousLinearEquiv

/-- The actual ambient support-flattening chart in standard tangent and normal complex
spaces, ready for the normal-slice pair calculation. -/
def closedImmersionStandardFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint X structureMapX)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionFlatteningChart structureMapX structureMapY i hi m d z).trans
    (((ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
      (closedImmersionNormalKernelEquiv structureMapX structureMapY i hi m d z)).toHomeomorph.toOpenPartialHomeomorph)

@[simp] theorem closedImmersionStandardFlatteningChart_apply (y : ComplexPoint X structureMapX) :
    closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z y =
      ((closedImmersionFlatteningChart structureMapX structureMapY i hi m d z y).1,
        closedImmersionNormalKernelEquiv structureMapX structureMapY i hi m d z
          (closedImmersionFlatteningChart structureMapX structureMapY i hi m d z y).2) := rfl

@[simp] theorem closedImmersionStandardFlatteningChart_source :
    (closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z).source =
      (closedImmersionFlatteningChart structureMapX structureMapY i hi m d z).source := by
  simp only [closedImmersionStandardFlatteningChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]

theorem closedImmersionStandardFlatteningChart_mem_source :
    Point.map i hi z ∈
      (closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z).source := by
  rw [closedImmersionStandardFlatteningChart_source]
  exact closedImmersionFlatteningChart_mem_source structureMapX structureMapY i hi m d z

@[simp] theorem closedImmersionStandardFlatteningChart_center :
    closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z
      (Point.map i hi z) = (localChart structureMapY m z z, 0) := by
  simp only [closedImmersionStandardFlatteningChart_apply, closedImmersionFlatteningChart_center,
    map_zero]

/-- The support is exactly the zero-normal plane throughout the actual chart source. -/
theorem closedImmersionStandardFlatteningChart_mem_range_iff (y : ComplexPoint X structureMapX)
    (hy : y ∈ (closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z).source) :
    y ∈ Set.range (Point.map i hi) ↔
      (closedImmersionStandardFlatteningChart structureMapX structureMapY i hi m d z y).2 = 0 := by
  rw [closedImmersionStandardFlatteningChart_source] at hy
  simpa only [closedImmersionStandardFlatteningChart_apply, ContinuousLinearEquiv.map_eq_zero_iff] using
    closedImmersionFlatteningChart_mem_range_iff structureMapX structureMapY i hi m d z y hy

end AlgebraicGeometry.ComplexPoint
