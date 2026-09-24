/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Differentials of extended charts

For a manifold `M` modelled on a boundaryless model with corners `I` with model vector space `F`,
the inverse `(extChartAt I p).symm` of an extended chart is smooth on the (open) target of the
chart and its differential at every point of the target is a linear isomorphism of `F`.

We also record the elementary consequences used in the construction of tubular neighbourhoods:
for a smooth map `e : M → E` into a normed space, the function `e ∘ (extChartAt I p).symm` is
smooth on the target of the chart, and its Fréchet derivative factors through `mfderiv e`.

Since `mfderiv I 𝓘(ℝ, E) e q` has type `TangentSpace I q →L[ℝ] TangentSpace 𝓘(ℝ, E) (e q)`,
which is only *definitionally* `F →L[ℝ] E`, we introduce `mfderivNormed I e q : F →L[ℝ] E` for
the same map with the syntactically simpler type; this is what makes the inner-product estimates
of `Other.Geometry.Manifold.NormalReach` elaborate.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The differential at `q` of a map `e` from a manifold to a normed space `E`, packaged as a
continuous linear map from the model space `F` to `E`. This is definitionally `mfderiv I 𝓘(ℝ, E)
e q`, but with a type that does not mention `TangentSpace`. -/
def mfderivNormed (I : ModelWithCorners ℝ F H) (e : M → E) (q : M) : F →L[ℝ] E :=
  mfderiv I 𝓘(ℝ, E) e q

omit [IsManifold I ∞ M] [I.Boundaryless] in
theorem mfderivNormed_injective_iff {e : M → E} {q : M} :
    Function.Injective (mfderivNormed I e q) ↔ Function.Injective (mfderiv I 𝓘(ℝ, E) e q) :=
  Iff.rfl

/-- The inverse of an extended chart is differentiable at each point of the chart's target. -/
theorem mdifferentiableAt_extChartAt_symm (p : M) {y : F} (hy : y ∈ (extChartAt I p).target) :
    MDifferentiableAt 𝓘(ℝ, F) I (extChartAt I p).symm y :=
  ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := I) p).mem_nhds hy)).mdifferentiableAt (by simp)

omit [I.Boundaryless] in
/-- An extended chart is differentiable at each point of its source. -/
theorem mdifferentiableAt_extChartAt' {p q : M} (hq : q ∈ (extChartAt I p).source) :
    MDifferentiableAt I 𝓘(ℝ, F) (extChartAt I p) q :=
  (contMDiffAt_extChartAt' (I := I) (n := ∞)
    (by rwa [← extChartAt_source I p])).mdifferentiableAt (by simp)

/-- The differential of the inverse of an extended chart is a linear isomorphism. -/
theorem mfderiv_extChartAt_symm_bijective (p : M) {y : F} (hy : y ∈ (extChartAt I p).target) :
    Function.Bijective (mfderiv 𝓘(ℝ, F) I (extChartAt I p).symm y) := by
  set φ := extChartAt I p with hφ
  set q := φ.symm y with hq
  have hqs : q ∈ φ.source := φ.map_target hy
  have hφq : φ q = y := φ.right_inv hy
  have hA : MDifferentiableAt 𝓘(ℝ, F) I φ.symm y := mdifferentiableAt_extChartAt_symm p hy
  have hB : MDifferentiableAt I 𝓘(ℝ, F) φ q := mdifferentiableAt_extChartAt' hqs
  have h1 : (φ.symm ∘ φ : M → M) =ᶠ[𝓝 q] id := by
    filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds hqs] with z hz
    exact φ.left_inv hz
  have h2 : (φ ∘ φ.symm : F → F) =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_extChartAt_target (I := I) p).mem_nhds hy] with z hz
    exact φ.right_inv hz
  have e1 : (mfderiv 𝓘(ℝ, F) I φ.symm y).comp (mfderiv I 𝓘(ℝ, F) φ q)
      = ContinuousLinearMap.id ℝ (TangentSpace I q) := by
    have h := mfderiv_comp (I := I) (I' := 𝓘(ℝ, F)) (I'' := I) q (f := φ) (g := φ.symm)
      (by rwa [hφq]) hB
    rw [hφq] at h
    rw [← h, h1.mfderiv_eq, mfderiv_id]
  have e2 : (mfderiv I 𝓘(ℝ, F) φ q).comp (mfderiv 𝓘(ℝ, F) I φ.symm y)
      = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, F) y) := by
    have h := mfderiv_comp (I := 𝓘(ℝ, F)) (I' := I) (I'' := 𝓘(ℝ, F)) y (f := φ.symm) (g := φ)
      hB hA
    rw [← h, h2.mfderiv_eq, mfderiv_id]
  have key2 : ∀ v : F, (mfderiv I 𝓘(ℝ, F) φ q) ((mfderiv 𝓘(ℝ, F) I φ.symm y) v) = v :=
    fun v => DFunLike.congr_fun e2 v
  have key1 : ∀ v : TangentSpace I q,
      (mfderiv 𝓘(ℝ, F) I φ.symm y) ((mfderiv I 𝓘(ℝ, F) φ q) v) = v :=
    fun v => DFunLike.congr_fun e1 v
  exact ⟨fun u v huv => by rw [← key2 u, ← key2 v, huv],
    fun v => ⟨mfderiv I 𝓘(ℝ, F) φ q v, key1 v⟩⟩

omit [I.Boundaryless] in
/-- Reading a smooth map into a normed space in a chart produces a smooth map on the (open)
target of that chart. -/
theorem contDiffOn_comp_extChartAt_symm {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e) (p : M) :
    ContDiffOn ℝ ∞ (e ∘ (extChartAt I p).symm) (extChartAt I p).target := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact he.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)

/-- The derivative of `e` read in a chart factors through the differential of `e`. -/
theorem fderiv_comp_extChartAt_symm_apply {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e) (p : M)
    {y : F} (hy : y ∈ (extChartAt I p).target) (u : F) :
    fderiv ℝ (e ∘ (extChartAt I p).symm) y u
      = mfderivNormed I e ((extChartAt I p).symm y)
          (mfderiv 𝓘(ℝ, F) I (extChartAt I p).symm y u) := by
  have h : fderiv ℝ (e ∘ (extChartAt I p).symm) y
      = (mfderiv I 𝓘(ℝ, E) e ((extChartAt I p).symm y)).comp
          (mfderiv 𝓘(ℝ, F) I (extChartAt I p).symm y) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp y (he.mdifferentiableAt (by simp))
      (mdifferentiableAt_extChartAt_symm p hy)
  exact DFunLike.congr_fun h u

/-- The image of the derivative of `e` read in a chart is exactly the image of `mfderiv e`. -/
theorem exists_preimage_fderiv_comp_extChartAt_symm {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e)
    (p : M) {y : F} (hy : y ∈ (extChartAt I p).target) (v : F) :
    ∃ u : F, fderiv ℝ (e ∘ (extChartAt I p).symm) y u
      = mfderivNormed I e ((extChartAt I p).symm y) v := by
  obtain ⟨u, hu⟩ := (mfderiv_extChartAt_symm_bijective p hy).2 v
  exact ⟨u, by rw [fderiv_comp_extChartAt_symm_apply he p hy u, hu]⟩

/-- If `mfderiv e p` is injective then so is the derivative of `e` read in a chart at `p`. -/
theorem injective_fderiv_comp_extChartAt_symm {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e)
    (p : M) {y : F} (hy : y ∈ (extChartAt I p).target)
    (hde : Function.Injective (mfderivNormed I e ((extChartAt I p).symm y))) :
    Function.Injective (fderiv ℝ (e ∘ (extChartAt I p).symm) y) := by
  intro u u' huu'
  rw [fderiv_comp_extChartAt_symm_apply he p hy u,
    fderiv_comp_extChartAt_symm_apply he p hy u'] at huu'
  exact (mfderiv_extChartAt_symm_bijective p hy).1 (hde huu')
