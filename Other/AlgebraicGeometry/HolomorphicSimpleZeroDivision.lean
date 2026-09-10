/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSimpleZeroDivision
public import Other.AlgebraicGeometry.HolomorphicOneFormLocalDivision

/-!
# Division of holomorphic functions by a function with simple zeros

On a one-dimensional complex manifold, a holomorphic function which vanishes
where a second holomorphic function vanishes is divisible by the second one,
provided all zeros of the denominator are simple.  The proof constructs the
quotient in a local chart and glues the local quotients.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Filter
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over (Spec (CommRingCat.of ℂ)))
  [SmoothOfRelativeDimension 1 X.hom]

/-- A one-dimensional chart section, expressed in the unique scalar
coordinate. -/
def scalarizedChartSection
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (f : OpenHolomorphicFunctions X 1 U) : ℂ → ℂ :=
  fun t ↦ chartSection X 1 U x f
    ((ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm t)

/-- The scalar coordinate of the center of the canonical chart. -/
def scalarizedChartCenter (x : ComplexPoint X) : ℂ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ (localChart X 1 x x)

theorem scalarizedChartSection_center
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hx : x ∈ Opposite.unop U)
    (f : OpenHolomorphicFunctions X 1 U) :
    scalarizedChartSection X U x f (scalarizedChartCenter X x) =
      f.1 ⟨x, hx⟩ := by
  rw [scalarizedChartSection, scalarizedChartCenter,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [chartSection_apply_of_mem X 1 U x f
    (localChart_center_mem_chartSectionDomain X U x hx)]
  simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, chartAt_eq_localChart,
    (localChart X 1 x).left_inv (mem_localChart_source X 1 x)]

theorem analyticAt_scalarizedChartSection
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hx : x ∈ Opposite.unop U)
    (f : OpenHolomorphicFunctions X 1 U) :
    AnalyticAt ℂ (scalarizedChartSection X U x f)
      (scalarizedChartCenter X x) := by
  let e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hc := localChart_center_mem_chartSectionDomain X U x hx
  have hf := (analyticOnNhd_chartSection X 1 U x f)
    (localChart X 1 x x) hc
  have hcenter : e.symm (scalarizedChartCenter X x) =
      localChart X 1 x x := by
    simp only [scalarizedChartCenter, e,
      ContinuousLinearEquiv.symm_apply_apply]
  have hcomp : AnalyticAt ℂ
      (fun t ↦ chartSection X 1 U x f (e.symm t))
      (scalarizedChartCenter X x) := by
    refine AnalyticAt.comp
      (g := chartSection X 1 U x f) (f := fun t ↦ e.symm t) ?_ ?_
    · simpa only [hcenter] using hf
    · exact e.symm.analyticAt _
  unfold scalarizedChartSection
  simpa only [e] using hcomp

/-- In one complex dimension, a nonzero coordinate derivative remains
nonzero after scalarizing the chart. -/
theorem deriv_scalarizedChartSection_ne_zero
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hx : x ∈ Opposite.unop U)
    (f : OpenHolomorphicFunctions X 1 U)
    (hf : fderiv ℂ (chartSection X 1 U x f)
      (localChart X 1 x x) ≠ 0) :
    deriv (scalarizedChartSection X U x f)
      (scalarizedChartCenter X x) ≠ 0 := by
  let e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hcenter := localChart_center_mem_chartSectionDomain X U x hx
  have hdiff : DifferentiableAt ℂ (chartSection X 1 U x f)
      (localChart X 1 x x) :=
    ((analyticOnNhd_chartSection X 1 U x f)
      (localChart X 1 x x) hcenter).differentiableAt
  have hcenterEq : e.symm (scalarizedChartCenter X x) =
      localChart X 1 x x := by
    simp only [scalarizedChartCenter, e,
      ContinuousLinearEquiv.symm_apply_apply]
  have hcomp : fderiv ℂ (scalarizedChartSection X U x f)
        (scalarizedChartCenter X x) =
      (fderiv ℂ (chartSection X 1 U x f)
        (localChart X 1 x x)).comp e.symm.toContinuousLinearMap := by
    have houter : HasFDerivAt (chartSection X 1 U x f)
        (fderiv ℂ (chartSection X 1 U x f) (localChart X 1 x x))
        (e.symm (scalarizedChartCenter X x)) := by
      simpa only [hcenterEq] using hdiff.hasFDerivAt
    have hc := houter.comp (scalarizedChartCenter X x) e.symm.hasFDerivAt
    unfold scalarizedChartSection
    simpa only [e, Function.comp_def] using hc.fderiv
  have hone : fderiv ℂ (chartSection X 1 U x f)
      (localChart X 1 x x) (fun _ ↦ 1) ≠ 0 := by
    intro h1
    apply hf
    ext v
    have hv : (v 0) • (fun _ : Fin 1 ↦ (1 : ℂ)) = v := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact congrArg v (Fin.eq_zero i).symm
    rw [← hv, map_smul, h1, smul_zero]
    rfl
  rw [← fderiv_apply_one_eq_deriv, hcomp,
    ContinuousLinearMap.comp_apply]
  have heone : e.symm (1 : ℂ) = (fun _ : Fin 1 ↦ (1 : ℂ)) := by
    rfl
  change fderiv ℂ (chartSection X 1 U x f)
      (localChart X 1 x x) (e.symm (1 : ℂ)) ≠ 0
  rw [heone]
  exact hone

/-- Local data for division around one point. The final field says that a
zero of the denominator in this neighborhood must be the chosen center. -/
structure HolomorphicSimpleZeroLocalDivision
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions X 1 U) (x : ComplexPoint X) where
  W : Opens (TopCat.of (ComplexPoint X))
  le_open : W ≤ Opposite.unop U
  mem : x ∈ W
  q : OpenHolomorphicFunctions X 1 (.op W)
  mul_eq :
    holomorphicRestrictionAlgHom X 1 (homOfLE le_open).op g * q =
      holomorphicRestrictionAlgHom X 1 (homOfLE le_open).op f
  zero_unique : ∀ (z : ComplexPoint X) (hz : z ∈ W),
    g.1 ⟨z, le_open hz⟩ = 0 → z = x

/-- Local analytic division at a simple zero. -/
theorem exists_holomorphicSimpleZeroLocalDivision_at_zero
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions X 1 U)
    (x : ComplexPoint X) (hx : x ∈ Opposite.unop U)
    (hfx : f.1 ⟨x, hx⟩ = 0) (hgx : g.1 ⟨x, hx⟩ = 0)
    (hg' : fderiv ℂ (chartSection X 1 U x g)
      (localChart X 1 x x) ≠ 0) :
    Nonempty (HolomorphicSimpleZeroLocalDivision X U f g x) := by
  let e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  let c := scalarizedChartCenter X x
  let F := scalarizedChartSection X U x f
  let G := scalarizedChartSection X U x g
  have hFa : AnalyticAt ℂ F c :=
    analyticAt_scalarizedChartSection X U x hx f
  have hGa : AnalyticAt ℂ G c :=
    analyticAt_scalarizedChartSection X U x hx g
  have hF0 : F c = 0 := by
    simpa only [F, c, scalarizedChartSection_center X U x hx f] using hfx
  have hG0 : G c = 0 := by
    simpa only [G, c, scalarizedChartSection_center X U x hx g] using hgx
  have hGderiv : deriv G c ≠ 0 := by
    exact deriv_scalarizedChartSection_ne_zero X U x hx g hg'
  obtain ⟨F₁, hF₁a, hF₁c, hFfactor⟩ :=
    hFa.exists_eq_sub_mul_analytic_deriv hF0
  obtain ⟨G₁, hG₁a, hG₁c, hGfactor⟩ :=
    hGa.exists_eq_sub_mul_analytic_deriv hG0
  have hG₁ne : G₁ c ≠ 0 := by simpa only [hG₁c] using hGderiv
  let Q : ℂ → ℂ := fun t ↦ F₁ t / G₁ t
  have hQa : AnalyticAt ℂ Q c := hF₁a.div hG₁a hG₁ne
  obtain ⟨r, hr, hQball⟩ := hQa.exists_ball_analyticOnNhd
  have hG₁event : ∀ᶠ t in nhds c, G₁ t ≠ 0 :=
    hG₁a.continuousAt.eventually_ne hG₁ne
  obtain ⟨T, hTsub, hTopen, hcT⟩ := mem_nhds_iff.mp hG₁event
  let scalarDomain : Set ℂ :=
    {t | e.symm t ∈ chartSectionDomain X 1 U x}
  have hScalarDomainOpen : IsOpen scalarDomain := by
    exact (isOpen_chartSectionDomain X 1 U x).preimage e.symm.continuous
  have hcScalarDomain : c ∈ scalarDomain := by
    change e.symm c ∈ chartSectionDomain X 1 U x
    simpa only [c, scalarizedChartCenter, e,
      ContinuousLinearEquiv.symm_apply_apply] using
        localChart_center_mem_chartSectionDomain X U x hx
  let D : Set ℂ := Metric.ball c r ∩ T ∩ scalarDomain
  have hDopen : IsOpen D :=
    (Metric.isOpen_ball.inter hTopen).inter hScalarDomainOpen
  have hcD : c ∈ D := by
    exact ⟨⟨Metric.mem_ball_self hr, hcT⟩, hcScalarDomain⟩
  have hDball : D ⊆ Metric.ball c r := fun _ ht ↦ ht.1.1
  have hDG₁ : ∀ t ∈ D, G₁ t ≠ 0 := fun _ ht ↦ hTsub ht.1.2
  have hQD : AnalyticOnNhd ℂ Q D := hQball.mono hDball
  let Dv : Set (Fin 1 → ℂ) := e ⁻¹' D
  have hDvOpen : IsOpen Dv := hDopen.preimage e.continuous
  let chart := localChart X 1 x
  let Wo : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨chart.source ∩ chart ⁻¹' Dv, chart.isOpen_inter_preimage hDvOpen⟩
  have hxsource : x ∈ chart.source := mem_localChart_source X 1 x
  have hxc : e (chart x) = c := rfl
  have hxWo : x ∈ Wo := ⟨hxsource, by
    change e (chart x) ∈ D
    rw [hxc]
    exact hcD⟩
  have hWoU : Wo ≤ Opposite.unop U := by
    intro z hz
    have hzD : e (chart z) ∈ D := hz.2
    have hzdom : e.symm (e (chart z)) ∈ chartSectionDomain X 1 U x := hzD.2
    rw [e.symm_apply_apply] at hzdom
    have hzu := hzdom.2
    change (localChart X 1 x).symm (localChart X 1 x z) ∈ Opposite.unop U at hzu
    rw [(localChart X 1 x).left_inv hz.1] at hzu
    exact hzu
  let W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ := .op Wo
  have hsourceW : ((Opposite.unop W : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin 1 → ℂ)) x).source := by
    intro z hz
    simpa only [W, Wo, chart, extChartAt_source,
      chartAt_eq_localChart X 1] using hz.1
  have hWDv (v : Fin 1 → ℂ) (hv : v ∈ chartSectionDomain X 1 W x) :
      v ∈ Dv := by
    have hpre : chart (chart.symm v) ∈ Dv := hv.2.2
    have hvtarget : v ∈ chart.target := by
      change v ∈ (localChart X 1 x).target
      simpa only [extChartAt_target, modelWithCornersSelf_coe_symm,
        Set.preimage_id, ModelWithCorners.range_eq_univ, Set.inter_univ,
        chartAt_eq_localChart X 1] using hv.1
    rwa [chart.right_inv hvtarget] at hpre
  let Qv : (Fin 1 → ℂ) → ℂ := fun v ↦ Q (e v)
  have hQDv : AnalyticOnNhd ℂ Qv Dv := by
    have he : AnalyticOnNhd ℂ (⇑e) Dv := fun v _ ↦ e.analyticAt v
    exact hQD.comp he (fun _ hv ↦ hv)
  have hQW : AnalyticOnNhd ℂ Qv (chartSectionDomain X 1 W x) :=
    hQDv.mono (fun v hv ↦ hWDv v hv)
  let q : OpenHolomorphicFunctions X 1 W :=
    holomorphicSectionOfChart X 1 W x hsourceW Qv hQW
  have hmul : holomorphicRestrictionAlgHom X 1
      (homOfLE hWoU).op g * q =
      holomorphicRestrictionAlgHom X 1 (homOfLE hWoU).op f := by
    apply ContMDiffMap.ext
    intro z
    let v : Fin 1 → ℂ := chart z.1
    have hzsource : z.1 ∈ chart.source := z.2.1
    have hvW : v ∈ chartSectionDomain X 1 W x := by
      refine ⟨?_, ?_⟩
      · simpa only [v, chart, extChartAt_target,
          modelWithCornersSelf_coe_symm, Set.preimage_id,
          ModelWithCorners.range_eq_univ, Set.inter_univ,
          chartAt_eq_localChart X 1] using chart.map_source hzsource
      · change chart.symm (chart z.1) ∈ Wo
        rw [chart.left_inv hzsource]
        exact z.2
    have hvU : v ∈ chartSectionDomain X 1 U x := by
      exact ⟨hvW.1, hWoU hvW.2⟩
    have hqval : q.1 z = Qv v := by
      change Qv ((extChartAt
        (modelWithCornersSelf ℂ (Fin 1 → ℂ)) x) z.1) = Qv v
      simp only [v, chart, extChartAt_coe, modelWithCornersSelf_coe,
        Function.comp_def, id_eq, chartAt_eq_localChart]
    have hfactor : chartSection X 1 U x g v * Qv v =
        chartSection X 1 U x f v := by
      have hF := hFfactor (e v)
      have hG := hGfactor (e v)
      have hne : G₁ (e v) ≠ 0 := hDG₁ (e v) (hWDv v hvW)
      change (e v - c) * F₁ (e v) =
        chartSection X 1 U x f (e.symm (e v)) at hF
      change (e v - c) * G₁ (e v) =
        chartSection X 1 U x g (e.symm (e v)) at hG
      rw [e.symm_apply_apply] at hF hG
      change chartSection X 1 U x g v * (F₁ (e v) / G₁ (e v)) =
        chartSection X 1 U x f v
      rw [← hF, ← hG]
      field_simp
    change g.1 ⟨z.1, hWoU z.2⟩ * q.1 z = f.1 ⟨z.1, hWoU z.2⟩
    rw [hqval]
    have hgval : chartSection X 1 U x g v = g.1 ⟨z.1, hWoU z.2⟩ := by
      rw [chartSection_apply_of_mem X 1 U x g hvU]
      apply congrArg g.1
      apply Subtype.ext
      change chart.symm (chart z.1) = z.1
      exact chart.left_inv hzsource
    have hfval : chartSection X 1 U x f v = f.1 ⟨z.1, hWoU z.2⟩ := by
      rw [chartSection_apply_of_mem X 1 U x f hvU]
      apply congrArg f.1
      apply Subtype.ext
      change chart.symm (chart z.1) = z.1
      exact chart.left_inv hzsource
    rw [← hgval, ← hfval]
    exact hfactor
  have hzero : ∀ (z : ComplexPoint X) (hz : z ∈ Wo),
      g.1 ⟨z, hWoU hz⟩ = 0 → z = x := by
    intro z hz hgz
    let v : Fin 1 → ℂ := chart z
    have hvD : e v ∈ D := hz.2
    have hne : G₁ (e v) ≠ 0 := hDG₁ (e v) hvD
    have hG := hGfactor (e v)
    have hvU : v ∈ chartSectionDomain X 1 U x := by
      have hvdom : e.symm (e v) ∈ chartSectionDomain X 1 U x := hvD.2
      simpa only [e.symm_apply_apply] using hvdom
    have hgval : chartSection X 1 U x g v = g.1 ⟨z, hWoU hz⟩ := by
      rw [chartSection_apply_of_mem X 1 U x g hvU]
      apply congrArg g.1
      apply Subtype.ext
      change chart.symm (chart z) = z
      exact chart.left_inv hz.1
    change (e v - c) * G₁ (e v) =
      chartSection X 1 U x g (e.symm (e v)) at hG
    rw [e.symm_apply_apply] at hG
    rw [hgval, hgz] at hG
    have heq : e v = c := by
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp hG).resolve_right hne
    have hvcenter : v = chart x := by
      apply e.injective
      simpa only [hxc] using heq
    calc
      z = chart.symm (chart z) := (chart.left_inv hz.1).symm
      _ = chart.symm (chart x) := congrArg chart.symm hvcenter
      _ = x := chart.left_inv hxsource
  exact ⟨⟨Wo, hWoU, hxWo, q, hmul, hzero⟩⟩

/-- Local division at a point where the denominator is already nonzero. -/
theorem exists_holomorphicSimpleZeroLocalDivision_of_ne_zero
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions X 1 U)
    (x : ComplexPoint X) (hx : x ∈ Opposite.unop U)
    (hgx : g.1 ⟨x, hx⟩ ≠ 0) :
    Nonempty (HolomorphicSimpleZeroLocalDivision X U f g x) := by
  let Uo : Opens (TopCat.of (ComplexPoint X)) := Opposite.unop U
  let T : Set Uo := {z | g.1 z ≠ 0}
  have hTopen : IsOpen T := isOpen_ne.preimage
    (holomorphicFunctionSheaf_section_analytic X 1 g).continuous
  let Wo : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨Subtype.val '' T,
      (Opposite.unop U).isOpen.isOpenMap_subtype_val T hTopen⟩
  have hWoU : Wo ≤ Uo := by
    rintro z ⟨w, _, rfl⟩
    exact w.2
  have hxWo : x ∈ Wo := ⟨⟨x, hx⟩, hgx, rfl⟩
  let W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ := .op Wo
  let fW := holomorphicRestrictionAlgHom X 1 (homOfLE hWoU).op f
  let gW := holomorphicRestrictionAlgHom X 1 (homOfLE hWoU).op g
  have hgW (z : Wo) : gW.1 z ≠ 0 := by
    rcases z.2 with ⟨w, hw, heq⟩
    have hzEq : (⟨z.1, hWoU z.2⟩ : Uo) = w :=
      Subtype.ext heq.symm
    change g.1 ⟨z.1, hWoU z.2⟩ ≠ 0
    rw [hzEq]
    exact hw
  let gu : (OpenHolomorphicFunctions X 1 W)ˣ := {
    val := gW
    inv := ⟨fun z ↦ (gW.1 z)⁻¹,
      (holomorphicFunctionSheaf_section_analytic X 1 gW).inv₀ hgW⟩
    val_inv := by
      apply ContMDiffMap.ext
      intro z
      exact mul_inv_cancel₀ (hgW z)
    inv_val := by
      apply ContMDiffMap.ext
      intro z
      exact inv_mul_cancel₀ (hgW z) }
  let q : OpenHolomorphicFunctions X 1 W := gu.inv * fW
  have hmul : gW * q = fW := by
    change gu.val * (gu.inv * fW) = fW
    rw [← mul_assoc, gu.val_inv, one_mul]
  have hzero : ∀ (z : ComplexPoint X) (hz : z ∈ Wo),
      g.1 ⟨z, hWoU hz⟩ = 0 → z = x := by
    intro z hz hgz
    exact (hgW ⟨z, hz⟩ hgz).elim
  exact ⟨⟨Wo, hWoU, hxWo, q, hmul, hzero⟩⟩

/-- Chosen local quotient around every point, under the global simple-zero
hypotheses. -/
def holomorphicSimpleZeroLocalDivision
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions X 1 U)
    (hvanish : ∀ (z : ComplexPoint X) (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 → f.1 ⟨z, hz⟩ = 0)
    (hsimple : ∀ (z : ComplexPoint X) (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 →
        fderiv ℂ (chartSection X 1 U z g) (localChart X 1 z z) ≠ 0)
    (x : {z : ComplexPoint X // z ∈ Opposite.unop U}) :
    HolomorphicSimpleZeroLocalDivision X U f g x.1 := by
  by_cases hgx : g.1 x = 0
  · exact (exists_holomorphicSimpleZeroLocalDivision_at_zero X U f g x.1 x.2
      (hvanish x.1 x.2 hgx) hgx (hsimple x.1 x.2 hgx)).some
  · exact (exists_holomorphicSimpleZeroLocalDivision_of_ne_zero
      X U f g x.1 x.2 hgx).some

/-- The chosen local quotients agree on pairwise intersections. -/
theorem holomorphicSimpleZeroLocalDivision_compatible
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions X 1 U)
    (hvanish : ∀ (z : ComplexPoint X) (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 → f.1 ⟨z, hz⟩ = 0)
    (hsimple : ∀ (z : ComplexPoint X) (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 →
        fderiv ℂ (chartSection X 1 U z g) (localChart X 1 z z) ≠ 0)
    (x y : {z : ComplexPoint X // z ∈ Opposite.unop U}) :
    let dx := holomorphicSimpleZeroLocalDivision X U f g hvanish hsimple x
    let dy := holomorphicSimpleZeroLocalDivision X U f g hvanish hsimple y
    holomorphicRestrictionAlgHom X 1
        (homOfLE (inf_le_left : dx.W ⊓ dy.W ≤ dx.W)).op dx.q =
      holomorphicRestrictionAlgHom X 1
        (homOfLE (inf_le_right : dx.W ⊓ dy.W ≤ dy.W)).op dy.q := by
  dsimp only
  let dx := holomorphicSimpleZeroLocalDivision X U f g hvanish hsimple x
  let dy := holomorphicSimpleZeroLocalDivision X U f g hvanish hsimple y
  apply ContMDiffMap.ext
  intro z
  have hzx : z.1 ∈ dx.W := z.2.1
  have hzy : z.1 ∈ dy.W := z.2.2
  have hzU : z.1 ∈ Opposite.unop U := dx.le_open hzx
  by_cases hg : g.1 ⟨z.1, hzU⟩ = 0
  · have hzx0 : z.1 = x.1 := dx.zero_unique z.1 hzx hg
    have hgy : g.1 ⟨z.1, dy.le_open hzy⟩ = 0 := by
      convert hg
    have hzy0 : z.1 = y.1 := dy.zero_unique z.1 hzy hgy
    have hxy : x = y := Subtype.ext (hzx0.symm.trans hzy0)
    subst y
    rfl
  · have hxmul := congrArg
      (fun s : OpenHolomorphicFunctions X 1 (.op dx.W) ↦ s.1 ⟨z.1, hzx⟩)
      dx.mul_eq
    have hymul := congrArg
      (fun s : OpenHolomorphicFunctions X 1 (.op dy.W) ↦ s.1 ⟨z.1, hzy⟩)
      dy.mul_eq
    change g.1 ⟨z.1, dx.le_open hzx⟩ * dx.q.1 ⟨z.1, hzx⟩ =
      f.1 ⟨z.1, dx.le_open hzx⟩ at hxmul
    change g.1 ⟨z.1, dy.le_open hzy⟩ * dy.q.1 ⟨z.1, hzy⟩ =
      f.1 ⟨z.1, dy.le_open hzy⟩ at hymul
    change dx.q.1 ⟨z.1, hzx⟩ = dy.q.1 ⟨z.1, hzy⟩
    apply mul_left_cancel₀ hg
    calc
      g.1 ⟨z.1, hzU⟩ * dx.q.1 ⟨z.1, hzx⟩ =
          f.1 ⟨z.1, hzU⟩ := by convert hxmul
      _ = g.1 ⟨z.1, hzU⟩ * dy.q.1 ⟨z.1, hzy⟩ := by
        convert hymul.symm

/-- Global holomorphic division by a function whose zeros are all simple. -/
theorem exists_holomorphic_quotient_of_vanishes_on_simple_zeros
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions X 1 U)
    (hvanish : ∀ (z : ComplexPoint X) (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 → f.1 ⟨z, hz⟩ = 0)
    (hsimple : ∀ (z : ComplexPoint X) (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 →
        fderiv ℂ (chartSection X 1 U z g) (localChart X 1 z z) ≠ 0) :
    ∃ q : OpenHolomorphicFunctions X 1 U, g * q = f := by
  let Uo : Opens (TopCat.of (ComplexPoint X)) := Opposite.unop U
  let I := {z : ComplexPoint X // z ∈ Uo}
  let d : (x : I) → HolomorphicSimpleZeroLocalDivision X U f g x.1 :=
    fun x ↦ holomorphicSimpleZeroLocalDivision X U f g hvanish hsimple x
  let V : I → Opens (TopCat.of (ComplexPoint X)) := fun x ↦ (d x).W
  let sf : ∀ x, (holomorphicFunctionSheaf X 1).presheaf.obj (.op (V x)) :=
    fun x ↦ (d x).q
  have hcompat : TopCat.Presheaf.IsCompatible
      (holomorphicFunctionSheaf X 1).presheaf V sf := by
    intro x y
    change holomorphicRestrictionAlgHom X 1
        (homOfLE (inf_le_left : (d x).W ⊓ (d y).W ≤ (d x).W)).op (d x).q =
      holomorphicRestrictionAlgHom X 1
        (homOfLE (inf_le_right : (d x).W ⊓ (d y).W ≤ (d y).W)).op (d y).q
    exact holomorphicSimpleZeroLocalDivision_compatible
      X U f g hvanish hsimple x y
  have hcover : Uo ≤ iSup V := by
    intro z hz
    let x : I := ⟨z, hz⟩
    exact (le_iSup V x) (d x).mem
  obtain ⟨q, hq, _⟩ := (holomorphicFunctionSheaf X 1).existsUnique_gluing'
    V Uo (fun x ↦ homOfLE (d x).le_open) hcover sf hcompat
  simp only [Uo, Opposite.op_unop] at q hq
  change OpenHolomorphicFunctions X 1 U at q
  have hmul : g * q = f := by
    apply ContMDiffMap.ext
    intro z
    let x : I := ⟨z.1, z.2⟩
    let dx := d x
    have hqz := congrArg
      (fun s : OpenHolomorphicFunctions X 1 (.op dx.W) ↦
        s.1 ⟨z.1, dx.mem⟩) (hq x)
    have hm := congrArg
      (fun s : OpenHolomorphicFunctions X 1 (.op dx.W) ↦
        s.1 ⟨z.1, dx.mem⟩) dx.mul_eq
    change q.1 z = dx.q.1 ⟨z.1, dx.mem⟩ at hqz
    change g.1 z * dx.q.1 ⟨z.1, dx.mem⟩ = f.1 z at hm
    change g.1 z * q.1 z = f.1 z
    rw [hqz]
    exact hm
  exact ⟨q, hmul⟩

end AlgebraicGeometry.ComplexPoint
