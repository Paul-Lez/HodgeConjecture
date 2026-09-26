/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceAn
public import Other.Oka.AnalyticSpace.Evaluation
public import Other.Oka.StalkEquiv
public import Other.Oka.Analytic.OkaRingDifferentiable
public import Other.Oka.Analytic.ParametricCircleIntegral

/-!
# Sections of `𝒪_{ℙⁿ_an}` as functions on the cone

For an open `W ⊆ ℙⁿ_an` let `vecCone W = {v ∈ ℂⁿ⁺¹ ∖ 0 | [v] ∈ W}`. A section `s` of the
structure sheaf over `W` gives the function `secFun s : v ↦ s([v])` (zero off the cone), which is
homogeneous of degree `0` (`secFun_smul`) and holomorphic on the open cone
(`isOpen_vecCone`, `differentiableOn_secFun`): in the chart `i` it is the pulled back holomorphic
function composed with the dehomogenisation `v ↦ (v_{i.succAbove m} / vᵢ)ₘ`
(`secFun_eq_chartSec`). A section is determined by these values (`eq_of_secFun`), and every
holomorphic function of degree `0` on the cone over an open contained in a chart is of this form
(`exists_secFun_eq`). `secFun` is additive, multiplicative and compatible with restriction
(`secFun_restrictOpen`).

Along the way: on `ℂⁿ`, the value of a section over any open `U` is its value as a holomorphic
function (`ComplexAnalytic.eval_complexAffineSpace_of`), and evaluation commutes with restriction
(`ComplexAnalytic.AnalyticSpace.eval_restrictOpen`).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

variable {n : ℕ}

/-- **On `ℂⁿ` the value of a section over an open `U` is its value as a holomorphic
function.** -/
theorem eval_complexAffineSpace_of
    {U : TopologicalSpace.Opens (AnalyticSpace.complexAffineSpace.{u} n)}
    (y : AnalyticSpace.complexAffineSpace.{u} n) (hy : y ∈ U)
    (s : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op U)) :
    (AnalyticSpace.complexAffineSpace.{u} n).eval y hy s =
      OkaRing.evalHom (U := (U : Opens (ULift.{u} (Fin n) → ℂ))) (x := y) hy s := by
  set c := OkaRing.evalHom (U := (U : Opens (ULift.{u} (Fin n) → ℂ))) (x := y) hy s with hc
  refine ((AnalyticSpace.complexAffineSpace.{u} n).evalStalk_eq_iff _ _).2 ?_
  have hres : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.germ ⊤ y trivial
      ((AnalyticSpace.complexAffineSpace.{u} n).algebraMap c) =
      (AnalyticSpace.complexAffineSpace.{u} n).presheaf.germ U y hy
        (algebraMap ℂ (OkaRing (U : Opens (ULift.{u} (Fin n) → ℂ))) c) :=
    ((AnalyticSpace.complexAffineSpace.{u} n).presheaf.germ_res_apply (homOfLE le_top) y hy
      ((AnalyticSpace.complexAffineSpace.{u} n).algebraMap c)).symm
  rw [AnalyticSpace.stalkAlgMap, LocallyRingedSpace.stalkAlgMap_apply]
  refine (congrArg (_ - ·) hres).symm ▸ ?_
  rw [← map_sub]
  exact (germ_mem_maximalIdeal_iff (ι := ULift.{u} (Fin n)) (y := y) hy _).2
    ((map_sub (OkaRing.evalHom (U := (U : Opens (ULift.{u} (Fin n) → ℂ))) (x := y) hy)
        s _).trans (sub_eq_zero.2 (hc.trans (OkaRing.evalHom_algebraMap hy c).symm)))


/-- Evaluation commutes with restriction. -/
lemma AnalyticSpace.eval_restrictOpen (Z : AnalyticSpace.{u}) {U W : Opens Z} (h : W ≤ U) (z : Z)
    (hz : z ∈ W) (s : Z.presheaf.obj (op U)) :
    Z.eval z hz (TopCat.Presheaf.restrictOpen s W h) = Z.eval z (h hz) s := by
  rw [AnalyticSpace.eval_apply, AnalyticSpace.eval_apply]
  exact congrArg _ (Z.presheaf.germ_res_apply (homOfLE h) z hz s)

end ComplexAnalytic

namespace ComplexAnalytic.projectiveSpaceAn

open AnalyticSpace ProjectiveSpace

variable {n : ℕ}

/-- The chart `i` of `ℙⁿ_an`, as a morphism of locally ringed spaces. -/
noncomputable abbrev chartLRS (i : Fin (n + 1)) :
    (AnalyticSpace.complexAffineSpace.{u} n).toLocallyRingedSpace ⟶
      (projectiveSpaceAn.{u} n).toLocallyRingedSpace :=
  (projectiveSpaceAnChart.{u} i).toLRSHom

/-- The value of a section of `𝒪_{ℙⁿ_an}` at a point of the chart `i` is the value of its
pullback, a holomorphic function on an open of `ℂⁿ`. -/
lemma eval_chart {W : (projectiveSpaceAn.{u} n).Opens} (i : Fin (n + 1))
    (z : AnalyticSpace.complexAffineSpace.{u} n) (hz : (chartLRS i).base z ∈ W)
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) :
    (projectiveSpaceAn.{u} n).eval _ hz s =
      OkaRing.evalHom (U := ((Opens.map (chartLRS i).base).obj W :
        TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ))) (x := z) hz
        ((chartLRS i).c.app (op W) s) :=
  (eval_c_app _ (projectiveSpaceAnChart.{u} i).isCLinear z hz s).symm.trans
    (eval_complexAffineSpace_of z hz _)

/-- The cone `{v ≠ 0 | [v] ∈ W}` over an open `W ⊆ ℙⁿ_an`. -/
def vecCone (W : (projectiveSpaceAn.{u} n).Opens) : Set (Fin (n + 1) → ℂ) :=
  {v | ∃ hv : v ≠ 0, pointOfVec.{u} v hv ∈ W}

lemma mem_vecCone_iff {W : (projectiveSpaceAn.{u} n).Opens} {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    v ∈ vecCone.{u} W ↔ pointOfVec.{u} v hv ∈ W :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hv, h⟩⟩

lemma ne_zero_of_mem_vecCone {W : (projectiveSpaceAn.{u} n).Opens} {v : Fin (n + 1) → ℂ}
    (h : v ∈ vecCone.{u} W) : v ≠ 0 :=
  h.1

lemma smul_mem_vecCone {W : (projectiveSpaceAn.{u} n).Opens} {v : Fin (n + 1) → ℂ}
    (h : v ∈ vecCone.{u} W) {c : ℂ} (hc : c ≠ 0) : c • v ∈ vecCone.{u} W :=
  ⟨smul_ne_zero hc h.1, by rw [pointOfVec_smul _ _ hc]; exact h.2⟩

lemma vecCone_mono {W W' : (projectiveSpaceAn.{u} n).Opens} (h : W' ≤ W) :
    vecCone.{u} W' ⊆ vecCone.{u} W :=
  fun _ ⟨hv, hW⟩ ↦ ⟨hv, h hW⟩

lemma eval_congr_point {W : (projectiveSpaceAn.{u} n).Opens} {y y' : projectiveSpaceAn.{u} n}
    (h : y = y') (hy : y ∈ W) (hy' : y' ∈ W)
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) :
    (projectiveSpaceAn.{u} n).eval y hy s = (projectiveSpaceAn.{u} n).eval y' hy' s := by
  subst h
  rfl

open scoped Classical in
/-- A section of `𝒪_{ℙⁿ_an}` over `W`, as a function on `ℂⁿ⁺¹` (homogeneous of degree `0` on
the cone over `W`, zero off it). -/
noncomputable def secFun {W : (projectiveSpaceAn.{u} n).Opens}
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) (v : Fin (n + 1) → ℂ) : ℂ :=
  if h : v ∈ vecCone.{u} W then (projectiveSpaceAn.{u} n).eval (pointOfVec.{u} v h.1) h.2 s else 0

lemma secFun_of_mem {W : (projectiveSpaceAn.{u} n).Opens}
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) {v : Fin (n + 1) → ℂ} (hv : v ≠ 0)
    (hW : pointOfVec.{u} v hv ∈ W) :
    secFun s v = (projectiveSpaceAn.{u} n).eval (pointOfVec.{u} v hv) hW s := by
  classical
  rw [secFun, dif_pos ⟨hv, hW⟩]

lemma secFun_of_notMem {W : (projectiveSpaceAn.{u} n).Opens}
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) {v : Fin (n + 1) → ℂ}
    (h : v ∉ vecCone.{u} W) : secFun s v = 0 := by
  classical
  rw [secFun, dif_neg h]

lemma secFun_smul {W : (projectiveSpaceAn.{u} n).Opens}
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) (v : Fin (n + 1) → ℂ) {c : ℂ}
    (hc : c ≠ 0) : secFun s (c • v) = secFun s v := by
  by_cases h : v ∈ vecCone.{u} W
  · rw [secFun_of_mem s h.1 h.2, secFun_of_mem s (smul_ne_zero hc h.1)
      (by rw [pointOfVec_smul _ _ hc]; exact h.2)]
    exact eval_congr_point (pointOfVec_smul v h.1 hc) _ _ s
  · rw [secFun_of_notMem s h, secFun_of_notMem s fun h' ↦ h (by
      simpa [smul_smul, inv_mul_cancel₀ hc] using smul_mem_vecCone h' (inv_ne_zero hc))]


variable {W : (projectiveSpaceAn.{u} n).Opens}

lemma secFun_add (s t : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) (v : Fin (n + 1) → ℂ) :
    secFun (s + t) v = secFun s v + secFun t v := by
  by_cases h : v ∈ vecCone.{u} W
  · rw [secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, map_add]
  · rw [secFun_of_notMem _ h, secFun_of_notMem _ h, secFun_of_notMem _ h, add_zero]

lemma secFun_mul (s t : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) (v : Fin (n + 1) → ℂ) :
    secFun (s * t) v = secFun s v * secFun t v := by
  by_cases h : v ∈ vecCone.{u} W
  · rw [secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, map_mul]
  · rw [secFun_of_notMem _ h, secFun_of_notMem _ h, secFun_of_notMem _ h, mul_zero]

lemma secFun_zero (v : Fin (n + 1) → ℂ) :
    secFun (0 : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) v = 0 := by
  by_cases h : v ∈ vecCone.{u} W
  · rw [secFun_of_mem _ h.1 h.2, map_zero]
  · rw [secFun_of_notMem _ h]

lemma secFun_restrictOpen {W' : (projectiveSpaceAn.{u} n).Opens} (h : W' ≤ W)
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) (v : Fin (n + 1) → ℂ) :
    secFun (TopCat.Presheaf.restrictOpen s W' h) v = (vecCone.{u} W').indicator (secFun s) v := by
  by_cases hv : v ∈ vecCone.{u} W'
  · rw [Set.indicator_of_mem hv, secFun_of_mem _ hv.1 hv.2, secFun_of_mem _ hv.1 (h hv.2),
      AnalyticSpace.eval_restrictOpen]
  · rw [Set.indicator_of_notMem hv, secFun_of_notMem _ hv]

/-- The dehomogenisation `v ↦ (v_{i.succAbove m} / vᵢ)ₘ`, as a point of `ℂⁿ`. -/
noncomputable def dehomOf (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) :
    AnalyticSpace.complexAffineSpace.{u} n :=
  ofFin (dehomogenizeVec i v)

lemma dehomOf_apply (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (k : ULift.{u} (Fin n)) :
    (dehomOf.{u} i v : ULift.{u} (Fin n) → ℂ) k = v (i.succAbove k.down) / v i :=
  rfl

lemma homogCoord_dehomOf (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (hi : v i ≠ 0) :
    homogCoord i (dehomOf.{u} i v) = (v i)⁻¹ • v := by
  rw [homogCoord, dehomOf, toFin_ofFin, insertNth_dehomogenizeVec i v hi]

lemma pointOfVec_eq_chart (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i : Fin (n + 1)) (hi : v i ≠ 0) :
    pointOfVec.{u} v hv = (chartLRS i).base (dehomOf.{u} i v) :=
  pointOfVec_eq v hv i hi

/-- `dehomOf` as a map to `ULift (Fin n) → ℂ`. -/
noncomputable def dehomVec (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) : ULift.{u} (Fin n) → ℂ :=
  fun k ↦ v (i.succAbove k.down) / v i

lemma dehomOf_eq_dehomVec (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) :
    (dehomOf.{u} i v : ULift.{u} (Fin n) → ℂ) = dehomVec.{u} i v :=
  rfl

lemma continuousOn_dehomVec (i : Fin (n + 1)) :
    ContinuousOn (dehomVec.{u} i) {v | v i ≠ 0} := by
  refine continuousOn_pi.2 fun k ↦ ?_
  exact ((continuous_apply _).continuousOn).div (continuous_apply i).continuousOn fun v hv ↦ hv

lemma differentiableAt_dehomVec (i : Fin (n + 1)) {v : Fin (n + 1) → ℂ} (hi : v i ≠ 0) :
    DifferentiableAt ℂ (dehomVec.{u} i) v := by
  refine differentiableAt_pi.2 fun k ↦ ?_
  change DifferentiableAt ℂ (fun w : Fin (n + 1) → ℂ ↦ w (i.succAbove k.down) / w i) v
  simp_rw [div_eq_mul_inv]
  exact (differentiableAt_apply (𝕜 := ℂ) _ _).mul ((differentiableAt_apply (𝕜 := ℂ) i _).inv hi)


/-- The preimage of `W` in the chart `i`, as an open of `ℂⁿ`. -/
noncomputable abbrev chartPreimage (i : Fin (n + 1)) (W : (projectiveSpaceAn.{u} n).Opens) :
    TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ) :=
  (Opens.map (chartLRS.{u} i).base).obj W

/-- The pullback of a section along the chart `i`, a holomorphic function. -/
noncomputable abbrev chartSec (i : Fin (n + 1))
    (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) : OkaRing (chartPreimage.{u} i W) :=
  (chartLRS.{u} i).c.app (op W) s

/-- **In the chart `i`, `secFun s` is the pulled back holomorphic function of the
dehomogenisation.** -/
lemma secFun_eq_chartSec (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W))
    {v : Fin (n + 1) → ℂ} (i : Fin (n + 1)) (hi : v i ≠ 0) (hv : v ∈ vecCone.{u} W) :
    secFun s v = (chartSec i s).toGlobalFun _ (dehomVec.{u} i v) := by
  have hz : (chartLRS i).base (dehomOf.{u} i v) ∈ W := by
    rw [← pointOfVec_eq_chart v hv.1 i hi]; exact hv.2
  rw [secFun_of_mem s hv.1 hv.2, eval_congr_point (pointOfVec_eq_chart v hv.1 i hi) _ hz,
    eval_chart i _ hz, OkaRing.toGlobalFun_apply _ hz]
  rfl

lemma mem_vecCone_iff_chart {v : Fin (n + 1) → ℂ} (i : Fin (n + 1)) (hi : v i ≠ 0) :
    v ∈ vecCone.{u} W ↔ dehomVec.{u} i v ∈ chartPreimage.{u} i W := by
  have hv : v ≠ 0 := fun h ↦ hi (by simp [h])
  rw [mem_vecCone_iff hv, pointOfVec_eq_chart v hv i hi]
  rfl

lemma isOpen_vecCone : IsOpen (vecCone.{u} W) := by
  have : vecCone.{u} W = ⋃ i, {v | v i ≠ 0} ∩ dehomVec.{u} i ⁻¹' (chartPreimage.{u} i W) := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      SetLike.mem_coe]
    refine ⟨fun hv ↦ ?_, fun ⟨i, hi, h⟩ ↦ (mem_vecCone_iff_chart i hi).2 h⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv.1
    exact ⟨i, hi, (mem_vecCone_iff_chart i hi).1 hv⟩
  rw [this]
  exact isOpen_iUnion fun i ↦ (continuousOn_dehomVec i).isOpen_inter_preimage
    (isOpen_ne_fun (continuous_apply i) continuous_const) (chartPreimage i W).isOpen

/-- **Sections of `𝒪_{ℙⁿ_an}` are holomorphic on the cone.** -/
lemma differentiableOn_secFun (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) :
    DifferentiableOn ℂ (secFun s) (vecCone.{u} W) := by
  intro v hv
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv.1
  refine DifferentiableAt.differentiableWithinAt ?_
  have hN : {w : Fin (n + 1) → ℂ | w i ≠ 0} ∩ vecCone.{u} W ∈ 𝓝 v :=
    ((isOpen_ne_fun (continuous_apply i) continuous_const).inter isOpen_vecCone).mem_nhds ⟨hi, hv⟩
  have heq : (chartSec i s).toGlobalFun _ ∘ dehomVec.{u} i =ᶠ[𝓝 v] secFun s := by
    filter_upwards [hN] with w hw
    exact (secFun_eq_chartSec s i hw.1 hw.2).symm
  refine (DifferentiableAt.comp v ?_ (differentiableAt_dehomVec i hi)).congr_of_eventuallyEq
    heq.symm
  have hz := (mem_vecCone_iff_chart i hi).1 hv
  exact ((chartSec i s).differentiableOn_toGlobalFun _ hz).differentiableAt
    ((chartPreimage i W).isOpen.mem_nhds hz)


lemma chartSec_toGlobalFun_eq (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W)) (i : Fin (n + 1))
    {z : AnalyticSpace.complexAffineSpace.{u} n} (hz : (chartLRS i).base z ∈ W) :
    (chartSec i s).toGlobalFun _ z = secFun s (homogCoord i z) := by
  have hv := homogCoord_ne_zero i z
  have hW : pointOfVec.{u} (homogCoord i z) hv ∈ W := by rw [← chart_eq_pointOfVec]; exact hz
  rw [secFun_of_mem s hv hW, ← eval_congr_point (chart_eq_pointOfVec i z) hz hW, eval_chart i z hz,
    OkaRing.toGlobalFun_apply _ hz]
  rfl

/-- **A section of `𝒪_{ℙⁿ_an}` is determined by its values.** -/
lemma eq_zero_of_secFun (s : (projectiveSpaceAn.{u} n).presheaf.obj (op W))
    (h : ∀ v ∈ vecCone.{u} W, secFun s v = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext (projectiveSpaceAn.{u} n).sheaf W s 0 fun y hy ↦ ?_
  obtain ⟨i, z, rfl⟩ := exists_mem_range_chart y
  have h0 : chartSec i s = 0 := by
    refine OkaRing.ext (funext fun w ↦ ?_)
    rw [← OkaRing.toGlobalFun_apply _ w.2, chartSec_toGlobalFun_eq s i w.2]
    exact h _ ⟨homogCoord_ne_zero i _, by rw [← chart_eq_pointOfVec]; exact w.2⟩
  apply (ConcreteCategory.bijective_of_isIso ((chartLRS i).stalkMap z)).1
  change (chartLRS i).stalkMap z ((projectiveSpaceAn.{u} n).presheaf.germ W _ hy s) =
    (chartLRS i).stalkMap z ((projectiveSpaceAn.{u} n).presheaf.germ W _ hy 0)
  rw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply, map_zero]
  exact congrArg _ h0

lemma eq_of_secFun {s t : (projectiveSpaceAn.{u} n).presheaf.obj (op W)}
    (h : ∀ v ∈ vecCone.{u} W, secFun s v = secFun t v) : s = t := by
  rw [← sub_eq_zero]
  refine eq_zero_of_secFun _ fun v hv ↦ ?_
  rw [sub_eq_add_neg, secFun_add, h v hv, ← secFun_add, ← sub_eq_add_neg, sub_self, secFun_zero]


lemma analyticAt_homogCoord (j : Fin (n + 1)) (z : ULift.{u} (Fin n) → ℂ) :
    AnalyticAt ℂ (fun z : ULift.{u} (Fin n) → ℂ ↦ homogCoord.{u} j z) z := by
  refine analyticAt_pi_iff.2 fun k ↦ ?_
  obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simp only [homogCoord, Fin.insertNth_apply_same]
    exact analyticAt_const
  · simp only [homogCoord, Fin.insertNth_apply_succAbove, toFin]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin n) ↦ ℂ)
      ⟨m⟩).analyticAt z

lemma chartPreimage_eq (j : Fin (n + 1))
    (hW : ∀ y ∈ W, y ∈ Set.range (chartLRS.{u} j).base) :
    W = (PresheafedSpace.IsOpenImmersion.opensFunctor (chartLRS.{u} j).toHom).obj
      (chartPreimage.{u} j W) := by
  ext y
  refine ⟨fun hy ↦ ?_, fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz⟩
  obtain ⟨z, rfl⟩ := hW y hy
  exact ⟨z, hy, rfl⟩

/-- **Holomorphic degree-`0` functions on the cone over an open inside a chart are sections of
`𝒪_{ℙⁿ_an}`.** -/
lemma exists_secFun_eq (j : Fin (n + 1)) (hW : ∀ y ∈ W, y ∈ Set.range (chartLRS.{u} j).base)
    (F : (Fin (n + 1) → ℂ) → ℂ) (hF : DifferentiableOn ℂ F (vecCone.{u} W))
    (hhom : ∀ v ∈ vecCone.{u} W, ∀ c : ℂ, c ≠ 0 → F (c • v) = F v) :
    ∃ s : (projectiveSpaceAn.{u} n).presheaf.obj (op W), ∀ v ∈ vecCone.{u} W, secFun s v = F v := by
  have hmem (z : ULift.{u} (Fin n) → ℂ) (hz : z ∈ chartPreimage.{u} j W) :
      homogCoord.{u} j z ∈ vecCone.{u} W :=
    ⟨homogCoord_ne_zero j z, by rw [← chart_eq_pointOfVec]; exact hz⟩
  have han : ∀ z ∈ chartPreimage.{u} j W,
      AnalyticAt ℂ (fun z : ULift.{u} (Fin n) → ℂ ↦ F (homogCoord.{u} j z)) z := fun z hz ↦
    (analyticAt_of_differentiableOn isOpen_vecCone hF (hmem z hz)).comp (analyticAt_homogCoord j z)
  let g : OkaRing (chartPreimage.{u} j W) := OkaRing.mk _ (okaAnalytic_restrict han)
  haveI : IsIso ((chartLRS.{u} j).c.app (op W)) :=
    PresheafedSpace.IsOpenImmersion.c_iso' (f := (chartLRS.{u} j).toHom) _ (chartPreimage_eq j hW)
  refine ⟨inv ((chartLRS.{u} j).c.app (op W)) g, fun v hv ↦ ?_⟩
  have hj : v j ≠ 0 := (mem_range_chart_pointOfVec_iff v hv.1 j).1 (hW _ hv.2)
  rw [secFun_eq_chartSec _ j hj hv]
  have hc : chartSec j (inv ((chartLRS.{u} j).c.app (op W)) g) = g :=
    IsIso.inv_hom_id_apply ((chartLRS.{u} j).c.app (op W)) g
  rw [hc, OkaRing.toGlobalFun_apply _ ((mem_vecCone_iff_chart j hj).1 hv)]
  change F (homogCoord j (dehomOf.{u} j v)) = F v
  rw [homogCoord_dehomOf j v hj]
  exact hhom v hv _ (inv_ne_zero hj)

end ComplexAnalytic.projectiveSpaceAn

end
