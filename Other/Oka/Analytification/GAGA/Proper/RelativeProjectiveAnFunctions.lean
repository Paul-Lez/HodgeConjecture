/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.RelativeProjectiveAn
public import Other.Oka.Analytification.GAGA.ParametricIntervalIntegral
public import Other.Oka.Analytification.GAGA.TwistTransition

/-!
# Sections of `𝒪_{P^an}` as functions of homogeneous coordinates and base coordinates

Let `P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])`. For an open `W ⊆ P^an` let
`vecCone W = {(v, y) | v ≠ 0, [v; y] ∈ W} ⊆ ℂᴺ⁺¹ × ℂᵐ`, where `[v; y]` is
`ComplexAnalytic.relProjectiveSpaceAn.pointOfVec v y`. A section `s` of the structure sheaf over
`W` gives the function `secFun s : (v, y) ↦ s([v; y])` (zero off the cone), homogeneous of degree
`0` in `v` (`secFun_smul`) and holomorphic on the open cone (`isOpen_vecCone`,
`differentiableOn_secFun`): in the chart `i` it is the pulled back holomorphic function composed
with `(v, y) ↦ ((v_{i.succAbove k} / vᵢ)ₖ, y)` (`secFun_eq_chartSec`). A section is determined by
these values (`eq_of_secFun`), and every such function on the cone over an open contained in a
chart is of this form (`exists_secFun_eq`).

The values of pulled back algebraic sections are computed as in
`Other/Oka/Analytification/GAGA/TwistTransition.lean`, now over the evaluation `A → ℂ` at `y`: the value
of `π^♯ a`, `a ∈ Γ(D₊(Xᵢ), 𝒪)`, at `[v; y]` is `a(v)` with coefficients evaluated at `y`
(`eval_π_awayToSection`), and the pulled back transition functions `(Xⱼ / Xᵢ)ᵏ` of `𝒪(k)` have
value `(vⱼ / vᵢ)ᵏ` (`evπ_cocycle_zpow`).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic.relProjectiveSpaceAn

open AnalyticSpace ProjectiveSpace projectiveSpaceAn

variable {m N : ℕ}

/-- The value of a section of `𝒪_{P^an}` at a point of the chart `i` is the value of its
pullback, a holomorphic function on an open of `ℂ^{N+m}`. -/
lemma eval_chart {W : (relProjectiveSpaceAn.{u} m N).Opens} (i : Fin (N + 1))
    (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) (hw : (chartLRS i).base w ∈ W)
    (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W)) :
    (relProjectiveSpaceAn.{u} m N).eval _ hw s =
      OkaRing.evalHom (U := ((Opens.map (chartLRS i).base).obj W :
        TopologicalSpace.Opens (ULift.{u} (Fin (N + m)) → ℂ))) (x := w) hw
        ((chartLRS i).c.app (op W) s) :=
  (eval_c_app _ (relProjectiveSpaceAnChart.{u} i).isCLinear w hw s).symm.trans
    (eval_complexAffineSpace_of w hw _)

/-- The cone `{(v, y) | v ≠ 0, [v; y] ∈ W}` over an open `W ⊆ P^an`. -/
def vecCone (W : (relProjectiveSpaceAn.{u} m N).Opens) :
    Set ((Fin (N + 1) → ℂ) × (Fin m → ℂ)) :=
  {p | ∃ hv : p.1 ≠ 0, pointOfVec.{u} p.1 hv p.2 ∈ W}

variable {W W' : (relProjectiveSpaceAn.{u} m N).Opens}

lemma mem_vecCone_iff {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hv : p.1 ≠ 0) :
    p ∈ vecCone.{u} W ↔ pointOfVec.{u} p.1 hv p.2 ∈ W :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hv, h⟩⟩

lemma smul_mem_vecCone {v : Fin (N + 1) → ℂ} {y : Fin m → ℂ} (h : (v, y) ∈ vecCone.{u} W)
    {c : ℂ} (hc : c ≠ 0) : (c • v, y) ∈ vecCone.{u} W :=
  ⟨smul_ne_zero hc h.1, by rw [pointOfVec_smul _ _ _ hc]; exact h.2⟩

lemma vecCone_mono (h : W' ≤ W) : vecCone.{u} W' ⊆ vecCone.{u} W :=
  fun _ ⟨hv, hW⟩ ↦ ⟨hv, h hW⟩

lemma baseY_mem_of_mem_vecCone {U : Opens (Fin m → ℂ)} {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)}
    (h : p ∈ vecCone.{u} (tube.{u} (N := N) U)) : p.2 ∈ U := by
  have := h.2
  rwa [mem_tube, baseY_pointOfVec] at this

lemma eval_congr_point {y y' : relProjectiveSpaceAn.{u} m N} (h : y = y') (hy : y ∈ W)
    (hy' : y' ∈ W) (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W)) :
    (relProjectiveSpaceAn.{u} m N).eval y hy s = (relProjectiveSpaceAn.{u} m N).eval y' hy' s := by
  subst h
  rfl

open scoped Classical in
/-- A section of `𝒪_{P^an}` over `W`, as a function on `ℂᴺ⁺¹ × ℂᵐ` (homogeneous of degree `0`
in the first variable on the cone over `W`, zero off it). -/
noncomputable def secFun (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) : ℂ :=
  if h : p ∈ vecCone.{u} W then
    (relProjectiveSpaceAn.{u} m N).eval (pointOfVec.{u} p.1 h.1 p.2) h.2 s
  else 0

lemma secFun_of_mem (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hv : p.1 ≠ 0) (hW : pointOfVec.{u} p.1 hv p.2 ∈ W) :
    secFun s p = (relProjectiveSpaceAn.{u} m N).eval (pointOfVec.{u} p.1 hv p.2) hW s := by
  classical
  rw [secFun, dif_pos ⟨hv, hW⟩]

lemma secFun_of_notMem (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (h : p ∉ vecCone.{u} W) : secFun s p = 0 := by
  classical
  rw [secFun, dif_neg h]

lemma secFun_smul (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (v : Fin (N + 1) → ℂ) (y : Fin m → ℂ) {c : ℂ} (hc : c ≠ 0) :
    secFun s (c • v, y) = secFun s (v, y) := by
  by_cases h : (v, y) ∈ vecCone.{u} W
  · rw [secFun_of_mem s h.1 h.2, secFun_of_mem s (p := (c • v, y)) (smul_ne_zero hc h.1)
      (by rw [pointOfVec_smul _ _ _ hc]; exact h.2)]
    exact eval_congr_point (pointOfVec_smul v h.1 y hc) _ _ s
  · rw [secFun_of_notMem s h, secFun_of_notMem s fun h' ↦ h (by
      simpa [smul_smul, inv_mul_cancel₀ hc] using smul_mem_vecCone h' (inv_ne_zero hc))]

lemma secFun_add (s t : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) :
    secFun (s + t) p = secFun s p + secFun t p := by
  by_cases h : p ∈ vecCone.{u} W
  · rw [secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, map_add]
  · rw [secFun_of_notMem _ h, secFun_of_notMem _ h, secFun_of_notMem _ h, add_zero]

lemma secFun_mul (s t : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) :
    secFun (s * t) p = secFun s p * secFun t p := by
  by_cases h : p ∈ vecCone.{u} W
  · rw [secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, secFun_of_mem _ h.1 h.2, map_mul]
  · rw [secFun_of_notMem _ h, secFun_of_notMem _ h, secFun_of_notMem _ h, mul_zero]

lemma secFun_zero (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) :
    secFun (0 : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W)) p = 0 := by
  by_cases h : p ∈ vecCone.{u} W
  · rw [secFun_of_mem _ h.1 h.2, map_zero]
  · rw [secFun_of_notMem _ h]

lemma secFun_restrictOpen (h : W' ≤ W) (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) :
    secFun (TopCat.Presheaf.restrictOpen s W' h) p = (vecCone.{u} W').indicator (secFun s) p := by
  by_cases hp : p ∈ vecCone.{u} W'
  · rw [Set.indicator_of_mem hp, secFun_of_mem _ hp.1 hp.2, secFun_of_mem _ hp.1 (h hp.2),
      AnalyticSpace.eval_restrictOpen]
  · rw [Set.indicator_of_notMem hp, secFun_of_notMem _ hp]

/-- The chart coordinates `((v_{i.succAbove k} / vᵢ)ₖ, y)` of `(v, y)`, as a point of
`ℂ^{N+m}`. -/
noncomputable def dehomOf (i : Fin (N + 1)) (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) :
    AnalyticSpace.complexAffineSpace.{u} (N + m) :=
  joinPt (dehomogenizeVec i p.1) p.2

lemma pointOfVec_eq_chart {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hv : p.1 ≠ 0) (i : Fin (N + 1))
    (hi : p.1 i ≠ 0) : pointOfVec.{u} p.1 hv p.2 = (chartLRS i).base (dehomOf.{u} i p) :=
  pointOfVec_eq _ hv _ i hi

/-- `dehomOf` as a map to `ULift (Fin (N + m)) → ℂ`. -/
noncomputable def dehomVec (i : Fin (N + 1)) (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) :
    ULift.{u} (Fin (N + m)) → ℂ :=
  fun k ↦ Fin.append (fun l ↦ p.1 (i.succAbove l) / p.1 i) p.2 k.down

lemma dehomOf_eq_dehomVec (i : Fin (N + 1)) (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) :
    (dehomOf.{u} i p : ULift.{u} (Fin (N + m)) → ℂ) = dehomVec.{u} i p :=
  rfl

lemma continuousOn_dehomVec (i : Fin (N + 1)) :
    ContinuousOn (dehomVec.{u} (m := m) i) {p | p.1 i ≠ 0} := by
  refine continuousOn_pi.2 fun ⟨k⟩ ↦ ?_
  induction k using Fin.addCases with
  | left l =>
    simp only [dehomVec, Fin.append_left]
    exact (((continuous_apply _).comp continuous_fst).continuousOn).div
      ((continuous_apply i).comp continuous_fst).continuousOn fun p hp ↦ hp
  | right j =>
    simp only [dehomVec, Fin.append_right]
    exact ((continuous_apply j).comp continuous_snd).continuousOn

lemma differentiableAt_dehomVec (i : Fin (N + 1)) {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)}
    (hi : p.1 i ≠ 0) : DifferentiableAt ℂ (dehomVec.{u} i) p := by
  refine differentiableAt_pi.2 fun ⟨k⟩ ↦ ?_
  induction k using Fin.addCases with
  | left l =>
    simp only [dehomVec, Fin.append_left]
    have h1 : DifferentiableAt ℂ
        (fun q : (Fin (N + 1) → ℂ) × (Fin m → ℂ) ↦ q.1 (i.succAbove l)) p := by fun_prop
    have h2 : DifferentiableAt ℂ (fun q : (Fin (N + 1) → ℂ) × (Fin m → ℂ) ↦ q.1 i) p := by
      fun_prop
    simp_rw [div_eq_mul_inv]
    exact h1.mul (h2.inv hi)
  | right j =>
    simp only [dehomVec, Fin.append_right]
    fun_prop

/-- The preimage of `W` in the chart `i`, as an open of `ℂ^{N+m}`. -/
noncomputable abbrev chartPreimage (i : Fin (N + 1)) (W : (relProjectiveSpaceAn.{u} m N).Opens) :
    TopologicalSpace.Opens (ULift.{u} (Fin (N + m)) → ℂ) :=
  (Opens.map (chartLRS.{u} i).base).obj W

/-- The pullback of a section along the chart `i`, a holomorphic function. -/
noncomputable abbrev chartSec (i : Fin (N + 1))
    (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W)) : OkaRing (chartPreimage.{u} i W) :=
  (chartLRS.{u} i).c.app (op W) s

/-- **In the chart `i`, `secFun s` is the pulled back holomorphic function of the chart
coordinates.** -/
lemma secFun_eq_chartSec (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (i : Fin (N + 1)) (hi : p.1 i ≠ 0)
    (hp : p ∈ vecCone.{u} W) :
    secFun s p = (chartSec i s).toGlobalFun _ (dehomVec.{u} i p) := by
  have hz : (chartLRS i).base (dehomOf.{u} i p) ∈ W := by
    rw [← pointOfVec_eq_chart hp.1 i hi]; exact hp.2
  rw [secFun_of_mem s hp.1 hp.2, eval_congr_point (pointOfVec_eq_chart hp.1 i hi) _ hz,
    eval_chart i _ hz, OkaRing.toGlobalFun_apply _ hz]
  rfl

lemma mem_vecCone_iff_chart {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (i : Fin (N + 1))
    (hi : p.1 i ≠ 0) : p ∈ vecCone.{u} W ↔ dehomVec.{u} i p ∈ chartPreimage.{u} i W := by
  have hv : p.1 ≠ 0 := fun h ↦ hi (by simp [h])
  rw [mem_vecCone_iff hv, pointOfVec_eq_chart hv i hi]
  rfl

lemma isOpen_vecCone : IsOpen (vecCone.{u} W) := by
  have : vecCone.{u} W = ⋃ i, {p | p.1 i ≠ 0} ∩ dehomVec.{u} i ⁻¹' (chartPreimage.{u} i W) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      SetLike.mem_coe]
    refine ⟨fun hp ↦ ?_, fun ⟨i, hi, h⟩ ↦ (mem_vecCone_iff_chart i hi).2 h⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hp.1
    exact ⟨i, hi, (mem_vecCone_iff_chart i hi).1 hp⟩
  rw [this]
  exact isOpen_iUnion fun i ↦ (continuousOn_dehomVec i).isOpen_inter_preimage
    (isOpen_ne_fun ((continuous_apply i).comp continuous_fst) continuous_const)
    (chartPreimage i W).isOpen

/-- **Sections of `𝒪_{P^an}` are holomorphic on the cone.** -/
lemma differentiableOn_secFun (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W)) :
    DifferentiableOn ℂ (secFun s) (vecCone.{u} W) := by
  intro p hp
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hp.1
  refine DifferentiableAt.differentiableWithinAt ?_
  have hN : {q : (Fin (N + 1) → ℂ) × (Fin m → ℂ) | q.1 i ≠ 0} ∩ vecCone.{u} W ∈ 𝓝 p :=
    ((isOpen_ne_fun ((continuous_apply i).comp continuous_fst) continuous_const).inter
      isOpen_vecCone).mem_nhds ⟨hi, hp⟩
  have heq : (chartSec i s).toGlobalFun _ ∘ dehomVec.{u} i =ᶠ[𝓝 p] secFun s := by
    filter_upwards [hN] with q hq
    exact (secFun_eq_chartSec s i hq.1 hq.2).symm
  refine (DifferentiableAt.comp p ?_ (differentiableAt_dehomVec i hi)).congr_of_eventuallyEq
    heq.symm
  have hz := (mem_vecCone_iff_chart i hi).1 hp
  exact ((chartSec i s).differentiableOn_toGlobalFun _ hz).differentiableAt
    ((chartPreimage i W).isOpen.mem_nhds hz)

/-- The homogeneous and base coordinates `(homogCoord i w, yPart w)` of a point `w` of the chart
`i`. -/
def chartVec (i : Fin (N + 1)) (w : AnalyticSpace.complexAffineSpace.{u} (N + m)) :
    (Fin (N + 1) → ℂ) × (Fin m → ℂ) :=
  (homogCoord i w, yPart w)

lemma chartVec_mem_vecCone {i : Fin (N + 1)} {w : AnalyticSpace.complexAffineSpace.{u} (N + m)}
    (hw : (chartLRS i).base w ∈ W) : chartVec.{u} i w ∈ vecCone.{u} W :=
  ⟨homogCoord_ne_zero i w, by
    change pointOfVec.{u} (homogCoord i w) (homogCoord_ne_zero i w) (yPart w) ∈ W
    rw [← chart_eq_pointOfVec]; exact hw⟩

lemma chartSec_toGlobalFun_eq (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (i : Fin (N + 1)) {w : AnalyticSpace.complexAffineSpace.{u} (N + m)}
    (hw : (chartLRS i).base w ∈ W) :
    (chartSec i s).toGlobalFun _ w = secFun s (chartVec.{u} i w) := by
  have hv := homogCoord_ne_zero i w
  have hW : pointOfVec.{u} (homogCoord i w) hv (yPart w) ∈ W := by
    rw [← chart_eq_pointOfVec]; exact hw
  rw [secFun_of_mem s (p := chartVec i w) hv hW]
  change _ = (relProjectiveSpaceAn.{u} m N).eval (pointOfVec.{u} (homogCoord i w) hv (yPart w)) hW s
  rw [← eval_congr_point (chart_eq_pointOfVec i w) hw hW, eval_chart i w hw,
    OkaRing.toGlobalFun_apply _ hw]
  rfl

/-- **A section of `𝒪_{P^an}` is determined by its values.** -/
lemma eq_zero_of_secFun (s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (h : ∀ p ∈ vecCone.{u} W, secFun s p = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext (relProjectiveSpaceAn.{u} m N).sheaf W s 0 fun x hx ↦ ?_
  obtain ⟨i, w, rfl⟩ := exists_mem_range_chart x
  have h0 : chartSec i s = 0 := by
    refine OkaRing.ext (funext fun w' ↦ ?_)
    rw [← OkaRing.toGlobalFun_apply _ w'.2, chartSec_toGlobalFun_eq s i w'.2]
    exact h _ (chartVec_mem_vecCone w'.2)
  apply (ConcreteCategory.bijective_of_isIso ((chartLRS i).stalkMap w)).1
  change (chartLRS i).stalkMap w ((relProjectiveSpaceAn.{u} m N).presheaf.germ W _ hx s) =
    (chartLRS i).stalkMap w ((relProjectiveSpaceAn.{u} m N).presheaf.germ W _ hx 0)
  rw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply, map_zero]
  exact congrArg _ h0

lemma eq_of_secFun {s t : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W)}
    (h : ∀ p ∈ vecCone.{u} W, secFun s p = secFun t p) : s = t := by
  rw [← sub_eq_zero]
  refine eq_zero_of_secFun _ fun p hp ↦ ?_
  rw [sub_eq_add_neg, secFun_add, h p hp, ← secFun_add, ← sub_eq_add_neg, sub_self, secFun_zero]

lemma analyticAt_chartVec (j : Fin (N + 1)) (w : ULift.{u} (Fin (N + m)) → ℂ) :
    AnalyticAt ℂ (fun w : ULift.{u} (Fin (N + m)) → ℂ ↦ chartVec.{u} j w) w := by
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun k ↦ ?_) (analyticAt_pi_iff.2 fun l ↦ ?_)
  · obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
    · simp only [homogCoord, Fin.insertNth_apply_same]
      exact analyticAt_const
    · simp only [homogCoord, Fin.insertNth_apply_succAbove, zPart]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin (N + m)) ↦ ℂ)
        ⟨Fin.castAdd m l⟩).analyticAt w
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin (N + m)) ↦ ℂ)
      ⟨Fin.natAdd N l⟩).analyticAt w

lemma chartPreimage_eq (j : Fin (N + 1)) (hW : ∀ y ∈ W, y ∈ Set.range (chartLRS.{u} j).base) :
    W = (PresheafedSpace.IsOpenImmersion.opensFunctor (chartLRS.{u} j).toHom).obj
      (chartPreimage.{u} j W) := by
  ext y
  refine ⟨fun hy ↦ ?_, fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz⟩
  obtain ⟨z, rfl⟩ := hW y hy
  exact ⟨z, hy, rfl⟩

lemma chartVec_dehomOf (j : Fin (N + 1)) (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ))
    (hj : p.1 j ≠ 0) : chartVec.{u} j (dehomOf.{u} j p) = ((p.1 j)⁻¹ • p.1, p.2) := by
  simp only [chartVec, homogCoord, dehomOf, zPart_joinPt, yPart_joinPt]
  rw [insertNth_dehomogenizeVec j p.1 hj]

/-- **Holomorphic functions on the cone over an open inside a chart, homogeneous of degree `0`
in `v`, are sections of `𝒪_{P^an}`.** -/
lemma exists_secFun_eq (j : Fin (N + 1)) (hW : ∀ y ∈ W, y ∈ Set.range (chartLRS.{u} j).base)
    (F : (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ) (hF : DifferentiableOn ℂ F (vecCone.{u} W))
    (hhom : ∀ p ∈ vecCone.{u} W, ∀ c : ℂ, c ≠ 0 → F (c • p.1, p.2) = F p) :
    ∃ s : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W),
      ∀ p ∈ vecCone.{u} W, secFun s p = F p := by
  have hmem (w : ULift.{u} (Fin (N + m)) → ℂ) (hw : w ∈ chartPreimage.{u} j W) :
      chartVec.{u} j w ∈ vecCone.{u} W :=
    chartVec_mem_vecCone (w := w) hw
  have han : ∀ w ∈ chartPreimage.{u} j W,
      AnalyticAt ℂ (fun w : ULift.{u} (Fin (N + m)) → ℂ ↦ F (chartVec.{u} j w)) w :=
    fun w hw ↦ AnalyticAt.comp (g := F)
      (f := fun w : ULift.{u} (Fin (N + m)) → ℂ ↦ chartVec.{u} j w)
      (analyticAt_of_differentiableOn_of_finiteDimensional isOpen_vecCone hF (hmem w hw))
      (analyticAt_chartVec j w)
  let g : OkaRing (chartPreimage.{u} j W) := OkaRing.mk _ (okaAnalytic_restrict han)
  haveI : IsIso ((chartLRS.{u} j).c.app (op W)) :=
    PresheafedSpace.IsOpenImmersion.c_iso' (f := (chartLRS.{u} j).toHom) _ (chartPreimage_eq j hW)
  refine ⟨inv ((chartLRS.{u} j).c.app (op W)) g, fun p hp ↦ ?_⟩
  have hj : p.1 j ≠ 0 := (mem_range_chart_pointOfVec_iff p.1 hp.1 p.2 j).1 (hW _ hp.2)
  rw [secFun_eq_chartSec _ j hj hp]
  have hc : chartSec j (inv ((chartLRS.{u} j).c.app (op W)) g) = g :=
    IsIso.inv_hom_id_apply ((chartLRS.{u} j).c.app (op W)) g
  rw [hc, OkaRing.toGlobalFun_apply _ ((mem_vecCone_iff_chart j hj).1 hp)]
  change F (chartVec j (dehomOf.{u} j p)) = F p
  rw [chartVec_dehomOf j p hj]
  exact hhom p hp _ (inv_ne_zero hj)

/-! ### Values of pulled back sections of `𝒪_P` -/

section Transition

open HomogeneousLocalization MvPolynomial AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
set_option quotPrecheck false in
local notation "𝒜" => homogeneousSubmodule (Fin (N + 1)) (RelBase.{u} m)

lemma eval₂_evalBase_X (v : Fin (N + 1) → ℂ) (y : Fin m → ℂ) (i : Fin (N + 1)) :
    eval₂ (evalBase.{u} y) v (X i) = v i :=
  eval₂_X _ _ _

/-- The comparison morphism at the point `[v; y]` of the chart `i`. -/
lemma π_pointOfVec (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) (i : Fin (N + 1))
    (hi : v i ≠ 0) :
    π m N (pointOfVec.{u} v hv y) =
      (Proj.awayι 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos).base
        (awayPoint (φ := evalBase.{u} y) v (X i) (by rwa [eval₂_evalBase_X])) := by
  rw [pointOfVec_eq _ _ _ i hi, π_chart, zPart_joinPt, yPart_joinPt, chart_base_evalPoint]

lemma π_pointOfVec_mem_U (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) (i : Fin (N + 1))
    (hi : v i ≠ 0) : π m N (pointOfVec.{u} v hv y) ∈ U N (RelBase.{u} m) i := by
  rw [← SetLike.mem_coe, ← Set.mem_preimage, ← range_chart, mem_range_chart_pointOfVec_iff]
  exact hi

/-- The constants of `P` are the constants of `A = ℂ[y₀, …, y_{m-1}]`. -/
lemma schemeConst_relProjectiveSpace (c : ULift.{u} ℂ) :
    schemeConst (relProjectiveSpace.{u} m N) c =
      (ProjectiveSpace.toSpec N (RelBase.{u} m)).appTop
        ((Scheme.ΓSpecIso (.of (RelBase.{u} m))).inv (C c)) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (C : ULift.{u} ℂ →+* RelBase.{u} m))).hom c)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  change (ProjectiveSpace.toSpec N (RelBase.{u} m) ≫
    Spec.map (CommRingCat.ofHom (C : ULift.{u} ℂ →+* RelBase.{u} m))).appTop
      ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv c) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact congrArg (fun x ↦ (ProjectiveSpace.toSpec N (RelBase.{u} m)).appTop x) h.symm

/-- **Values of the pulled-back sections `AlgebraicGeometry.Proj.awayToSection a` of `𝒪_P` over
`D₊(Xᵢ)`**: the value of `π^♯ a` at `[v; y]` is `a(v)`, evaluated over `A → ℂ` at `y`. -/
theorem eval_π_awayToSection (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ)
    (i : Fin (N + 1)) (hi : v i ≠ 0) (a : Away 𝒜 (X i)) :
    (relProjectiveSpaceAn.{u} m N).eval (pointOfVec.{u} v hv y)
      (π_pointOfVec_mem_U v hv y i hi)
      ((analytificationπLRS (relProjectiveSpace.{u} m N)).c.app (op (U N _ i))
        (Proj.awayToSection 𝒜 (X i) a)) =
      awayEval (φ := evalBase.{u} y) v (X i) (by rwa [eval₂_evalBase_X]) a := by
  refine eval_analytificationπ_eq (X := relProjectiveSpace.{u} m N) (V := U N _ i) _ _
    (π_pointOfVec_mem_U v hv y i hi) _ ?_
  have hi' : eval₂ (evalBase.{u} y) v (X i) ≠ 0 := by rwa [eval₂_evalBase_X]
  set c := awayEval (φ := evalBase.{u} y) v (X i) hi' a
  have hconst : TopCat.Presheaf.restrictOpen
      (schemeConst (relProjectiveSpace.{u} m N) (ULift.up c)) (U N _ i) le_top =
      Proj.awayToSection 𝒜 (X i) (awayXBase _ i (C (ULift.up c))) := by
    rw [schemeConst_relProjectiveSpace]
    exact restrict_toSpec_appTop (X_mem_homogeneousSubmodule_one i) Nat.one_pos _
  intro hu
  have hmem : π m N (pointOfVec.{u} v hv y) ∈ ℙₒ(N; RelBase.{u} m).basicOpen
      (Proj.awayToSection 𝒜 (X i) (a - awayXBase _ i (C (ULift.up c)))) := by
    have := (Scheme.mem_basicOpen ℙₒ(N; RelBase.{u} m) _ _ _).2 hu
    rw [hconst] at this
    rw [map_sub]
    exact this
  rw [π_pointOfVec v hv y i hi, awayι_awayPoint_mem_basicOpen_iff, map_sub,
    awayEval_awayXBase] at hmem
  exact hmem (by rw [eval₂Hom_C, sub_eq_zero]; rfl)

/-- Evaluation at `[v; y]` of the pullback to `P^an` of a section of `𝒪_P`. -/
noncomputable def evπ {W : ℙₒ(N; RelBase.{u} m).Opens} (v : Fin (N + 1) → ℂ) (hv : v ≠ 0)
    (y : Fin m → ℂ) (hW : π m N (pointOfVec.{u} v hv y) ∈ W) :
    ℙₒ(N; RelBase.{u} m).presheaf.obj (op W) →+* ℂ :=
  ((relProjectiveSpaceAn.{u} m N).eval
    (U := (Opens.map (analytificationπLRS (relProjectiveSpace.{u} m N)).base).obj W)
      (pointOfVec.{u} v hv y) hW).comp
    ((analytificationπLRS (relProjectiveSpace.{u} m N)).c.app (op W)).hom

lemma evπ_restrictOpen {W W' : ℙₒ(N; RelBase.{u} m).Opens} (h : W' ≤ W) (v : Fin (N + 1) → ℂ)
    (hv : v ≠ 0) (y : Fin m → ℂ) (hW' : π m N (pointOfVec.{u} v hv y) ∈ W')
    (x : ℙₒ(N; RelBase.{u} m).presheaf.obj (op W)) :
    evπ.{u} v hv y hW' (TopCat.Presheaf.restrictOpen x W' h) = evπ v hv y (h hW') x := by
  have key : (analytificationπLRS (relProjectiveSpace.{u} m N)).c.app (op W')
      (TopCat.Presheaf.restrictOpen x W' h) =
      TopCat.Presheaf.restrictOpen (F := (relProjectiveSpaceAn.{u} m N).presheaf)
        ((analytificationπLRS (relProjectiveSpace.{u} m N)).c.app (op W) x)
        ((Opens.map (analytificationπLRS (relProjectiveSpace.{u} m N)).base).obj W')
        ((Opens.map (analytificationπLRS (relProjectiveSpace.{u} m N)).base).monotone h) :=
    congr($((analytificationπLRS (relProjectiveSpace.{u} m N)).c.naturality
      (homOfLE h).op).hom x)
  simp only [evπ, RingHom.coe_comp, Function.comp_apply]
  exact (congrArg _ key).trans (AnalyticSpace.eval_restrictOpen _ _ _ _ _)

lemma evπ_xDiv (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) (i j : Fin (N + 1))
    (hi : v i ≠ 0) :
    evπ.{u} v hv y (π_pointOfVec_mem_U v hv y i hi) (xDiv i j) = v j / v i := by
  refine (eval_π_awayToSection v hv y i hi (awayXDiv _ i j)).trans ?_
  exact awayEval_awayXDiv (φ := evalBase.{u} y) v i j _

/-- **The transition functions of `𝒪(k)^an`**: the value at `[v; y]` of the pullback of the
cocycle `(Xⱼ / Xᵢ)ᵏ` is `(vⱼ / vᵢ)ᵏ`. -/
lemma evπ_cocycle_zpow (k : ℤ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ)
    (i j : Fin (N + 1)) (hi : v i ≠ 0)
    (hW : π m N (pointOfVec.{u} v hv y) ∈ U N (RelBase.{u} m) i ⊓ U N _ j) :
    evπ.{u} v hv y hW ((cocycle N (RelBase.{u} m) ^ k).g i j) = (v j / v i) ^ k := by
  have hg := cocycle_zpow_g_res (R := RelBase.{u} m) k i j (U N _ i ⊓ U N _ j) le_rfl
  rw [ores_self] at hg
  rw [hg]
  set w := xDivUnit (R := RelBase.{u} m) i j (U N _ i ⊓ U N _ j) le_rfl
  refine (Units.coe_map (evπ v hv y hW).toMonoidHom (w ^ k)).symm.trans ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
  congr 1
  change evπ v hv y hW (xDiv i j |ₒ (U N _ i ⊓ U N _ j)) = _
  rw [evπ_restrictOpen]
  exact evπ_xDiv v hv y i j hi

end Transition

end ComplexAnalytic.relProjectiveSpaceAn

end
