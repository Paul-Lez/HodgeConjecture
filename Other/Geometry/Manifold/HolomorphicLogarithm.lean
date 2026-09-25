/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Local holomorphic logarithms

A holomorphic function that is nonzero at a point has a holomorphic logarithm near that point.
The construction normalizes the function to take the value one at the chosen point, so that
the principal logarithm is analytic on a neighborhood. This is the local surjectivity input
for the holomorphic exponential sequence in the proof of the Lefschetz `(1, 1)` theorem.
-/

public section

open scoped Manifold ContDiff Topology
open Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A holomorphic function nonzero at a point admits a holomorphic logarithm near that point. -/
theorem ContMDiffAt.exists_local_log {f : M → ℂ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℂ) ω f x) (hx : f x ≠ 0) :
    ∃ g : M → ℂ, ContMDiffAt I 𝓘(ℂ) ω g x ∧
      ∀ᶠ y in 𝓝 x, Complex.exp (g y) = f y := by
  refine ⟨fun y ↦ Complex.log (f y / f x) + Complex.log (f x), ?_, ?_⟩
  · have hmem : f x / f x ∈ Complex.slitPlane := by simp [hx]
    exact ((analyticAt_clog hmem).contDiffAt.comp_contMDiffAt
      (f := fun y : M ↦ f y / f x) (x := x)
      (hf.div_const (f x))).add contMDiffAt_const
  · filter_upwards [hf.continuousAt.eventually (eventually_ne_nhds hx)] with y hy
    rw [Complex.exp_add, Complex.exp_log (div_ne_zero hy hx), Complex.exp_log hx,
      div_mul_cancel₀ _ hx]

/-- The local logarithm can be bundled as a holomorphic section on an open neighborhood. -/
theorem ContMDiffAt.exists_holomorphic_log [IsManifold I ω M] {f : M → ℂ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℂ) ω f x) (hx : f x ≠ 0) :
    ∃ U : Opens M, x ∈ U ∧ ∃ g : C^ω⟮I, U; ℂ⟯,
      ∀ y : U, Complex.exp (g y) = f y := by
  obtain ⟨g, hg, hgf⟩ := hf.exists_local_log hx
  obtain ⟨V, hV, hgV⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hg
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hV hgf)
  let W : Opens M := ⟨U, hUo⟩
  refine ⟨W, hxU, ⟨fun y ↦ g y, ?_⟩, fun y ↦ (hU y.2).2⟩
  intro y
  apply contMDiffAt_subtype_iff.mpr
  exact (hgV y (hU y.2).1).contMDiffAt
    (Filter.mem_of_superset (hUo.mem_nhds y.2) fun z hz ↦ (hU hz).1)

/-- A continuous function in the kernel of the complex exponential is locally an integer
multiple of its period. This identifies the kernel sheaf of the exponential map. -/
theorem ContinuousAt.exists_local_exp_period {f : M → ℂ} {x : M}
    (hf : ContinuousAt f x) (he : ∀ᶠ y in 𝓝 x, Complex.exp (f y) = 1) :
    ∃ n : ℤ, ∀ᶠ y in 𝓝 x, f y = n * (2 * Real.pi * Complex.I) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he.self_of_nhds
  refine ⟨n, ?_⟩
  have hc : ContinuousAt (fun y ↦ (f y - f x).im) x :=
    Complex.continuous_im.continuousAt.comp (hf.sub continuousAt_const)
  have hnear : ∀ᶠ y in 𝓝 x, (f y - f x).im ∈ Set.Ioo (-Real.pi) Real.pi :=
    hc.eventually (isOpen_Ioo.mem_nhds (by simp [Real.pi_pos]))
  filter_upwards [he, hnear] with y hy him
  have hexp : Complex.exp (f y - f x) = Complex.exp 0 := by
    rw [Complex.exp_sub, hy, he.self_of_nhds, Complex.exp_zero, div_self one_ne_zero]
  have hzero := Complex.exp_inj_of_neg_pi_lt_of_le_pi him.1 him.2.le
    (by simpa using neg_lt_zero.mpr Real.pi_pos) (by simpa using Real.pi_pos.le) hexp
  exact (sub_eq_zero.mp hzero).trans hn

/-- With the normalization `z ↦ exp(2πiz)`, a continuous kernel section is locally an integer. -/
theorem ContinuousAt.exists_local_int_of_exp_two_pi_I_eq_one {f : M → ℂ} {x : M}
    (hf : ContinuousAt f x)
    (he : ∀ᶠ y in 𝓝 x, Complex.exp (2 * Real.pi * Complex.I * f y) = 1) :
    ∃ n : ℤ, ∀ᶠ y in 𝓝 x, f y = n := by
  obtain ⟨n, hn⟩ := (continuousAt_const.mul hf).exists_local_exp_period he
  refine ⟨n, hn.mono fun y hy ↦ ?_⟩
  exact mul_left_cancel₀ Complex.two_pi_I_ne_zero (hy.trans (mul_comm _ _))

namespace ContMDiffMap

/-- A holomorphic section in the normalized exponential kernel becomes a constant integer
after restriction to a small open neighborhood in the ambient manifold. -/
theorem exists_local_eq_int {U : Opens M} (f : C^ω⟮I, U; ℂ⟯) (x : U)
    (he : ∀ y : U, Complex.exp (2 * Real.pi * Complex.I * f y) = 1) :
    ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧ ∃ n : ℤ,
      ∀ y : V, f ⟨y, hVU y.2⟩ = n := by
  classical
  let fext : M → ℂ := fun y ↦ if hy : y ∈ U then f ⟨y, hy⟩ else 0
  have hres : (fun y : U ↦ fext y) = f := by
    funext y
    simp [fext, y.2]
  have hfext : ContMDiffAt I 𝓘(ℂ) ω fext (x : M) := by
    apply (contMDiffAt_subtype_iff (x := x)).mp
    rw [hres]
    exact f.contMDiff x
  have hU : (U : Set M) ∈ 𝓝 (x : M) := U.isOpen.mem_nhds x.2
  have hext : ∀ᶠ y in 𝓝 (x : M),
      Complex.exp (2 * Real.pi * Complex.I * fext y) = 1 := by
    filter_upwards [hU] with y hy
    dsimp only [fext]
    rw [dif_pos (show y ∈ U from hy)]
    exact he ⟨y, hy⟩
  obtain ⟨n, hn⟩ := hfext.continuousAt.exists_local_int_of_exp_two_pi_I_eq_one hext
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem hU hn)
  refine ⟨⟨V, hVo⟩, fun y hy ↦ (hV hy).1, hxV, n, fun y ↦ ?_⟩
  have hy : (y : M) ∈ U := (hV y.2).1
  have h := (hV y.2).2
  change fext (y : M) = n at h
  dsimp only [fext] at h
  rw [dif_pos hy] at h
  exact h

/-- A nonvanishing holomorphic section has a normalized logarithm after restriction to a
smaller open neighborhood in the ambient manifold. -/
theorem exists_local_holomorphicExponential [IsManifold I ω M] {U : Opens M}
    (f : C^ω⟮I, U; ℂ⟯) (x : U) (hx : f x ≠ 0) :
    ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧ ∃ g : C^ω⟮I, V; ℂ⟯,
      ∀ y : V, Complex.exp (2 * Real.pi * Complex.I * g y) = f ⟨y, hVU y.2⟩ := by
  classical
  let fext : M → ℂ := fun y ↦ if hy : y ∈ U then f ⟨y, hy⟩ else 0
  have hres : (fun y : U ↦ fext y) = f := by
    funext y
    simp [fext, y.2]
  have hfext : ContMDiffAt I 𝓘(ℂ) ω fext (x : M) := by
    apply (contMDiffAt_subtype_iff (x := x)).mp
    rw [hres]
    exact f.contMDiff x
  have hxext : fext x ≠ 0 := by simpa [fext, x.2] using hx
  obtain ⟨W, hxW, g, hg⟩ := hfext.exists_holomorphic_log hxext
  let V := W ⊓ U
  let gV : C^ω⟮I, V; ℂ⟯ := restrictRingHom I 𝓘(ℂ) ℂ inf_le_left g
  let h : C^ω⟮I, V; ℂ⟯ :=
    ⟨fun y ↦ gV y / (2 * Real.pi * Complex.I),
      gV.contMDiff.div_const _⟩
  refine ⟨V, inf_le_right, ⟨hxW, x.2⟩, h, fun y ↦ ?_⟩
  change Complex.exp (2 * Real.pi * Complex.I *
    (g ⟨y, y.2.1⟩ / (2 * Real.pi * Complex.I))) = _
  rw [mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, hg]
  exact dif_pos (show (y : M) ∈ U from y.2.2)

/-- The normalized exponential of holomorphic functions, regarded as a multiplicative map. -/
@[expose]
noncomputable def holomorphicExpMonoidHom :
    Multiplicative C^ω⟮I, M; ℂ⟯ →* C^ω⟮I, M; ℂ⟯ where
  toFun f := ⟨fun x ↦ Complex.exp (2 * Real.pi * Complex.I * f.toAdd x),
    Complex.contDiff_exp.comp_contMDiff (contMDiff_const.mul f.toAdd.contMDiff)⟩
  map_one' := by
    ext x
    change Complex.exp (2 * Real.pi * Complex.I * 0) = 1
    simp
  map_mul' f g := by
    ext x
    change Complex.exp (2 * Real.pi * Complex.I * (f.toAdd x + g.toAdd x)) =
      Complex.exp (2 * Real.pi * Complex.I * f.toAdd x) *
        Complex.exp (2 * Real.pi * Complex.I * g.toAdd x)
    rw [mul_add, Complex.exp_add]

/-- The holomorphic exponential takes values in units and is additive after writing the
unit group additively. Its inverse unit is supplied by exponentiating the negative section. -/
@[expose]
noncomputable def holomorphicExponential :
    C^ω⟮I, M; ℂ⟯ →+ Additive (C^ω⟮I, M; ℂ⟯)ˣ :=
  (MonoidHom.toHomUnits (holomorphicExpMonoidHom (I := I) (M := M))).toAdditive

/-- Pointwise evaluation of the normalized holomorphic exponential. -/
@[simp]
theorem holomorphicExponential_apply (f : C^ω⟮I, M; ℂ⟯) (x : M) :
    ((holomorphicExponential f).toMul : C^ω⟮I, M; ℂ⟯) x =
      Complex.exp (2 * Real.pi * Complex.I * f x) := rfl

end ContMDiffMap
