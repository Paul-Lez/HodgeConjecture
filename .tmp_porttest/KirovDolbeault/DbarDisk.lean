/-
  DbarDisk.lean

  ∂̄-on-a-disk solvability (the Cauchy transform) — a standalone, Mathlib-only
  probe toward the Dolbeault wall.

  We define the Wirtinger ∂̄ operator on `ℂ → ℂ` and aim to prove the
  inhomogeneous Cauchy–Riemann solvability statement:

    for `g` continuous on the closed disk of radius `r`, there is an ℝ-differentiable
    `f` on the open disk with `∂̄ f = g` there.

  The classical witness is the **Cauchy transform**
    f(z) = -(1/π) ∬_{|ζ|≤r} g(ζ)/(ζ - z) dA(ζ),
  whose ∂̄ recovers `g` (Cauchy–Pompeiu).  This file isolates exactly the
  Mathlib gap on that route; see `dbar_disk_solvable` below.
-/
import Mathlib

open scoped Real Topology ENNReal
open Complex MeasureTheory

namespace DbarDisk

/-- The Wirtinger anti-holomorphic derivative `∂̄f = ½(∂ₓf + i ∂_y f)`, written via
the real Fréchet derivative `fderiv ℝ f` evaluated at the basis directions `1` and `I`.
`f` is holomorphic at `z` iff `dbar f z = 0` (see `dbar_eq_zero_of_differentiableAt`). -/
noncomputable def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

@[simp] theorem dbar_const (c : ℂ) (z : ℂ) : dbar (fun _ => c) z = 0 := by
  simp [dbar]

/-! ## D0 — the Cauchy kernel is locally integrable

The kernel `K ζ = -(1/(π·ζ))` has `‖K ζ‖ = (1/π)·‖ζ‖⁻¹`, which is `~ 1/r` in 2D and hence
locally integrable (`∫ r·(1/r) dr dθ < ∞`).  We synthesize this via polar coordinates; the
isolated "`‖x‖⁻¹` loc-integrable on ℝ²" lemma is absent from Mathlib. -/

/-- The Cauchy-transform kernel `K ζ = 1/(π·ζ)`, so that the convolution
`u(z) = (g ⋆ K)(z) = (1/π)∬ g(ζ)/(z-ζ) dA(ζ)` satisfies `∂̄u = g` (Cauchy–Pompeiu, with this
sign convention; see `cauchyPompeiu` / `dbar_cauchyTransform`). -/
noncomputable def cauchyKernel (ζ : ℂ) : ℂ := 1 / (π * ζ)

/-- The inverse function `ζ ↦ ζ⁻¹` is integrable on every closed ball of `ℂ`: in polar
coordinates the area element `r dr dθ` exactly cancels the `1/r` singularity. -/
theorem integrableOn_inv_closedBall (R : ℝ) :
    IntegrableOn (fun ζ : ℂ => ζ⁻¹) (Metric.closedBall 0 R) volume := by
  refine ⟨(measurable_inv).aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  -- The set-lintegral of `‖ζ⁻¹‖ₑ` over the ball, expressed on the whole space via an indicator,
  -- then transported to polar coordinates where the `r`-Jacobian cancels the `r⁻¹` singularity.
  rw [← lintegral_indicator measurableSet_closedBall,
    ← Complex.lintegral_comp_polarCoord_symm]
  -- Bound the polar integrand pointwise by the indicator (value `1`) of the finite-measure
  -- box `B = Ioc 0 R ×ˢ Ioo (-π) π`, then integrate the constant.
  set B : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π with hB
  have hbound : ∀ p ∈ Complex.polarCoord.target,
      ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R).indicator (fun ζ => ‖ζ⁻¹‖ₑ)
          (Complex.polarCoord.symm p)
        ≤ Set.indicator B (fun _ => (1 : ℝ≥0∞)) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    -- `r > 0` and `θ ∈ Ioo (-π) π`; `‖symm (r,θ)‖ = r`.
    simp only [Set.mem_Ioi] at hr
    by_cases hrR : r ≤ R
    · -- inside the ball: the indicator is `‖(symm p)⁻¹‖ₑ = ofReal r⁻¹`, so `ofReal r * ofReal r⁻¹ = 1`.
      have hmem : Complex.polarCoord.symm (r, θ) ∈ Metric.closedBall (0 : ℂ) R := by
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hr]
        exact hrR
      have hpB : (r, θ) ∈ B := ⟨⟨hr, hrR⟩, hθ⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpB]
      have hne : Complex.polarCoord.symm (r, θ) ≠ 0 := by
        rw [← norm_ne_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hr]; exact hr.ne'
      rw [enorm_inv hne, ← ofReal_norm, Complex.norm_polarCoord_symm, abs_of_pos hr,
        smul_eq_mul, ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_mul hr.le,
        mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]
    · -- outside the ball: the closedBall indicator vanishes.
      have hnmem : Complex.polarCoord.symm (r, θ) ∉ Metric.closedBall (0 : ℂ) R := by
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hr]
        exact hrR
      rw [Set.indicator_of_notMem hnmem, smul_zero]; exact zero_le
  calc
    ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R).indicator
            (fun ζ => ‖ζ⁻¹‖ₑ) (Complex.polarCoord.symm p)
        ≤ ∫⁻ p, Set.indicator B (fun _ => (1 : ℝ≥0∞)) p := by
          rw [← lintegral_indicator Complex.polarCoord.open_target.measurableSet]
          refine lintegral_mono fun p => ?_
          by_cases hp : p ∈ Complex.polarCoord.target
          · simpa [Set.indicator_of_mem hp] using hbound p hp
          · rw [Set.indicator_of_notMem hp]; exact zero_le
      _ = volume B := by
          rw [lintegral_indicator (by exact (measurableSet_Ioc.prod measurableSet_Ioo)),
            setLIntegral_const, one_mul]
      _ < ∞ := by
          rw [hB, Measure.volume_eq_prod, Measure.prod_prod]
          exact ENNReal.mul_lt_top (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioo])

/-- **D0.** The Cauchy kernel `K ζ = -(1/(π·ζ))` is locally integrable on `ℂ`. -/
theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  -- `K = (-(1/π) : ℂ) • (·⁻¹)`, and `·⁻¹` is integrable on every compact set (⊆ some closed ball).
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  have hinv : IntegrableOn (fun ζ : ℂ => ζ⁻¹) k volume :=
    (integrableOn_inv_closedBall R).mono_set hR
  have : cauchyKernel = fun ζ : ℂ => ((1 / π) : ℂ) • ζ⁻¹ := by
    funext ζ; simp only [cauchyKernel, smul_eq_mul, one_div, mul_inv]
  rw [this]
  exact hinv.smul ((1 / π) : ℂ)

/-! ## D1 — regularity of the Cauchy transform, derivative onto the smooth factor

For `g ∈ C^∞_c`, the Cauchy transform `u = g ⋆ K` (with the kernel `K`) is `C^∞`, and its
Fréchet derivative is the convolution of `fderiv g` against `K`.  The derivative transfers to
the *smooth* factor `g`, so the rough kernel `K` is never differentiated; we need only
`LocallyIntegrable K` (D0).  We use `L = ContinuousLinearMap.mul ℝ ℂ` (complex multiplication
as an `ℝ`-bilinear map), so `(g ⋆[L] K) x = ∫ t, g t * K (x - t)`. -/

open scoped Convolution in
/-- The Cauchy transform of `g`: `u = g ⋆ K` with `K` the Cauchy kernel, computed against
complex multiplication.  Pointwise `u(x) = ∫ g(t)·K(x−t) dt = -(1/π)∬ g(ζ)/(x−ζ) dA(ζ)`. -/
noncomputable def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel

open scoped Convolution in
/-- **D1 (regularity).** For `g ∈ C^∞_c`, the Cauchy transform `u = g ⋆ K` is `C^∞`. -/
theorem contDiff_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) : ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform g) :=
  hgsupp.contDiff_convolution_left _ hg locallyIntegrable_cauchyKernel

/-! ### Linearity of the Cauchy transform

The Cauchy transform `g ↦ g ⋆ K` is `ℝ`-linear: `smul` pulls out of the convolution integral with no
hypothesis, and additivity splits the integral whenever both convolutions exist (e.g. for
compactly-supported continuous inputs). These are the linearity primitives used to make the
Dolbeault → Čech cocycle operator an honest `ℝ`-linear map. -/

open scoped Convolution in
/-- **`ℝ`-homogeneity of the Cauchy transform** (free — `smul` commutes with the convolution
integral; no integrability needed). -/
theorem cauchyTransform_smul (c : ℝ) (g : ℂ → ℂ) :
    cauchyTransform (c • g) = c • cauchyTransform g := by
  show (c • g) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel
      = c • (g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel)
  exact smul_convolution

open scoped Convolution in
/-- **Additivity of the Cauchy transform** on compactly-supported continuous functions: both
convolution integrands are integrable (`HasCompactSupport.convolutionExists_left` against the locally
integrable kernel), so the integral of the sum splits (`ConvolutionExists.add_distrib`). -/
theorem cauchyTransform_add {f g : ℂ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    cauchyTransform (f + g) = cauchyTransform f + cauchyTransform g :=
  ConvolutionExists.add_distrib
    (hfs.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hf locallyIntegrable_cauchyKernel)
    (hgs.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hg locallyIntegrable_cauchyKernel)

open scoped Convolution in
/-- **D1 (derivative).** For `g ∈ C^∞_c`, the Fréchet derivative of `u = g ⋆ K` is
`(fderiv ℝ g) ⋆ K` (with the precomposed bilinear map), evaluated at each point. -/
theorem hasFDerivAt_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) (x : ℂ) :
    HasFDerivAt (cauchyTransform g)
      (((fderiv ℝ g) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompL ℂ, volume] cauchyKernel) x) x :=
  hgsupp.hasFDerivAt_convolution_left _ (hg.of_le (by exact_mod_cast le_top))
    locallyIntegrable_cauchyKernel x

open scoped Convolution in
/-- **D3 bridge.** `∂̄` commutes through the Cauchy transform onto the *smooth* factor:
`∂̄(g ⋆ K) = (∂̄g) ⋆ K`.  Combined with D1's derivative formula and the fact that the
evaluation maps `T ↦ T 1`, `T ↦ T I` (and hence `dbar`) commute with the Bochner integral. -/
theorem dbar_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) (z : ℂ) :
    dbar (cauchyTransform g) z = (dbar g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel) z := by
  set L := ContinuousLinearMap.mul ℝ ℂ
  -- The CLM-valued convolution integrand (D1's derivative) is integrable: `fderiv g` is
  -- continuous with compact support, `K` is locally integrable.
  have hfd_supp : HasCompactSupport (fderiv ℝ g) := hgsupp.fderiv ℝ
  have hfd_cont : Continuous (fderiv ℝ g) :=
    (hg.continuous_fderiv (by norm_num))
  have hint : Integrable
      (fun t => (L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) volume :=
    hfd_supp.convolutionExists_left (L.precompL ℂ) hfd_cont locallyIntegrable_cauchyKernel z
  -- Integrability of the two scalar integrands (evaluations of the CLM integrand at `1`, `I`).
  have hi1 : Integrable
      (fun t => ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) (1 : ℂ)) volume :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).integrable_comp hint
  have hiI : Integrable
      (fun t => ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I) volume :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).integrable_comp hint
  -- Pull `dbar` (an evaluation-at-`1`/`I` combination) through the convolution integral.
  rw [dbar, (hasFDerivAt_cauchyTransform hg hgsupp z).fderiv, convolution_def,
    ContinuousLinearMap.integral_apply hint, ContinuousLinearMap.integral_apply hint,
    convolution_def]
  -- Merge the two scalar integrals into one (linearity), then compare integrands pointwise.
  have hmul : (Complex.I * ∫ t, ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I)
      = ∫ t, Complex.I * ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I :=
    (integral_const_mul _ _).symm
  rw [hmul, ← integral_add hi1 (hiI.const_mul Complex.I)]
  have hhalf : (2⁻¹ : ℂ) * ∫ t, (((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) 1
        + Complex.I * ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I)
      = ∫ t, (2⁻¹ : ℂ) * (((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) 1
        + Complex.I * ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I) :=
    (integral_const_mul _ _).symm
  rw [hhalf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.precompL_apply, L, ContinuousLinearMap.mul_apply', dbar]
  ring

/-- A function that is `ℂ`-differentiable (holomorphic) at `z` satisfies the
homogeneous Cauchy–Riemann equation `∂̄ f = 0` there.  This is the Wirtinger
characterization and validates the definition of `dbar`. -/
theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : dbar f z = 0 := by
  -- For a `ℂ`-differentiable `f`, the real Fréchet derivative is multiplication by the
  -- complex derivative `f'(z)`: `fderiv ℝ f z = f'(z) • (1 : ℂ →L[ℝ] ℂ)`.
  -- (`HasDerivAt.complexToReal_fderiv` avoids the `restrictScalars` instance-synthesis snag.)
  have hr : fderiv ℝ f z = (deriv f z) • (1 : ℂ →L[ℝ] ℂ) :=
    hf.hasDerivAt.complexToReal_fderiv.fderiv
  -- Evaluate `∂̄f = ½(D 1 + I · D I)` with `D = f'(z) • 1`: `D 1 = f'`, `D I = f'·I`,
  -- so `∂̄f = ½(f' + I·(f'·I)) = ½(f' + I²·f') = 0`.
  rw [dbar, hr]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  have hII : Complex.I * (deriv f z * Complex.I) = - deriv f z := by
    rw [show Complex.I * (deriv f z * Complex.I) = deriv f z * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]; ring
  rw [hII]; ring

/-! ## D2 — the fundamental-solution identity (Cauchy–Pompeiu)

The genuine content: for `g ∈ C^∞_c`, `(∂̄g) ⋆ K = g`, i.e. `∫ t, (∂̄g)(t)·K(z−t) dt = g(z)`.
With `K ζ = 1/(πζ)` this is the Cauchy–Pompeiu formula with NO boundary term (compact support
kills it).  Proof = the complex Green / divergence theorem applied to `ζ ↦ g(ζ)/(ζ−z)` on the
annulus `ε ≤ |ζ−z| ≤ R`: the outer boundary vanishes by support, the inner circle tends to
`2πi·g(z)` as `ε→0` (the residue brick), and the area integral converges by D0. -/

/-- `dbar g` is continuous when `g` is `C^∞` (it is a fixed continuous-linear combination of the
first Fréchet derivative, which is itself continuous). -/
theorem continuous_dbar {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (dbar g) := by
  have hfd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  unfold dbar
  fun_prop

/-- `dbar g` has compact support when `g` does (`dbar` is built from `fderiv g`, whose support
is contained in `tsupport g`). -/
theorem hasCompactSupport_dbar {g : ℂ → ℂ}
    (hgsupp : HasCompactSupport g) : HasCompactSupport (dbar g) := by
  apply HasCompactSupport.intro (hgsupp.fderiv ℝ).isCompact
  intro z hz
  have : fderiv ℝ g z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [dbar, this]

open scoped Convolution in
/-- Integrability of the area integrand `ζ ↦ (∂̄g)(ζ)·K(z−ζ)`: `∂̄g` is continuous with compact
support and `K(z−·)` is locally integrable (a reflection/translation of the kernel `K`). -/
theorem integrable_dbar_mul_cauchyKernel {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) (z : ℂ) :
    Integrable (fun ζ => dbar g ζ * cauchyKernel (z - ζ)) volume := by
  have h := (hasCompactSupport_dbar hgsupp).convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
    (continuous_dbar hg) locallyIntegrable_cauchyKernel z
  simpa only [ContinuousLinearMap.mul_apply'] using h

/-- Evaluate the ℝ-linear map `fderiv ℝ g w` at a complex direction `a + b·I` in the `{1, I}`
basis: `(fderiv ℝ g w)(a + b·I) = a·(fderiv … 1) + b·(fderiv … I)` for real `a, b`. -/
theorem fderiv_apply_basis (g : ℂ → ℂ) (w : ℂ) (a b : ℝ) :
    (fderiv ℝ g w) (a + b * I) = (a : ℂ) * (fderiv ℝ g w) 1 + (b : ℂ) * (fderiv ℝ g w) I := by
  have h1 : ((a : ℂ) + b * I) = a • (1 : ℂ) + b • (I : ℂ) := by
    simp only [Complex.real_smul]; ring
  rw [h1, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- **Polar–Wirtinger identity** (purely algebraic, from ℝ-linearity of `fderiv ℝ g`).
With `c = cos θ + sin θ·I = e^{iθ}`, the anti-radial Wirtinger derivative decomposes into the
radial (`fderiv … c`) and angular (`fderiv … (I·c)`) directional derivatives:
`e^{−iθ}·(2·∂̄g w) = (fderiv ℝ g w) c + I·(fderiv ℝ g w) (I·c)`. -/
theorem dbar_polar_identity (g : ℂ → ℂ) (w : ℂ) (θ : ℝ) :
    (Real.cos θ - Real.sin θ * I) * ((2 : ℂ) * dbar g w)
      = (fderiv ℝ g w) (Real.cos θ + Real.sin θ * I)
        + I * (fderiv ℝ g w) (I * (Real.cos θ + Real.sin θ * I)) := by
  set A := (fderiv ℝ g w) 1 with hA
  set B := (fderiv ℝ g w) I with hB
  -- The radial direction `c = cos θ + sin θ·I`.
  have hbasis : (fderiv ℝ g w) (Real.cos θ + Real.sin θ * I)
      = (Real.cos θ : ℂ) * A + (Real.sin θ : ℂ) * B := fderiv_apply_basis g w _ _
  -- The angular direction `I·c = -sin θ + cos θ·I`.
  have hIc : I * (Real.cos θ + Real.sin θ * I) = ((-Real.sin θ : ℝ) : ℂ) + (Real.cos θ : ℝ) * I := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hbasisI : (fderiv ℝ g w) (I * (Real.cos θ + Real.sin θ * I))
      = (-Real.sin θ : ℂ) * A + (Real.cos θ : ℂ) * B := by
    rw [hIc, fderiv_apply_basis g w _ _]; push_cast; ring
  rw [hbasis, hbasisI, dbar, ← hA, ← hB]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The radial map `r ↦ z + r•c : ℝ → ℂ` (real scalar multiple), as the building block of the
radial slice.  `C^∞` and, for `c ≠ 0`, a closed embedding (proper affine). -/
private noncomputable def radialMap (z c : ℂ) : ℝ → ℂ := fun r => z + r • c

theorem contDiff_radialMap (z c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (radialMap z c) := by
  unfold radialMap; fun_prop

/-- The radial slice `r ↦ g(z + r•c)` is `C^∞`. -/
theorem contDiff_radial {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => g (radialMap z c r)) :=
  hg.comp (contDiff_radialMap z c)

theorem hasCompactSupport_radial {g : ℂ → ℂ} (hgsupp : HasCompactSupport g) {c : ℂ}
    (hc : c ≠ 0) (z : ℂ) : HasCompactSupport (fun r : ℝ => g (radialMap z c r)) := by
  -- `r ↦ z + r•c` is antilipschitz + (uniformly) continuous ⟹ closed embedding; support pulls back.
  have hdist : ∀ a b : ℝ, dist (radialMap z c a) (radialMap z c b) = ‖c‖ * dist a b := by
    intro a b
    have h1 : radialMap z c a - radialMap z c b = ((a - b : ℝ) : ℂ) * c := by
      simp only [radialMap, Complex.real_smul]
      push_cast; ring
    rw [dist_eq_norm, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq, mul_comm]
  have hcpos : (0 : ℝ) < ‖c‖ := by positivity
  have hanti : AntilipschitzWith ⟨‖c‖⁻¹, by positivity⟩ (radialMap z c) := by
    refine AntilipschitzWith.of_le_mul_dist fun a b => ?_
    rw [hdist a b]
    show dist a b ≤ ‖c‖⁻¹ * (‖c‖ * dist a b)
    rw [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
  have hlip : LipschitzWith ⟨‖c‖, norm_nonneg c⟩ (radialMap z c) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [hdist a b]
    show ‖c‖ * dist a b ≤ ‖c‖ * dist a b
    rfl
  exact hgsupp.comp_isClosedEmbedding (hanti.isClosedEmbedding hlip.uniformContinuous)

/-- The radial derivative `deriv (fun r => g(z + r•c)) r = (fderiv ℝ g (z + r•c)) c`. -/
theorem deriv_radial {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z c : ℂ) (r : ℝ) :
    deriv (fun r : ℝ => g (radialMap z c r)) r = (fderiv ℝ g (radialMap z c r)) c := by
  have hg' : DifferentiableAt ℝ g (radialMap z c r) :=
    hg.differentiable (by norm_num) _
  have hmap : HasDerivAt (radialMap z c) c r := by
    show HasDerivAt (fun r : ℝ => z + r • c) c r
    simpa using ((hasDerivAt_id r).smul_const c).const_add z
  exact (hg'.hasFDerivAt.comp_hasDerivAt r hmap).deriv

/-- **The radial integral** produces the answer: `∫_{r>0} (fderiv ℝ g (z+r•c)) c dr = −g(z)`
for `c ≠ 0` (1D fundamental theorem of calculus, compact support kills the `r→∞` endpoint). -/
theorem radial_integral {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    ∫ r in Set.Ioi (0 : ℝ), (fderiv ℝ g (radialMap z c r)) c = -g z := by
  have hkey := (hasCompactSupport_radial hgsupp hc z).integral_Ioi_deriv_eq
    ((contDiff_radial hg z c).of_le (by exact_mod_cast le_top)) 0
  simp only [deriv_radial hg z c] at hkey
  rw [hkey]
  simp [radialMap]

/-- The angular slice `θ ↦ z + r·(cos θ + sin θ·I)` (fixed radius `r`). -/
private noncomputable def angularMap (z : ℂ) (r : ℝ) : ℝ → ℂ :=
  fun θ => z + (r : ℂ) * (Real.cos θ + Real.sin θ * I)

theorem contDiff_angularMap (z : ℂ) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (angularMap z r) := by
  unfold angularMap
  have hcos : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => (Real.cos θ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have hsin : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => (Real.sin θ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  have : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => (Real.cos θ : ℂ) + Real.sin θ * I) :=
    hcos.add (hsin.mul contDiff_const)
  fun_prop

/-- The angular derivative `deriv (fun θ => g(z + r·c(θ))) θ = (fderiv ℝ g w)(r·I·c(θ))`,
where `w = z + r·c(θ)` and `c(θ) = cos θ + sin θ·I`, since `d/dθ c(θ) = I·c(θ)`. -/
theorem deriv_angular {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : ℂ) (r : ℝ) (θ : ℝ) :
    deriv (fun θ : ℝ => g (angularMap z r θ)) θ
      = (fderiv ℝ g (angularMap z r θ))
          ((r : ℂ) * (I * (Real.cos θ + Real.sin θ * I))) := by
  have hg' : DifferentiableAt ℝ g (angularMap z r θ) :=
    hg.differentiable (by norm_num) _
  -- d/dθ [r·(cos θ + sin θ·I)] = r·(-sin θ + cos θ·I) = r·I·(cos θ + sin θ·I).
  have hcderiv : HasDerivAt (fun θ : ℝ => (r : ℂ) * (Real.cos θ + Real.sin θ * I))
      ((r : ℂ) * (I * (Real.cos θ + Real.sin θ * I))) θ := by
    have hcos : HasDerivAt (fun θ : ℝ => (Real.cos θ : ℂ)) (-(Real.sin θ : ℂ)) θ := by
      simpa using (Real.hasDerivAt_cos θ).ofReal_comp
    have hsin : HasDerivAt (fun θ : ℝ => (Real.sin θ : ℂ)) ((Real.cos θ : ℂ)) θ := by
      simpa using (Real.hasDerivAt_sin θ).ofReal_comp
    have hbase : HasDerivAt (fun θ : ℝ => (Real.cos θ : ℂ) + Real.sin θ * I)
        (-(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I) θ :=
      hcos.add (hsin.mul_const I)
    have := hbase.const_mul (r : ℂ)
    convert this using 1
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hmap : HasDerivAt (angularMap z r)
      ((r : ℂ) * (I * (Real.cos θ + Real.sin θ * I))) θ := by
    show HasDerivAt (fun θ : ℝ => z + (r : ℂ) * (Real.cos θ + Real.sin θ * I)) _ θ
    simpa using hcderiv.const_add z
  exact (hg'.hasFDerivAt.comp_hasDerivAt θ hmap).deriv

/-- **The angular integral vanishes**: `∫_{θ∈(−π,π)} (fderiv ℝ g w)(I·c(θ)) dθ = 0`, where
`w = z + r·c(θ)`, `c(θ) = cos θ + sin θ·I`.  By the angular FTC, the integral of the directional
derivative collapses to the endpoints `θ=±π`, and `c(π)=c(−π)=−1`, so they cancel. -/
theorem angular_integral {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : ℂ) {r : ℝ} (hr : r ≠ 0) :
    ∫ θ in (-π)..π, (fderiv ℝ g (angularMap z r θ)) (I * (Real.cos θ + Real.sin θ * I)) = 0 := by
  -- `deriv (g ∘ angularMap) θ = r·(fderiv g w)(I·c(θ))`, so the integrand is `r⁻¹·deriv(…)`.
  have hintegrand : ∀ θ, (fderiv ℝ g (angularMap z r θ)) (I * (Real.cos θ + Real.sin θ * I))
      = (r : ℂ)⁻¹ * deriv (fun θ : ℝ => g (angularMap z r θ)) θ := by
    intro θ
    rw [deriv_angular hg z r θ]
    rw [show ((r : ℂ) * (I * (Real.cos θ + Real.sin θ * I)))
          = (r : ℝ) • (I * (Real.cos θ + Real.sin θ * I)) from by rw [Complex.real_smul],
      map_smul, Complex.real_smul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hr), one_mul]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => g (angularMap z r θ)) :=
    hg.comp (contDiff_angularMap z r)
  simp only [hintegrand]
  -- Pull out `r⁻¹` and apply the angular FTC over `(−π)..π`.
  have hcm : ∫ θ in (-π)..π, (r : ℂ)⁻¹ * deriv (fun θ : ℝ => g (angularMap z r θ)) θ
      = (r : ℂ)⁻¹ * ∫ θ in (-π)..π, deriv (fun θ : ℝ => g (angularMap z r θ)) θ :=
    intervalIntegral.integral_const_mul _ _
  rw [hcm, intervalIntegral.integral_deriv_eq_sub
    (fun θ _ => (hcd.differentiable (by norm_num)).differentiableAt)
    ((hcd.continuous_deriv (by norm_num)).intervalIntegrable _ _)]
  -- `angularMap z r π = z − r = angularMap z r (−π)`, so the difference vanishes.
  have hπ : angularMap z r π = z - r := by
    simp only [angularMap, Real.cos_pi, Real.sin_pi]; push_cast; ring
  have hmπ : angularMap z r (-π) = z - r := by
    simp only [angularMap, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]; push_cast; ring
  rw [hπ, hmπ, sub_self, mul_zero]

/-- A bound `M` beyond which the radial slice leaves `tsupport (fderiv ℝ g)`: there is `M` with
`∀ r > M, ∀ θ, fderiv ℝ g (z + r·c(θ)) = 0` (where `‖c(θ)‖ = 1`). -/
theorem exists_radius_fderiv_eq_zero {g : ℂ → ℂ} (hgsupp : HasCompactSupport g) (z : ℂ) :
    ∃ M : ℝ, ∀ r : ℝ, M < r → ∀ θ : ℝ,
      fderiv ℝ g (z + (r : ℂ) * (Real.cos θ + Real.sin θ * I)) = 0 := by
  obtain ⟨M, hM⟩ := (hgsupp.fderiv ℝ).isBounded.subset_closedBall z
  refine ⟨M, fun r hr θ => ?_⟩
  -- `‖(z + r·c(θ)) − z‖ = r > M`, so the point is outside the closed ball ⊇ tsupport.
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hM hmem
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul] at this
  have hc : ‖(Real.cos θ + Real.sin θ * I : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_add_mul_I, Real.cos_sq_add_sin_sq, Real.sqrt_one]
  rw [hc, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
  have : r ≤ M := le_trans (le_abs_self r) this
  linarith

/-- Integrability on the polar target `Ioi 0 ×ˢ Ioo (−π) π` for a continuous integrand that
vanishes for `r = p.1 > M`: it then lives on the compact `Icc 0 M ×ˢ Icc (−π) π`. -/
theorem integrableOn_target_of_continuous_of_vanishing {f : ℝ × ℝ → ℂ} (hf : Continuous f)
    {M : ℝ} (hvanish : ∀ p : ℝ × ℝ, M < p.1 → f p = 0) :
    IntegrableOn f (Set.Ioi 0 ×ˢ Set.Ioo (-π) π) volume := by
  -- `f` is integrable on the compact box `K = Icc 0 M ×ˢ Icc (−π) π`.
  have hKcompact : IsCompact (Set.Icc (0:ℝ) M ×ˢ Set.Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  have hintK : IntegrableOn f (Set.Icc (0:ℝ) M ×ˢ Set.Icc (-π) π) volume :=
    hf.continuousOn.integrableOn_compact hKcompact
  -- It suffices to integrate over `target ∩ support f ⊆ box`.
  refine IntegrableOn.of_inter_support (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  refine hintK.mono_set fun p hp => ?_
  obtain ⟨⟨hr, hθ⟩, hsupp⟩ := hp
  refine ⟨⟨le_of_lt hr, ?_⟩, ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩
  -- `p.1 ≤ M`: else `f p = 0`, contradicting `p ∈ support f`.
  by_contra h
  exact hsupp (hvanish p (lt_of_not_ge h))

/-- **D2 core — the Cauchy–Pompeiu area-integral identity.**  For `g ∈ C^∞_c`,
`∬_ℂ (∂̄g)(ζ)/(ζ−z) dA(ζ) = −π·g(z)`.

This is THE genuine mathematical content of the ∂̄-disk atom and the single remaining gap.

PLANNED PROOF — polar coordinates (NOT Green's theorem; this route avoids the unscaffolded
annulus-divergence theorem entirely):
1. Translate `ζ ↦ z + w` (`integral_add_left_eq_self`): `∫ (∂̄g)(ζ)/(ζ−z) = ∫ (∂̄g)(z+w)/w`.
2. Polar change of variables (`Complex.integral_comp_polarCoord_symm`): the Jacobian factor `r`
   cancels `1/w` (`r/(r e^{iθ}) = e^{−iθ}`), giving
   `∫_{(r,θ)∈(0,∞)×(−π,π)} e^{−iθ}·(∂̄g)(z + r e^{iθ}) dr dθ`.
3. The polar-Wirtinger identity `dbar_polar_identity` (PROVEN): rewrites the integrand as a
   ½-combination of the radial directional derivative `(fderiv g w) c` and the angular one
   `(fderiv g w)(I·c)`, where `c = e^{iθ}`, `w = z + r·c`.
4. The radial part integrates over `r∈(0,∞)` to `−g(z)` (`radial_integral`, PROVEN), then over
   `θ` to `−2π·g(z)`.  The angular part integrates over `θ∈(−π,π)` to `0` (`angular_integral`,
   PROVEN: `c(π)=c(−π)=−1`).  Net `½·(−2π·g(z)) = −π·g(z)`.

BOTH genuine analytic pieces — the radial FTC (`radial_integral`) and the angular vanishing
(`angular_integral`) — are PROVEN axiom-clean.  Steps 1–4 below are DONE (translation,
polar CoV, the `e^{−iθ}` simplification, and the `dbar_polar_identity` rewrite), reducing the goal
to `∫_{target} ½·(R(p) + I·A(p)) = −π·g(z)` with `R = (fderiv g w) c` (radial), `A = (fderiv g w)(I·c)`
(angular), `w = radialMap z (c θ) r`.  REMAINING GAP: only the final split + Fubini interchange:
`½[∫_target R + I·∫_target A]`, with `∫_target R = ∫_θ (∫_r R) = ∫_θ (−g z) = −2π·g(z)` (Fubini,
`radial_integral`) and `∫_target A = ∫_r (∫_θ A) = ∫_r 0 = 0` (Fubini-swapped, `angular_integral`).
The blocker is the Fubini integrability side-conditions on `target = Ioi 0 ×ˢ Ioo(−π) π` (no
packaged polar-integrability transport in Mathlib).  ~50–100 LoC.  See the probe report. -/
theorem cauchyPompeiu_area {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (z : ℂ) : ∫ ζ, dbar g ζ / (ζ - z) = -π * g z := by
  -- Step 1: translate `ζ = z + w`.
  have htrans : ∫ ζ, dbar g ζ / (ζ - z) = ∫ w, dbar g (z + w) / w := by
    rw [← integral_add_left_eq_self (fun ζ => dbar g ζ / (ζ - z)) z]
    simp only [add_sub_cancel_left]
  -- Step 2: polar change of variables `w = symm (r,θ) = r·(cos θ + sin θ·I)`.
  rw [htrans, ← Complex.integral_comp_polarCoord_symm (fun w => dbar g (z + w) / w)]
  -- Step 3: simplify the integrand on `target` (where `r = p.1 > 0`): the Jacobian `r` cancels
  -- the `1/w`, leaving `(cos θ − sin θ·I)·dbar g(z + r·c(θ))`.
  have hsimp : ∀ p ∈ Complex.polarCoord.target,
      p.1 • (dbar g (z + Complex.polarCoord.symm p) / Complex.polarCoord.symm p)
        = (Real.cos p.2 - Real.sin p.2 * I)
            * dbar g (z + (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I)) := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Complex.polarCoord_symm_apply, Set.mem_Ioi] at hr ⊢
    rw [Complex.real_smul]
    have hcne : (Real.cos θ + Real.sin θ * I : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.normSq h
      rw [Complex.normSq_add_mul_I, Real.cos_sq_add_sin_sq] at this
      simp at this
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    -- `(cos − sin·I)·(cos + sin·I) = cos² + sin² = 1`, the key scalar cancellation.
    have hconj : (Real.cos θ - Real.sin θ * I) * (Real.cos θ + Real.sin θ * I) = 1 := by
      rw [show (Real.cos θ - Real.sin θ * I : ℂ) * (Real.cos θ + Real.sin θ * I)
          = (Real.cos θ : ℂ)^2 - (Real.sin θ : ℂ)^2 * (Complex.I)^2 by ring, Complex.I_sq]
      rw [show ((Real.cos θ : ℂ)^2 - (Real.sin θ : ℂ)^2 * (-1))
          = ((Real.cos θ ^ 2 + Real.sin θ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Real.cos_sq_add_sin_sq, Complex.ofReal_one]
    -- Factor `dbar g(arg)` out and cancel.
    generalize dbar g (z + (r : ℂ) * (Real.cos θ + Real.sin θ * I)) = D
    rw [mul_div_assoc']
    rw [div_eq_iff (mul_ne_zero hrne hcne)]
    rw [show (Real.cos θ - Real.sin θ * I : ℂ) * D * ((r : ℂ) * (Real.cos θ + Real.sin θ * I))
        = (r : ℂ) * ((Real.cos θ - Real.sin θ * I) * (Real.cos θ + Real.sin θ * I)) * D by ring,
      hconj]
    ring
  refine Eq.trans (MeasureTheory.setIntegral_congr_fun (μ := volume)
    Complex.polarCoord.open_target.measurableSet hsimp) ?_
  -- Step 4: apply the polar–Wirtinger identity, rewriting the integrand as a ½-combination of the
  -- radial and angular directional derivatives at `w = z + r·c(θ) = radialMap z (c θ) r`.
  have hpw : ∀ p : ℝ × ℝ,
      (Real.cos p.2 - Real.sin p.2 * I) * dbar g (z + (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I))
        = (2 : ℂ)⁻¹ * ((fderiv ℝ g (radialMap z (Real.cos p.2 + Real.sin p.2 * I) p.1))
              (Real.cos p.2 + Real.sin p.2 * I)
            + I * (fderiv ℝ g (radialMap z (Real.cos p.2 + Real.sin p.2 * I) p.1))
              (I * (Real.cos p.2 + Real.sin p.2 * I))) := by
    intro p
    have hwarg : z + (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I)
        = radialMap z (Real.cos p.2 + Real.sin p.2 * I) p.1 := by
      rw [radialMap, Complex.real_smul]
    rw [hwarg]
    have := dbar_polar_identity g (radialMap z (Real.cos p.2 + Real.sin p.2 * I) p.1) p.2
    rw [show (Real.cos p.2 - Real.sin p.2 * I : ℂ)
          * dbar g (radialMap z (Real.cos p.2 + Real.sin p.2 * I) p.1)
        = (2 : ℂ)⁻¹ * ((Real.cos p.2 - Real.sin p.2 * I)
          * ((2 : ℂ) * dbar g (radialMap z (Real.cos p.2 + Real.sin p.2 * I) p.1))) by ring,
      this]
  refine Eq.trans (MeasureTheory.setIntegral_congr_fun (μ := volume)
    Complex.polarCoord.open_target.measurableSet (fun p _ => hpw p)) ?_
  -- Name the integrands and the polar target (`polarCoord.target = Ioi 0 ×ˢ Ioo (−π) π` by `rfl`).
  set c : ℝ → ℂ := fun θ => Real.cos θ + Real.sin θ * I with hc
  set Rfun : ℝ × ℝ → ℂ := fun p => (fderiv ℝ g (radialMap z (c p.2) p.1)) (c p.2) with hR
  set Afun : ℝ × ℝ → ℂ := fun p => (fderiv ℝ g (radialMap z (c p.2) p.1)) (I * c p.2) with hA
  set T : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo (-π) π with hT
  show ∫ p in T, (2 : ℂ)⁻¹ * (Rfun p + I * Afun p) = -π * g z
  -- Continuity of the integrands (`fderiv g` is continuous, `radialMap`/`c` are smooth, and the
  -- CLM-evaluation `(L, v) ↦ L v` is continuous).
  have hfdcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hccont : Continuous c := by rw [hc]; fun_prop
  have hradcont : Continuous (fun p : ℝ × ℝ => radialMap z (c p.2) p.1) := by
    have : (fun p : ℝ × ℝ => radialMap z (c p.2) p.1)
        = fun p => z + (p.1 : ℂ) * c p.2 := by
      funext p; rw [radialMap, Complex.real_smul]
    rw [this]
    fun_prop
  have hRcont : Continuous Rfun :=
    isBoundedBilinearMap_apply.continuous.comp ((hfdcont.comp hradcont).prodMk
      (hccont.comp continuous_snd))
  have hAcont : Continuous Afun :=
    isBoundedBilinearMap_apply.continuous.comp ((hfdcont.comp hradcont).prodMk
      (continuous_const.mul (hccont.comp continuous_snd)))
  -- Both integrands vanish for `r = p.1 > M` (the radial slice leaves `tsupport (fderiv g)`).
  obtain ⟨M, hMvanish⟩ := exists_radius_fderiv_eq_zero hgsupp z
  have hwval : ∀ p : ℝ × ℝ, radialMap z (c p.2) p.1
      = z + (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I) := fun p => by
    rw [radialMap, hc, Complex.real_smul]
  have hRvanish : ∀ p : ℝ × ℝ, M < p.1 → Rfun p = 0 := fun p hp => by
    rw [hR]; simp only; rw [hwval p, hMvanish p.1 hp p.2]; rfl
  have hAvanish : ∀ p : ℝ × ℝ, M < p.1 → Afun p = 0 := fun p hp => by
    rw [hA]; simp only; rw [hwval p, hMvanish p.1 hp p.2]; rfl
  have hRint : IntegrableOn Rfun T volume :=
    integrableOn_target_of_continuous_of_vanishing hRcont hRvanish
  have hAint : IntegrableOn Afun T volume :=
    integrableOn_target_of_continuous_of_vanishing hAcont hAvanish
  -- Split: `∫ ½(R + I·A) = ½(∫R + I·∫A)`.
  have haddint : ∫ p in T, (Rfun p + I * Afun p)
      = (∫ p in T, Rfun p) + ∫ p in T, I * Afun p :=
    integral_add hRint (hAint.const_mul I)
  have hcmI : ∫ p in T, I * Afun p = I * ∫ p in T, Afun p := integral_const_mul _ _
  have hcmhalf : ∫ p in T, (2 : ℂ)⁻¹ * (Rfun p + I * Afun p)
      = (2 : ℂ)⁻¹ * ∫ p in T, (Rfun p + I * Afun p) := integral_const_mul _ _
  rw [hcmhalf, haddint, hcmI]
  -- For each fixed `θ`, `c θ ≠ 0` (since `‖c θ‖ = 1`).
  have hcne : ∀ θ : ℝ, c θ ≠ 0 := fun θ => by
    rw [hc]; intro h
    have := congrArg Complex.normSq h
    rw [Complex.normSq_add_mul_I, Real.cos_sq_add_sin_sq] at this; simp at this
  -- Radial term: `∫_T R = ∫_θ (∫_r R) = ∫_θ (−g z) = −2π·g z` (Fubini, `radial_integral`).
  have hRval : (∫ p in T, Rfun p) = -π * (2 * g z) := by
    have hRint' : IntegrableOn Rfun (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod ℝ ℝ]; rw [hT] at hRint; exact hRint
    rw [hT, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
      ← setIntegral_prod_swap (Set.Ioi (0:ℝ)) (Set.Ioo (-π) π) Rfun]
    rw [setIntegral_prod (fun z => Rfun z.swap) hRint'.swap]
    -- Inner integral over `r` is `radial_integral` (= −g z); then integrate the constant over θ.
    rw [show (fun θ => ∫ r in Set.Ioi (0:ℝ), Rfun (Prod.swap (θ, r)))
          = fun _ : ℝ => -g z from funext fun θ => by
        simp only [Prod.swap]
        exact radial_integral hg hgsupp (hcne θ) z]
    have hpi : (0:ℝ) ≤ π - -π := by nlinarith [Real.pi_pos]
    rw [setIntegral_const, Real.volume_real_Ioo, max_eq_left hpi]
    -- `(π−−π) • (−g z) = −π·(2·g z)`: `setIntegral_const`'s `ℝ•ℂ` is a defeq-but-not-syntactic
    -- instance vs `Complex.real_smul` (a `SMul ℝ ℂ` diamond), so `rw`/`simp [real_smul]` miss it.
    -- `show` the mul-form (defeq unfolds the smul instance), then `push_cast; ring`.
    show ((π - -π : ℝ) : ℂ) * (-g z) = -↑π * (2 * g z)
    push_cast; ring
  -- Angular term: `∫_T A = ∫_r (∫_θ A) = ∫_r 0 = 0` (Fubini, `angular_integral`).
  have hAval : (∫ p in T, Afun p) = 0 := by
    have hAint' : IntegrableOn Afun (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod ℝ ℝ]; rw [hT] at hAint; exact hAint
    rw [hT, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
      setIntegral_prod Afun hAint']
    -- Inner `θ`-integral vanishes for each `r ∈ Ioi 0` (angular FTC, `c(π)=c(−π)=−1`).
    rw [MeasureTheory.setIntegral_congr_fun (μ := volume) measurableSet_Ioi
      (g := fun _ : ℝ => (0 : ℂ)) (fun r hr => ?_), integral_zero]
    -- For `r > 0`: the inner `θ`-integral over `Ioo (−π) π` equals the interval integral over
    -- `(−π)..π` (a.e.-equal endpoints), which is `angular_integral`'s `0`.
    -- (Isolated `Ioo`-vs-`Ioc` set/interval reconciliation; see report.)
    have hra : ∀ θ, Afun (r, θ) = (fderiv ℝ g (angularMap z r θ))
        (I * (Real.cos θ + Real.sin θ * I)) := fun θ => by
      rw [hA]; simp only
      congr 2
    have hang := angular_integral hg z (show (0:ℝ) < r by simpa using hr).ne'
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)] at hang
    simp only [hra]
    -- Close the residual `∫_Ioo F = ∫_Ioc F ∂volume`: the two sets differ only by `{π}`
    -- (measure zero), so the set-integrals agree (`volume` has `NoAtoms`).
    rw [← hang, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hRval, hAval, mul_zero, add_zero]
  field_simp

open scoped Convolution in
/-- **D2 (Cauchy–Pompeiu).** For `g ∈ C^∞_c`, `(∂̄g) ⋆ K = g`.  Reduces by elementary algebra to
the area-integral identity `cauchyPompeiu_area`. -/
theorem cauchyPompeiu {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (z : ℂ) : (dbar g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel) z = g z := by
  -- Unfold the convolution and rewrite the kernel: `(∂̄g ⋆ K) z = ∫ (∂̄g ζ)·K(z−ζ)`.
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply', cauchyKernel]
  -- `K(z−ζ) = 1/(π(z−ζ)) = -(1/π)·(1/(ζ−z))`, so the integral is `-(1/π)·∫ (∂̄g ζ)/(ζ−z)`.
  have hker : ∀ ζ, dbar g ζ * (1 / (↑π * (z - ζ))) = (-(1 / ↑π)) * (dbar g ζ / (ζ - z)) := by
    intro ζ
    rcases eq_or_ne (ζ - z) 0 with h | h
    · have hzζ : z - ζ = 0 := by linear_combination -h
      simp [h, hzζ]
    · have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hzζ : z - ζ ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp h).symm
      field_simp
      ring
  have hfun : (fun ζ => dbar g ζ * (1 / (↑π * (z - ζ))))
      = (fun ζ => (-(1 / ↑π)) * (dbar g ζ / (ζ - z))) := funext hker
  rw [hfun]
  have hcm : ∫ ζ, (-(1 / ↑π)) * (dbar g ζ / (ζ - z))
      = (-(1 / ↑π)) * ∫ ζ, dbar g ζ / (ζ - z) := integral_const_mul _ _
  rw [hcm, cauchyPompeiu_area hg hgsupp z]
  field_simp

/-! ## D3 — assemble: the ∂̄-solvability atom -/

/-- **Main theorem (∂̄-on-a-disk solvability atom).** For `g ∈ C^∞_c(ℂ)`, the Cauchy transform
`u = g ⋆ K` is a `C^∞` solution of the inhomogeneous Cauchy–Riemann equation `∂̄u = g`
everywhere.  Combines D1 (regularity), the D3 bridge `∂̄(g⋆K) = (∂̄g)⋆K`, and D2 (Cauchy–Pompeiu
`(∂̄g)⋆K = g`). -/
theorem dbar_solvable_of_compactSupport {g : ℂ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) :
    ∃ u : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ z, dbar u z = g z := by
  refine ⟨cauchyTransform g, contDiff_cauchyTransform hg hgsupp, fun z => ?_⟩
  rw [dbar_cauchyTransform hg hgsupp z, cauchyPompeiu hg hgsupp z]

end DbarDisk
