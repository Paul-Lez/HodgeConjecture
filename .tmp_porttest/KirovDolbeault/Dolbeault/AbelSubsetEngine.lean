/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.AbelSubsetPairing
import KirovDolbeault.Abel

/-!
# Abel ⊆ campaign, E-block: the Forster §20 weak-solution engine

Rungs E0/E1/E2/E5 of `docs/planning/AB_E_ROUTE.md` (the E-block refinement of
`docs/planning/AB_ROUTE.md`): from the P-block's ∂̄-solvability theorem
(`dbar_solvable_of_pairOmega_eq_zero`, `AbelSubsetPairing.lean`) to the meromorphic function
with prescribed divisor — the port-side engine behind the A-block's named hypothesis
`ZeroPeriodChainSolvability` (PR #211, `Jacobians/RiemannSurface/AbelPlumbing.lean`).

Main declarations:

* `SmoothOneChain` (**E0**) — a 1-chain: finitely many `IsSmoothPath`s with ℤ-coefficients;
  `boundary` (the divisor `∂c = ∑ᵢ nᵢ·((tgtᵢ) − (srcᵢ))`, degree 0 by `deg_boundary`);
  `period α c = ∑ᵢ nᵢ·∫_{γᵢ} α`, additive and `ℂ`-homogeneous in the form (`periodL`),
  integrability from the paths' `velCont` field.
* `period_eq_zero_of_spanning` (**E1**) — periods vanishing on a spanning family of
  `H⁰(X, Ω¹)` vanish for every holomorphic 1-form.  This is all that survives of the
  classical "correct the periods into `2πi·ℤ`" step: on the §20 route the chain itself
  carries the homology data (the pinned-loop part of `HasZeroPeriodLoopPresentation` is the
  correction, done root-side), so its periods are exactly zero and only the
  basis-to-all-forms linear algebra remains port-side.
* `LogDbarDatum` (**E2**, the weak-solution interface) — the Forster 20.4/20.5 output
  bundled: the weak solution `F` (locally `unit·z^{∂c(a)}`, `≡ 1` off the chain), its global
  smooth `(0,1)` logarithmic datum `σ = ∂̄ log F`, the **E4 pairing identity**
  `∫_X σ∧α = 2πi·∫_c α` as a field, and the two exp-correction laws (W1/W2 of
  `AB_E_ROUTE.md` §2 in consequence form): a global smooth `u` with `∂̄u = σ` makes
  `F·e^{−u}` meromorphic with divisor `∂c`.  The constructor discharging these fields from
  the per-arc `exp(ψ·log((z−b)/(z−a)))` construction is rung E3 (open).
* `exists_meromorphic_of_logDbarDatum` / `exists_meromorphic_of_zeroPeriodChain` (**E5**) —
  the engine assembly: zero periods + E4 ⟹ `∫_X σ∧α = 0` for all `α` ⟹ (P6)
  `σ = ∂̄u` ⟹ `f := F·e^{−u}` is meromorphic with `div f = ∂c`.

The root-side adapter (E6, separate Bridge file) translates `HasZeroPeriodLoopPresentation`
into a `SmoothOneChain` with vanishing bridged-basis periods and the port divisor of the
output back into root `PrincipalDivisors` membership — see `AB_E_ROUTE.md` §0.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §§20.1–20.7; Miranda,
*Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VIII §4.
-/

open Complex
open scoped Manifold ContDiff Topology Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## E0 — the smooth 1-chain layer -/

/-- **E0: a smooth 1-chain** on `X`: finitely many smooth paths (the port's `IsSmoothPath`
regularity, which carries the `velCont` integrability provision) with ℤ-coefficients.
Forster §20.1's chains, in the representation the engine consumes. -/
structure SmoothOneChain (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The number of weighted paths. -/
  n : ℕ
  /-- The ℤ-coefficient of each path. -/
  coeff : Fin n → ℤ
  /-- The start point of each path. -/
  src : Fin n → X
  /-- The end point of each path. -/
  tgt : Fin n → X
  /-- The paths themselves. -/
  path : Fin n → ℝ → X
  /-- Smooth-path regularity (endpoints + continuity + chart differentiability +
  velocity-section continuity). -/
  smooth : ∀ i, IsSmoothPath (src i) (tgt i) (path i)

namespace SmoothOneChain

variable (c : SmoothOneChain X)

/-- The **boundary divisor** `∂c = ∑ᵢ nᵢ·((tgtᵢ) − (srcᵢ))`. -/
def boundary : Divisor X :=
  ∑ i, c.coeff i • (Finsupp.single (c.tgt i) (1 : ℤ) - Finsupp.single (c.src i) (1 : ℤ))

/-- A 1-chain boundary has degree zero. -/
theorem deg_boundary : Divisor.deg X c.boundary = 0 := by
  rw [boundary, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_zsmul, map_sub, Divisor.deg_single, Divisor.deg_single, sub_self, smul_zero]

/-- The **period** `∫_c α = ∑ᵢ nᵢ·∫_{γᵢ} α` of a holomorphic 1-form over the chain. -/
def period (α : HolomorphicOneForms X) : ℂ :=
  ∑ i, (c.coeff i : ℂ) * lineIntegral α (c.path i)

/-- Periods are additive in the form (integrability from the paths' `velCont`). -/
theorem period_add (α β : HolomorphicOneForms X) :
    c.period (α + β) = c.period α + c.period β := by
  rw [period, period, period, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineIntegral_add α β (c.path i)
      (intervalIntegrable_form_pathSpeed_of_velContinuous α (c.path i) (c.smooth i).velCont)
      (intervalIntegrable_form_pathSpeed_of_velContinuous β (c.path i) (c.smooth i).velCont),
    mul_add]

/-- Periods are `ℂ`-homogeneous in the form. -/
theorem period_smul (a : ℂ) (α : HolomorphicOneForms X) :
    c.period (a • α) = a * c.period α := by
  rw [period, period, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineIntegral_smul]
  ring

/-- The period functional of the chain, as a `ℂ`-linear map on `H⁰(X, Ω¹)`. -/
def periodL : HolomorphicOneForms X →ₗ[ℂ] ℂ where
  toFun := c.period
  map_add' := c.period_add
  map_smul' a α := by simpa using c.period_smul a α

@[simp] theorem periodL_apply (α : HolomorphicOneForms X) : c.periodL α = c.period α := rfl

/-! ## E1 — zero-period extension from a spanning family

The Route-A residue of the classical "period correction" step: the chain (not a
meromorphic form) carries the homology data, its basis periods are exactly zero, and
linearity extends the vanishing to all of `H⁰(X, Ω¹)`. -/

/-- **E1: zero-period extension.**  If the periods of `c` vanish on a spanning family of
`H⁰(X, Ω¹)` (in the application: the `bridgeKDFormEquiv`-image of `jacobianBasis`), they
vanish for every holomorphic 1-form. -/
theorem period_eq_zero_of_spanning {ι : Type*} (b : ι → HolomorphicOneForms X)
    (hspan : Submodule.span ℂ (Set.range b) = ⊤)
    (h0 : ∀ j, c.period (b j) = 0) (α : HolomorphicOneForms X) :
    c.period α = 0 := by
  have hker : (⊤ : Submodule ℂ (HolomorphicOneForms X)) ≤ LinearMap.ker c.periodL := by
    rw [← hspan]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨j, rfl⟩
    exact h0 j
  exact LinearMap.mem_ker.mp (hker Submodule.mem_top)

end SmoothOneChain

/-! ## E2 — the weak-solution interface (Forster 20.4/20.5 output) -/

/-- **E2: the logarithmic-`∂̄` datum of a chain** — the bundled output of the Forster
20.4/20.5 weak-solution construction for `c`:

* `F` — the weak solution: smooth and nonvanishing off the chain, locally
  `unit·z^{∂c(a)}` at each boundary point (these geometric facts are not recorded as
  fields; their *consequences* `mero_correction`/`div_correction` are — the W1/W2 walls of
  `AB_E_ROUTE.md` §2 in consequence form, discharged by the E3 constructor);
* `σ` — the global smooth `(0,1)`-form `∂̄ log F` (smooth ACROSS the boundary points since
  `F` is locally a unit times a holomorphic power there);
* `pairing` — the **E4 identity** `∫_X σ∧α = 2πi·∫_c α` (Forster 20.3/20.5);
* `mero_correction`/`div_correction` — any global smooth `∂̄`-antiderivative `u` of `σ`
  corrects `F` to the meromorphic `F·e^{−u}` with divisor `∂c`: off the chain
  `∂̄(F·e^{−u}) = e^{−u}·(∂̄F − F·∂̄u) = F·e^{−u}·(σ − σ) = 0`, and near a boundary point
  `a` the local form `unit·z^{∂c(a)}·e^{−u}` has a removable-singularity meromorphic
  extension of order `∂c(a)`. -/
structure LogDbarDatum (𝔇 : ChartDiskCover X) (c : SmoothOneChain X) where
  /-- The weak solution. -/
  F : X → ℂ
  /-- The global smooth `(0,1)` logarithmic datum `σ = ∂̄ log F`. -/
  σ : ↥(OneFormsZeroOne X)
  /-- E4, the pairing identity: `∫_X σ∧α = 2πi·∫_c α` for every holomorphic 1-form. -/
  pairing : ∀ α : HolomorphicOneForms X,
    FineResidue.pairOmega 𝔇 σ α = 2 * (Real.pi : ℂ) * Complex.I * c.period α
  /-- W1 (consequence form): a global smooth `∂̄`-antiderivative of `σ` corrects `F` to a
  meromorphic function. -/
  mero_correction : ∀ u : SmoothCFunctions X, dbarL u = (σ : SmoothCOneForms X) →
    IsMeromorphic X fun x => F x * Complex.exp (-(u x))
  /-- W2 (consequence form): the corrected function has divisor `∂c`. -/
  div_correction : ∀ (u : SmoothCFunctions X) (hu : dbarL u = (σ : SmoothCOneForms X)),
    MeromorphicFunction.div X ⟨fun x => F x * Complex.exp (-(u x)), mero_correction u hu⟩ =
      c.boundary

/-! ## E5 — the engine assembly -/

/-- **E5: the weak-solution engine** (Forster §20, proof of Abel's theorem, ⟸ direction):
a chain with a logarithmic-`∂̄` datum and **all** periods zero bounds a principal divisor —
there is a meromorphic function with `div f = ∂c`.

Assembly: zero periods + the E4 pairing field ⟹ `∫_X σ∧α = 0` for every holomorphic `α`
⟹ (**P6**, `dbar_solvable_of_pairOmega_eq_zero`) `σ = ∂̄u` for a global smooth `u` ⟹ the
correction fields make `f := F·e^{−u}` meromorphic with divisor `∂c`. -/
theorem exists_meromorphic_of_logDbarDatum (𝔇 : ChartDiskCover X) (c : SmoothOneChain X)
    (W : LogDbarDatum 𝔇 c) (hper : ∀ α : HolomorphicOneForms X, c.period α = 0) :
    ∃ f : MeromorphicFunction X, MeromorphicFunction.div X f = c.boundary := by
  have hzero : ∀ α : HolomorphicOneForms X, FineResidue.pairOmega 𝔇 W.σ α = 0 := fun α => by
    rw [W.pairing α, hper α, mul_zero]
  obtain ⟨u, hu⟩ := FineResidue.dbar_solvable_of_pairOmega_eq_zero 𝔇 W.σ hzero
  exact ⟨⟨_, W.mero_correction u hu⟩, W.div_correction u hu⟩

/-- **E5 at a spanning family** (the adapter-facing form): zero periods need only be
checked on a spanning family of `H⁰(X, Ω¹)` — in the application, the bridged
`jacobianBasis`, whose periods vanish by `HasZeroPeriodLoopPresentation`. -/
theorem exists_meromorphic_of_zeroPeriodChain (𝔇 : ChartDiskCover X) (c : SmoothOneChain X)
    (W : LogDbarDatum 𝔇 c) {ι : Type*} (b : ι → HolomorphicOneForms X)
    (hspan : Submodule.span ℂ (Set.range b) = ⊤)
    (h0 : ∀ j, c.period (b j) = 0) :
    ∃ f : MeromorphicFunction X, MeromorphicFunction.div X f = c.boundary :=
  exists_meromorphic_of_logDbarDatum 𝔇 c W (c.period_eq_zero_of_spanning b hspan h0)

/-! ## E3 groundwork — the slit-segment logarithm (planar layer)

The geometric core of the Forster 20.5 one-disk weak solution `exp(ψ·log((z−b)/(z−a)))`:
off the closed segment `[a, b]`, the Möbius ratio `(z−b)/(z−a)` avoids the closed negative
real axis, so `Complex.log` composes holomorphically and exponentiates back to the ratio.
(The cutoff `ψ`, the gluing across the open segment, and the resulting `LogDbarDatum`
constructor are the rest of rung E3.) -/

section SlitSegment

/-- A real segment in `ℂ` is compact (image of `[0,1]` under the affine parametrization). -/
theorem isCompact_segment (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image ℝ a b]
  exact isCompact_Icc.image (by fun_prop)

/-- **Slit avoidance**: off the closed segment `[a, b]`, the ratio `(z−b)/(z−a)` lies in
the slit plane `ℂ ∖ ℝ≤0`.  (If the ratio were a nonpositive real `t`, then
`z = (−t·a + b)/(1−t)` would be a convex combination of `a` and `b`.) -/
theorem ratio_mem_slitPlane_of_notMem_segment {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    (z - b) / (z - a) ∈ Complex.slitPlane := by
  have hza : z ≠ a := fun h => hz (h ▸ left_mem_segment ℝ a b)
  by_contra hmem
  rw [Complex.mem_slitPlane_iff] at hmem
  push Not at hmem
  obtain ⟨hre, him⟩ := hmem
  set w : ℂ := (z - b) / (z - a) with hw
  set t : ℝ := w.re with ht
  have hwt : w = (t : ℂ) := Complex.ext rfl (by simpa using him)
  have hzb' : z - b = (t : ℂ) * (z - a) := by
    have h1 : z - b = w * (z - a) := (div_eq_iff (sub_ne_zero.mpr hza)).mp hw.symm
    rw [h1, hwt]
  have ht0 : t ≤ 0 := hre
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h1t' : ((1 : ℂ) - (t : ℂ)) ≠ 0 := by exact_mod_cast h1t.ne'
  have key : ((1 : ℂ) - (t : ℂ)) * z = b - (t : ℂ) * a := by linear_combination hzb'
  refine hz ⟨-t / (1 - t), 1 / (1 - t), div_nonneg (neg_nonneg.mpr ht0) h1t.le,
    by positivity, by field_simp; ring, ?_⟩
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp
  linear_combination -key

/-- The **slit-segment logarithm** `log((z−b)/(z−a))`: the single-valued branch off the
segment `[a, b]` whose exponential is the Möbius ratio with zero at `b` and pole at `a`.
Forster 20.5's `g`. -/
noncomputable def slitLogRatio (a b z : ℂ) : ℂ :=
  Complex.log ((z - b) / (z - a))

/-- The slit-segment logarithm is `ℂ`-differentiable off the segment. -/
theorem differentiableAt_slitLogRatio {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    DifferentiableAt ℂ (slitLogRatio a b) z := by
  have hza : z ≠ a := fun h => hz (h ▸ left_mem_segment ℝ a b)
  have hdiv : DifferentiableAt ℂ (fun w => (w - b) / (w - a)) z :=
    (differentiableAt_id.sub_const b).div (differentiableAt_id.sub_const a)
      (sub_ne_zero.mpr hza)
  exact hdiv.clog (ratio_mem_slitPlane_of_notMem_segment hz)

/-- Off the segment, `exp(slitLogRatio a b z) = (z−b)/(z−a)`: the weak solution really is
the Möbius ratio wherever the cutoff is `1`. -/
theorem exp_slitLogRatio {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    Complex.exp (slitLogRatio a b z) = (z - b) / (z - a) := by
  have hza : z ≠ a := fun h => hz (h ▸ left_mem_segment ℝ a b)
  have hzb : z ≠ b := fun h => hz (h ▸ right_mem_segment ℝ a b)
  exact Complex.exp_log (div_ne_zero (sub_ne_zero.mpr hzb) (sub_ne_zero.mpr hza))

end SlitSegment

end Jacobians.Dolbeault

end
