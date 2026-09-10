import KirovDolbeault.Montel.ChartTransition
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Montel path — completeness of `HolomorphicOneForms X`

This file proves `CompleteSpace (HolomorphicOneForms X)` under the
canonical supNormK-based normed structure. Combined with precompactness
of closed unit ball (from Arzelà–Ascoli in `Compactness.lean`), this
yields `IsCompact (closedBall 0 1)` — the missing piece in the Montel
conclusion.

## Proof outline

Given a Cauchy sequence `α_n` in supNormK:
1. Per-chart: `localRep α_n x₀` is uniformly Cauchy on `shrunkChart x₀`
   (since supNormK bounds chart-wise values).
2. Uniform Cauchy on compact + ℂ complete ⇒ uniform convergence to
   some `g_{x₀} : shrunkChart x₀ → ℂ` (continuous).
3. Pointwise limit exists in CLM space: `α_n.toFun y → α∞(y)` in
   operator norm for each y ∈ X.
4. Chart-wise analyticity of pullbacks ⇒ α∞ is `ContMDiffSection ω`
   (via `analyticOn_of_pullback_tendsto_locally_uniformly`).
5. `α_n → α∞` in supNormK.

Step 4 is the heart of the argument; it requires assembling the
analytic chart-pullbacks back into a bundle section.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff Topology
open Bundle Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step 1 — Per-chart uniform Cauchy from supNormK Cauchy

`supNormK = sup over chartCover of chartNormK`, where `chartNormK α x₀
= sup_{y ∈ shrunkChart x₀} ‖localRep α x₀ y‖`. Hence a supNormK-Cauchy
sequence yields uniformly-Cauchy chart-representatives on each
`shrunkChart x₀`. -/

omit [ConnectedSpace X] in
/-- Per-chart-chart uniform bound from chartNormK: for y ∈ shrunkChart x₀,
|localRep (α - β) x₀ y| is bounded by `chartNormK (α - β) x₀ ≤ supNormK (α - β)`. -/
theorem norm_localRep_sub_le_supNormK
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {y : X} (hy : y ∈ shrunkChart (X := X) x₀) :
    ‖localRep α x₀ y - localRep β x₀ y‖ ≤ HolomorphicOneForms.supNormK (α - β) := by
  have hsub : α - β = α + (-β) := by rw [sub_eq_add_neg]
  have h_ap : localRep α x₀ y - localRep β x₀ y = localRep (α - β) x₀ y := by
    rw [hsub, localRep_add, localRep_neg]; ring
  rw [h_ap]
  exact HolomorphicOneForms.norm_localRep_le_supNormK (α - β) hx₀ hy

/-! ### Step 1b — `localRep α` on shrunkChart as a continuous map

Bundles `localRep α x₀` restricted to `shrunkChart x₀` as a `C(_, ℂ)`,
parallel to `localRepOnInnerShrunk` but on the outer shrinkage. -/

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem shrunkChart_compactSpace' (x₀ : X) :
    CompactSpace (shrunkChart (X := X) x₀) :=
  isCompact_iff_compactSpace.mp (shrunkChart_isCompact x₀)

/-- Bundled version of `localRep α x₀` on shrunkChart x₀. -/
noncomputable def localRepOnShrunkBcf
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : BoundedContinuousFunction (shrunkChart (X := X) x₀) ℂ := by
  letI := shrunkChart_compactSpace' (X := X) x₀
  exact BoundedContinuousFunction.mkOfCompact (localRepOnShrunk α x₀)

/-! ### Step 2 — bcf-Cauchy on shrunkChart from supNormK-Cauchy

The per-chart bcf distance is bounded by supNormK of the difference,
so a supNormK-Cauchy sequence has bcf-Cauchy chart restrictions. -/

omit [ConnectedSpace X] in
/-- Per-chart bcf-distance ≤ supNormK-distance for `α, β ∈ HOF X`. -/
theorem dist_localRepOnShrunkBcf_le_supNormK_sub
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    letI := shrunkChart_compactSpace' (X := X) x₀
    dist (localRepOnShrunkBcf α x₀) (localRepOnShrunkBcf β x₀) ≤
      HolomorphicOneForms.supNormK (α - β) := by
  letI := shrunkChart_compactSpace' (X := X) x₀
  refine (BoundedContinuousFunction.dist_le
    (HolomorphicOneForms.supNormK_nonneg _)).mpr ?_
  intro y
  have hy : (y : X) ∈ shrunkChart (X := X) x₀ := y.2
  simp only [localRepOnShrunkBcf, BoundedContinuousFunction.mkOfCompact_apply,
    localRepOnShrunk_apply _ hx₀, dist_eq_norm]
  exact norm_localRep_sub_le_supNormK α β hx₀ hy

/-! ### Step 3 — Pointwise CLM limit from supNormK Cauchy

For a supNormK-Cauchy sequence of sections, `α_n.toFun y` is Cauchy in
the complete space `T_y X →L[ℂ] ℂ` (CLM space, complete since ℂ is).
This gives a pointwise CLM limit `αLim.toFun y`. -/

omit [ConnectedSpace X] in
/-- For a supNormK-Cauchy sequence, the CLM value at each point is Cauchy.
This uses the identity `α.toFun y (e.symmL y 1) = localRep α x₀ y` and
the supNormK bound on localRep. -/
theorem cauchySeq_alpha_toFun_apply_symmL
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h_diff : ∀ ε > 0, ∃ N, ∀ n m, n ≥ N → m ≥ N →
      HolomorphicOneForms.supNormK (αs n - αs m) < ε)
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) {y : X}
    (hy : y ∈ shrunkChart (X := X) x₀) :
    CauchySeq (fun n : ℕ => localRep (αs n) x₀ y) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h_diff ε hε
  refine ⟨N, fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  calc ‖localRep (αs n) x₀ y - localRep (αs m) x₀ y‖
      ≤ HolomorphicOneForms.supNormK (αs n - αs m) :=
        norm_localRep_sub_le_supNormK (αs n) (αs m) hx₀ hy
    _ < ε := hN n m hn hm

/-! ### Step 3b — Finite diagonal: common bcf-convergent subsequence on chartCover

Given a bounded sequence of sections (supNormK ≤ 1), iterate per-chart
Arzelà (`isCompact_closure_image_inner_bcf` for `M = 1`) over the finite
`chartCover` to extract a single strict-mono `φ : ℕ → ℕ` such that for
every `x₀ ∈ chartCover` the bcf-image on `innerShrunkChart x₀`
converges to some limit. -/

omit [ConnectedSpace X] in
/-- List-indexed finite-diagonal extractor. By induction on `xs`, at
each cons step we sub-sample inside the compact closure of the range
of `mkOfCompact ∘ localRepOnInnerShrunk · y`. The outer strict-mono
preserves convergence in earlier charts (composing with a strict-mono
sequence preserves `Tendsto` at `atTop`). -/
private lemma exists_common_subseq_bcf_tendsto
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : ∀ n, HolomorphicOneForms.supNormK (αs n) ≤ 1)
    (xs : List X) (hxs : ∀ x ∈ xs, x ∈ (chartCover : Finset X)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ x ∈ xs,
        letI := innerShrunkChart_compactSpace (X := X) x
        ∃ g : BoundedContinuousFunction (innerShrunkChart (X := X) x) ℂ,
          Tendsto
            (fun n : ℕ => BoundedContinuousFunction.mkOfCompact
              (localRepOnInnerShrunk (αs (φ n)) x))
            atTop (𝓝 g) := by
  induction xs with
  | nil =>
    refine ⟨id, strictMono_id, fun x hx => ?_⟩
    exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    have hys : ∀ x ∈ ys, x ∈ (chartCover : Finset X) :=
      fun x hx => hxs x (List.mem_cons_of_mem _ hx)
    obtain ⟨φ₀, hφ₀, hφ₀_conv⟩ := ih hys
    have hy : y ∈ (chartCover : Finset X) := hxs y List.mem_cons_self
    letI := innerShrunkChart_compactSpace (X := X) y
    set K : Set (BoundedContinuousFunction (innerShrunkChart (X := X) y) ℂ) :=
      closure (Set.range
        (fun α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
            (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
            HolomorphicOneForms.supNormK α ≤ 1} =>
          BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 y)))
      with hK_def
    have hK : IsCompact K := isCompact_closure_image_inner_bcf 1 zero_le_one hy
    have hK_seq : IsSeqCompact K := hK.isSeqCompact
    set s : ℕ → BoundedContinuousFunction (innerShrunkChart (X := X) y) ℂ :=
      fun n => BoundedContinuousFunction.mkOfCompact
        (localRepOnInnerShrunk (αs (φ₀ n)) y)
      with hs_def
    have hs_in : ∀ n, s n ∈ K := by
      intro n
      refine subset_closure ?_
      exact ⟨⟨αs (φ₀ n), h (φ₀ n)⟩, rfl⟩
    obtain ⟨a, _haK, ψ, hψ, hψ_conv⟩ :=
      hK_seq.subseq_of_frequently_in (x := s)
        (Filter.Eventually.frequently (Filter.Eventually.of_forall hs_in))
    refine ⟨φ₀ ∘ ψ, hφ₀.comp hψ, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxys
    · refine ⟨a, ?_⟩
      simpa [Function.comp, s, hs_def] using hψ_conv
    · obtain ⟨g, hg⟩ := hφ₀_conv x hxys
      refine ⟨g, ?_⟩
      exact hg.comp hψ.tendsto_atTop

omit [ConnectedSpace X] in
/-- **Common bcf-convergent subsequence on `chartCover`.**
For any bounded sequence of sections (`supNormK (αs n) ≤ 1`), there is
a strict-mono subsequence `φ` such that on each chart `x₀ ∈ chartCover`
the bcf-image `mkOfCompact ∘ localRepOnInnerShrunk (αs (φ n)) x₀`
converges in `BCF(innerShrunkChart x₀, ℂ)`. -/
theorem exists_subseq_bcf_tendsto_on_chartCover
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : ∀ n, HolomorphicOneForms.supNormK (αs n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ x₀ ∈ (chartCover : Finset X),
        letI := innerShrunkChart_compactSpace (X := X) x₀
        ∃ g : BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ,
          Tendsto
            (fun n : ℕ => BoundedContinuousFunction.mkOfCompact
              (localRepOnInnerShrunk (αs (φ n)) x₀))
            atTop (𝓝 g) := by
  obtain ⟨φ, hφ, hconv⟩ := exists_common_subseq_bcf_tendsto αs h
    (chartCover : Finset X).toList (fun x hx => Finset.mem_toList.mp hx)
  refine ⟨φ, hφ, ?_⟩
  intro x₀ hx₀
  exact hconv x₀ (Finset.mem_toList.mpr hx₀)

/-! ### Step 3c — Chart-transition: bcf-Cauchy ⇒ supNormK-Cauchy

Combining the chart-transition supNormK bound
(`exists_supNormK_le_const_sup_inner`) with per-chart bcf-convergence
(which implies bcf-Cauchy, which dominates the inner-chart sSup),
a subsequence whose bcf-images converge on every chart is
supNormK-Cauchy. -/

omit [ConnectedSpace X] [Nonempty X] in
/-- **Inner sSup is bounded by bcf-distance.** For any two sections and
any chart x₀ ∈ chartCover, `sSup ‖localRep (α-β) x₀ ·‖` on
`innerShrunkChart x₀` is bounded above by the bcf-distance of their
`mkOfCompact ∘ localRepOnInnerShrunk` images. -/
private lemma sSup_innerShrunk_norm_sub_le_dist_bcf
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    sSup ((fun y : X => ‖localRep (α - β) x₀ y‖) '' innerShrunkChart (X := X) x₀) ≤
      dist
        (BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀))
        (BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk β x₀)) := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  set D : ℝ := dist
    (BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀))
    (BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk β x₀))
  have hD_nn : 0 ≤ D := dist_nonneg
  by_cases hne : Set.Nonempty (innerShrunkChart (X := X) x₀)
  · apply csSup_le
    · obtain ⟨y, hy⟩ := hne
      exact ⟨‖localRep (α - β) x₀ y‖, y, hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      -- ‖localRep (α - β) x₀ y‖ = ‖bcf_α ⟨y, hy⟩ - bcf_β ⟨y, hy⟩‖ ≤ D.
      show ‖localRep (α - β) x₀ y‖ ≤ D
      have h_sub : localRep (α - β) x₀ y = localRep α x₀ y - localRep β x₀ y := by
        have hsub : α - β = α + (-β) := by rw [sub_eq_add_neg]
        rw [hsub, localRep_add, localRep_neg]; ring
      rw [h_sub]
      calc ‖localRep α x₀ y - localRep β x₀ y‖
          = ‖(BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀))
              ⟨y, hy⟩ -
            (BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk β x₀))
              ⟨y, hy⟩‖ := by
              simp only [BoundedContinuousFunction.mkOfCompact_apply,
                localRepOnInnerShrunk_apply _ hx₀]
        _ = dist
              ((BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀))
                ⟨y, hy⟩)
              ((BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk β x₀))
                ⟨y, hy⟩) := (dist_eq_norm _ _).symm
        _ ≤ D := BoundedContinuousFunction.dist_coe_le_dist _
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne, Real.sSup_empty, hD_nn]

omit [ConnectedSpace X] in
/-- **bcf-convergent on every chart ⇒ supNormK-Cauchy.**
Given a strict-mono subsequence `φ` such that the bcf-images on each
`innerShrunkChart x₀` converge, the subsequence is supNormK-Cauchy. -/
theorem cauchy_supNormK_of_bcf_tendsto
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (φ : ℕ → ℕ)
    (h_chart_conv : ∀ x₀ ∈ (chartCover : Finset X),
      letI := innerShrunkChart_compactSpace (X := X) x₀
      ∃ g : BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ,
        Tendsto
          (fun n : ℕ => BoundedContinuousFunction.mkOfCompact
            (localRepOnInnerShrunk (αs (φ n)) x₀))
          atTop (𝓝 g)) :
    ∀ ε > 0, ∃ N, ∀ n m, n ≥ N → m ≥ N →
      HolomorphicOneForms.supNormK (αs (φ n) - αs (φ m)) < ε := by
  classical
  obtain ⟨M, hMnn, hM⟩ := exists_supNormK_le_const_sup_inner (X := X)
  intro ε hε
  -- Target per-chart bcf Cauchy threshold: δ = ε / (M + 1).
  set δ : ℝ := ε / (M + 1)
  have hM1_pos : 0 < M + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hM1_pos
  -- For each x₀ ∈ chartCover, extract Cauchy N_{x₀} at threshold δ.
  have h_each :
      ∀ x₀ ∈ (chartCover : Finset X), ∃ N_x, ∀ n m, n ≥ N_x → m ≥ N_x →
        letI := innerShrunkChart_compactSpace (X := X) x₀
        dist
          (BoundedContinuousFunction.mkOfCompact
            (localRepOnInnerShrunk (αs (φ n)) x₀))
          (BoundedContinuousFunction.mkOfCompact
            (localRepOnInnerShrunk (αs (φ m)) x₀)) < δ := by
    intro x₀ hx₀
    letI := innerShrunkChart_compactSpace (X := X) x₀
    obtain ⟨g, hg⟩ := h_chart_conv x₀ hx₀
    -- Convergent ⇒ Cauchy.
    have hCauchy : CauchySeq
        (fun n : ℕ => BoundedContinuousFunction.mkOfCompact
          (localRepOnInnerShrunk (αs (φ n)) x₀)) := hg.cauchySeq
    rw [Metric.cauchySeq_iff] at hCauchy
    obtain ⟨N_x, hN_x⟩ := hCauchy δ hδ_pos
    exact ⟨N_x, fun n m hn hm => hN_x n hn m hm⟩
  -- Pick a common N via Finset.sup' over chartCover (or 0 if empty — but chartCover is nonempty).
  choose N_fn hN_fn using h_each
  set N : ℕ := (chartCover : Finset X).attach.sup fun x => N_fn x.1 x.2 with hN_def
  refine ⟨N, fun n m hn hm => ?_⟩
  -- Bound supNormK (αs(φ n) - αs(φ m)) via chart transition.
  have h_bound := hM (αs (φ n) - αs (φ m))
  -- For each x₀ ∈ chartCover, bound the inner sSup by δ.
  have h_inner_le : ∀ x₀ ∈ (chartCover : Finset X),
      sSup ((fun y : X => ‖localRep (αs (φ n) - αs (φ m)) x₀ y‖) ''
        innerShrunkChart (X := X) x₀) ≤ δ := by
    intro x₀ hx₀
    have hn' : n ≥ N_fn x₀ hx₀ :=
      le_trans (Finset.le_sup (f := fun x : {x // x ∈ (chartCover : Finset X)} =>
        N_fn x.1 x.2) (Finset.mem_attach _ ⟨x₀, hx₀⟩)) hn
    have hm' : m ≥ N_fn x₀ hx₀ :=
      le_trans (Finset.le_sup (f := fun x : {x // x ∈ (chartCover : Finset X)} =>
        N_fn x.1 x.2) (Finset.mem_attach _ ⟨x₀, hx₀⟩)) hm
    have h_dist_lt := hN_fn x₀ hx₀ n m hn' hm'
    have h_le_dist := sSup_innerShrunk_norm_sub_le_dist_bcf
      (αs (φ n)) (αs (φ m)) hx₀
    linarith
  -- sup' over chartCover ≤ δ.
  have h_sup'_le :
      (chartCover : Finset X).sup' chartCover_nonempty
        (fun x₀' : X =>
          sSup ((fun y : X => ‖localRep (αs (φ n) - αs (φ m)) x₀' y‖) ''
            innerShrunkChart (X := X) x₀')) ≤ δ := by
    rw [Finset.sup'_le_iff]
    intro x₀ hx₀
    exact h_inner_le x₀ hx₀
  -- Combine: supNormK ≤ M * δ ≤ M * ε / (M+1) < ε.
  have h_step1 : HolomorphicOneForms.supNormK (αs (φ n) - αs (φ m)) ≤ M * δ :=
    le_trans h_bound (mul_le_mul_of_nonneg_left h_sup'_le hMnn)
  have h_step2 : M * δ < ε := by
    have h_sum : M * δ + δ = ε := by
      show M * (ε / (M + 1)) + ε / (M + 1) = ε
      field_simp
    linarith
  exact lt_of_le_of_lt h_step1 h_step2

/-! ### Step 3d — Coordinate identity and pointwise CLM Cauchy

On the base set of the trivialization at `x₀`, the section's CLM value
`α.toFun y` is `(localRep α x₀ y) • φ` where
`φ := e.continuousLinearEquivAt ℂ y hy`. This reduces CauchySeq in CLM
norm to CauchySeq in ℂ, which is already supplied by
`cauchySeq_alpha_toFun_apply_symmL`. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- **Coordinate identity.** For `y ∈ (trivializationAt … x₀).baseSet`,
`α.toFun y` equals `(localRep α x₀ y) • φ` where `φ` is the CLE
`T_y X ≃L[ℂ] ℂ` from the trivialization. -/
theorem toFun_eq_localRep_smul
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X)
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    α.toFun y = (localRep α x₀ y) •
      (e.continuousLinearEquivAt ℂ y hy :
        TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he
  set φ := e.continuousLinearEquivAt ℂ y hy with hφ
  apply ContinuousLinearMap.ext
  intro v
  -- Goal: α.toFun y v = ((localRep α x₀ y) • (φ : T_y X →L[ℂ] ℂ)) v
  -- RHS: (localRep α x₀ y) • (φ v) = localRep α x₀ y * φ v (in ℂ)
  change α.toFun y v = (localRep α x₀ y) • (φ v)
  -- Strategy: rewrite v as φ.symm (φ v); use ℂ-linearity of α.toFun y ∘ φ.symm.
  have hv_eq : v = (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) (φ v) :=
    (ContinuousLinearEquiv.symm_apply_apply φ v).symm
  -- Write (φ v : ℂ) = (φ v) • (1 : ℂ) and push through φ.symm.
  have hφv_smul : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) (φ v) =
      (φ v) • ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1) := by
    have h1 : (φ v : ℂ) = (φ v) • (1 : ℂ) := by
      rw [smul_eq_mul, mul_one]
    conv_lhs => rw [h1]
    exact (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y).map_smul (φ v) 1
  -- Identify φ.symm 1 with e.symmL ℂ y 1.
  have h_symmL : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = e.symmL ℂ y :=
    Trivialization.symm_continuousLinearEquivAt_eq' e hy
  -- Chain: α.toFun y v = α.toFun y ((φ v) • (e.symmL ℂ y 1))
  --                   = (φ v) • (α.toFun y (e.symmL ℂ y 1))
  --                   = (φ v) • localRep α x₀ y
  --                   = localRep α x₀ y • (φ v)  (commutative)
  calc α.toFun y v
      = α.toFun y ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) (φ v)) := by rw [← hv_eq]
    _ = α.toFun y ((φ v) • ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1)) := by
          rw [hφv_smul]
    _ = (φ v) • (α.toFun y ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1)) :=
          (α.toFun y).map_smul (φ v) _
    _ = (φ v) • (α.toFun y (e.symmL ℂ y 1)) := by rw [h_symmL]
    _ = (φ v) • (localRep α x₀ y) := rfl
    _ = (localRep α x₀ y) • (φ v) := by rw [smul_eq_mul, smul_eq_mul]; ring

omit [ConnectedSpace X] in
/-- **Pointwise CLM Cauchy.** For a supNormK-Cauchy sequence and
`y ∈ shrunkChart x₀` (some `x₀ ∈ chartCover`), the CLM value
`(αs n).toFun y` is Cauchy in `T_y X →L[ℂ] ℂ`.

Proof: the CLM `L : ℂ →L[ℂ] (T_y X →L[ℂ] ℂ), c ↦ c • φ` is Lipschitz
(CLMs are Lipschitz). Since `(αs n).toFun y = L (localRep (αs n) x₀ y)`
and `localRep (αs n) x₀ y` is Cauchy in ℂ, the image under `L` is
Cauchy in the CLM space. -/
theorem cauchySeq_toFun_of_supNormK_cauchy
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h_diff : ∀ ε > 0, ∃ N, ∀ n m, n ≥ N → m ≥ N →
      HolomorphicOneForms.supNormK (αs n - αs m) < ε)
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {y : X} (hy : y ∈ shrunkChart (X := X) x₀) :
    CauchySeq (fun n : ℕ => (αs n).toFun y) := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  have hy_baseSet : y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact shrunkChart_subset_source x₀ hx₀ hy
  set φ := e.continuousLinearEquivAt ℂ y hy_baseSet
  -- c ↦ c • φ as a CLM.
  set L : ℂ →L[ℂ] (TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight
      (φ : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ)
  -- Identity: (αs n).toFun y = L (localRep (αs n) x₀ y)
  have h_id : ∀ n, (αs n).toFun y = L (localRep (αs n) x₀ y) := by
    intro n
    have := toFun_eq_localRep_smul (αs n) x₀ y hy_baseSet
    simpa [L, ContinuousLinearMap.smulRight_apply] using this
  -- Cauchy in ℂ of localRep (αs n) x₀ y.
  have h_cauchy_ℂ : CauchySeq (fun n : ℕ => localRep (αs n) x₀ y) :=
    cauchySeq_alpha_toFun_apply_symmL αs h_diff hx₀ hy
  -- Transport via L (uniformly continuous).
  have h_unif : UniformContinuous L := L.uniformContinuous
  have h_cauchy_L : CauchySeq (fun n : ℕ => L (localRep (αs n) x₀ y)) :=
    h_unif.comp_cauchySeq h_cauchy_ℂ
  -- Rewrite using h_id.
  have h_fun_eq : (fun n : ℕ => (αs n).toFun y) =
      (fun n : ℕ => L (localRep (αs n) x₀ y)) := by
    funext n; exact h_id n
  rw [h_fun_eq]
  exact h_cauchy_L

/-! ### Step 4 — Pointwise CLM limit

Packages Step 5c's CauchySeq-per-point fact with completeness of the
CLM space to extract a pointwise limit function. Provides the local
normed instances on `TangentSpace 𝓘(ℂ, ℂ) y` (intentionally
non-reducible in Mathlib — `IsManifold/Basic.lean:1037`) via
`inferInstanceAs (NormedAddCommGroup ℂ)` / etc., relying on the defeq
`TangentSpace 𝓘(ℂ, ℂ) y = ℂ`. -/

omit [ConnectedSpace X] in
/-- Pointwise CLM limit of a supNormK-Cauchy sequence of sections. -/
theorem exists_toFun_limit
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h_diff : ∀ ε > 0, ∃ N, ∀ n m, n ≥ N → m ≥ N →
      HolomorphicOneForms.supNormK (αs n - αs m) < ε) :
    ∃ L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y,
      ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)) := by
  have h_pw_cauchy : ∀ y : X, CauchySeq (fun n : ℕ => (αs n).toFun y) := by
    intro y
    have hmem : y ∈ (Set.univ : Set X) := Set.mem_univ _
    rw [← iUnion_shrunkChart_chartCover_eq (X := X)] at hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x₀, hx₀mem, hy_in⟩ := hmem
    exact cauchySeq_toFun_of_supNormK_cauchy αs h_diff hx₀mem hy_in
  have h_pw_limit : ∀ y : X,
      ∃ L : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y,
        Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 L) := by
    intro y
    -- Pick x₀ ∈ chartCover with y ∈ shrunkChart x₀; use the chart CLE
    -- φ : TangentSpace y ≃L[ℂ] ℂ to transport the Cauchy sequence
    -- into `ℂ →L[ℂ] ℂ` (which is a complete normed space).
    have hmem : y ∈ (Set.univ : Set X) := Set.mem_univ _
    rw [← iUnion_shrunkChart_chartCover_eq (X := X)] at hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x₀, hx₀mem, hy_in⟩ := hmem
    set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he
    have hy_baseSet : y ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact shrunkChart_subset_source x₀ hx₀mem hy_in
    set φ := e.continuousLinearEquivAt ℂ y hy_baseSet with hφ
    -- CLE between CLM spaces: arrowCongr φ (refl ℂ) sends L ↦ L.comp φ.symm.
    let transport : (TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
        ≃L[ℂ] (ℂ →L[ℂ] ℂ) :=
      φ.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)
    -- Transport Cauchy into the complete `ℂ →L[ℂ] ℂ` space via the
    -- underlying CLM (which is uniformly continuous).
    have h_s_cauchy : CauchySeq (fun n : ℕ => transport ((αs n).toFun y)) :=
      transport.toContinuousLinearMap.uniformContinuous.comp_cauchySeq (h_pw_cauchy y)
    obtain ⟨L', hL'⟩ := cauchySeq_tendsto_of_complete h_s_cauchy
    refine ⟨transport.symm L', ?_⟩
    -- Transport the limit back via transport.symm (continuous ⇒ Tendsto).
    have h_back : Tendsto (fun n : ℕ => transport.symm (transport ((αs n).toFun y)))
        atTop (𝓝 (transport.symm L')) :=
      (transport.symm.continuous.tendsto L').comp hL'
    have h_round_trip : (fun n : ℕ => transport.symm (transport ((αs n).toFun y))) =
        fun n : ℕ => (αs n).toFun y := by
      funext n; exact transport.symm_apply_apply _
    rw [h_round_trip] at h_back
    exact h_back
  choose L hL using h_pw_limit
  exact ⟨L, hL⟩


/-! ### Step 6 helper — pointwise `localRep` Tendsto

From pointwise CLM Tendsto of `(αs n).toFun y`, evaluation at
`e.symmL ℂ y 1` gives pointwise scalar Tendsto of `localRep`. Bridges
pointwise CLM convergence (Step 5c/5d-limit) to the scalar chart-rep
used by `supNormK`/`chartNormK`. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Pointwise Tendsto of `localReps` from pointwise CLM Tendsto by
continuity of evaluation at `e.symmL ℂ y 1`. -/
theorem localRep_tendsto_of_toFun_tendsto
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (αLim_toFun : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (αLim_toFun y)))
    (x₀ y : X) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    Tendsto (fun n : ℕ => localRep (αs n) x₀ y) atTop
      (𝓝 (αLim_toFun y (e.symmL ℂ y 1))) := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  -- evaluation at a fixed vector is continuous via ContinuousEvalConst
  have h_eval : Continuous
      (fun L : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y =>
        L (e.symmL ℂ y 1)) :=
    continuous_eval_const _
  exact (h_eval.tendsto _).comp (hL y)

/-! ### Step 6a — norm bound on the pointwise limit

Pointwise in each chart, if the (αs n) are bounded by 1 in supNormK
and converge pointwise in CLM to L, then the chart-representative of
L is bounded by 1. This packages the norm-lsc argument at the level
of `localRep`-style scalar evaluation, without yet needing L to be a
`ContMDiffSection`. -/

omit [ConnectedSpace X] in
/-- **Step 6a bound**: for a bounded supNormK sequence with pointwise
CLM limit `L y`, each scalar `‖L y (e.symmL ℂ y 1)‖ ≤ 1` at
`y ∈ shrunkChart x₀`. -/
theorem norm_limit_localRep_le_one
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : ∀ n, HolomorphicOneForms.supNormK (αs n) ≤ 1)
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {y : X} (hy : y ∈ shrunkChart (X := X) x₀) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    ‖L y (e.symmL ℂ y 1)‖ ≤ 1 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  have h_tendsto : Tendsto (fun n : ℕ => localRep (αs n) x₀ y) atTop
      (𝓝 (L y (e.symmL ℂ y 1))) :=
    localRep_tendsto_of_toFun_tendsto αs L hL x₀ y
  have h_bounded : ∀ n : ℕ, ‖localRep (αs n) x₀ y‖ ≤ 1 := fun n =>
    le_trans (HolomorphicOneForms.norm_localRep_le_supNormK (αs n) hx₀ hy) (h n)
  exact le_of_tendsto h_tendsto.norm (Filter.Eventually.of_forall h_bounded)

/-! ### Step 6b — bound on `‖αs n - limit‖` at scalar level

Given a supNormK-Cauchy sequence `αs` with pointwise CLM limit `L`,
for every ε > 0 there is `N` such that for all `n ≥ N` and every
chart / point, the scalar diff `‖localRep (αs n) x₀ y - L y (e.symmL y 1)‖ ≤ ε`.
This is the scalar analog of `supNormK (αs n - αLim) ≤ ε`, proven
without yet packaging L as a ContMDiffSection. -/

omit [ConnectedSpace X] in
/-- Scalar-level convergence of `localRep (αs n) x₀ y` to
`L y (e.symmL ℂ y 1)`, uniformly over `(x₀ ∈ chartCover, y ∈ shrunkChart x₀)`. -/
theorem norm_localRep_sub_limit_le
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ n m, n ≥ N → m ≥ N →
      HolomorphicOneForms.supNormK (αs n - αs m) < ε)
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n, n ≥ N → ∀ (x₀ : X), x₀ ∈ (chartCover : Finset X) →
      ∀ (y : X), y ∈ shrunkChart (X := X) x₀ →
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      ‖localRep (αs n) x₀ y - L y (e.symmL ℂ y 1)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := h_cauchy ε hε
  refine ⟨N, fun n hn x₀ hx₀ y hy => ?_⟩
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  -- As m → ∞, localRep (αs m) x₀ y → L y (e.symmL ℂ y 1).
  have h_m_tendsto : Tendsto (fun m : ℕ => localRep (αs m) x₀ y) atTop
      (𝓝 (L y (e.symmL ℂ y 1))) :=
    localRep_tendsto_of_toFun_tendsto αs L hL x₀ y
  -- Hence the diff (αs n) - (αs m) → (αs n) - L as m → ∞.
  have h_sub_tendsto :
      Tendsto (fun m : ℕ =>
        localRep (αs n) x₀ y - localRep (αs m) x₀ y) atTop
          (𝓝 (localRep (αs n) x₀ y - L y (e.symmL ℂ y 1))) :=
    tendsto_const_nhds.sub h_m_tendsto
  -- For m ≥ N, the diff is bounded by ε.
  have h_eventually : ∀ᶠ m in atTop,
      ‖localRep (αs n) x₀ y - localRep (αs m) x₀ y‖ ≤ ε := by
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    have h_sub_eq : localRep (αs n) x₀ y - localRep (αs m) x₀ y =
        localRep (αs n - αs m) x₀ y := by
      have hsub : αs n - αs m = αs n + (-αs m) := sub_eq_add_neg _ _
      rw [hsub, localRep_add, localRep_neg]; ring
    rw [h_sub_eq]
    exact le_of_lt (lt_of_le_of_lt
      (HolomorphicOneForms.norm_localRep_le_supNormK (αs n - αs m) hx₀ hy)
      (hN n m hn hm))
  exact le_of_tendsto h_sub_tendsto.norm h_eventually

/-! ### Step 5d substep 1 — chart-pullback locally uniform convergence

The bridge from bcf-convergence on `innerShrunkChart x₀` (compact) to
`TendstoLocallyUniformlyOn` of the chart pullbacks on
`chart '' innerChartOpen x₀` (open ⊆ chart target). Path 2's step 1. -/

omit [ConnectedSpace X] [Nonempty X] in
/-- **Limit identification.** The bcf-limit `g` on `innerShrunkChart x₀`
agrees with `y ↦ L y (e.symmL ℂ y 1)` via pointwise uniqueness of limits. -/
private lemma bcf_limit_eq_L_eval
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (g : letI := innerShrunkChart_compactSpace (X := X) x₀
      BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ)
    (hg : letI := innerShrunkChart_compactSpace (X := X) x₀
      Tendsto (fun n : ℕ =>
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀))
        atTop (𝓝 g))
    (y : innerShrunkChart (X := X) x₀) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    g y = L y.val (e.symmL ℂ y.val 1) := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  -- bcf Tendsto → pointwise TendstoUniformly → pointwise Tendsto.
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly] at hg
  have hg_pw : Tendsto (fun n : ℕ =>
      BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀) y)
      atTop (𝓝 (g y)) :=
    hg.tendsto_at y
  -- LHS simplifies to localRep (αs n) x₀ y.val.
  have h_simp : ∀ n, BoundedContinuousFunction.mkOfCompact
      (localRepOnInnerShrunk (αs n) x₀) y = localRep (αs n) x₀ y.val := by
    intro n
    simp only [BoundedContinuousFunction.mkOfCompact_apply,
      localRepOnInnerShrunk_apply _ hx₀]
  -- Rewrite hg_pw to get Tendsto of `localRep (αs n) x₀ y.val`.
  rw [show (fun n : ℕ => BoundedContinuousFunction.mkOfCompact
        (localRepOnInnerShrunk (αs n) x₀) y) =
      fun n : ℕ => localRep (αs n) x₀ y.val from funext h_simp] at hg_pw
  -- Other Tendsto: from `localRep_tendsto_of_toFun_tendsto`.
  have h_L_tendsto : Tendsto (fun n : ℕ => localRep (αs n) x₀ y.val) atTop
      (𝓝 (L y.val (e.symmL ℂ y.val 1))) :=
    localRep_tendsto_of_toFun_tendsto αs L hL x₀ y.val
  -- Uniqueness of limit in ℂ.
  exact tendsto_nhds_unique hg_pw h_L_tendsto

omit [ConnectedSpace X] [Nonempty X] in
/-- **Substep 1 of Path 2.** Chart pullbacks of `localRep` converge
locally uniformly on `chart '' innerChartOpen x₀` to the pullback of
`y ↦ L y (e.symmL ℂ y 1)`, assuming bcf-convergence on
`innerShrunkChart x₀` and pointwise CLM Tendsto. -/
theorem tendstoLocallyUniformlyOn_pullback_on_innerChartOpen
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (g : letI := innerShrunkChart_compactSpace (X := X) x₀
      BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ)
    (hg : letI := innerShrunkChart_compactSpace (X := X) x₀
      Tendsto (fun n : ℕ =>
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀))
        atTop (𝓝 g)) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    TendstoLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => localRep (αs n) x₀ ((chartAt ℂ x₀).symm z))
      (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
      atTop
      ((chartAt ℂ x₀) '' innerChartOpen (X := X) x₀) := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  -- Step 1: Identify the subtype limit via uniqueness.
  have h_id : (⇑g : innerShrunkChart (X := X) x₀ → ℂ) =
      fun y : innerShrunkChart (X := X) x₀ => L y.val (e.symmL ℂ y.val 1) := by
    funext y; exact bcf_limit_eq_L_eval αs L hL hx₀ g hg y
  -- Step 2: bcf-Tendsto ⇒ TendstoUniformly on subtype.
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly] at hg
  -- Step 3: Simplify LHS of the subtype convergence to `localRep (αs n) x₀ y.val`.
  have h_simp : ∀ n : ℕ, (⇑(BoundedContinuousFunction.mkOfCompact
      (localRepOnInnerShrunk (αs n) x₀)) : innerShrunkChart (X := X) x₀ → ℂ) =
      fun y : innerShrunkChart (X := X) x₀ => localRep (αs n) x₀ y.val := by
    intro n; funext y
    simp only [BoundedContinuousFunction.mkOfCompact_apply,
      localRepOnInnerShrunk_apply _ hx₀]
  have hg_sub : TendstoUniformly
      (fun n : ℕ => fun y : innerShrunkChart (X := X) x₀ => localRep (αs n) x₀ y.val)
      (fun y : innerShrunkChart (X := X) x₀ => L y.val (e.symmL ℂ y.val 1))
      atTop := by
    have := hg
    rw [show (fun n : ℕ => ⇑(BoundedContinuousFunction.mkOfCompact
          (localRepOnInnerShrunk (αs n) x₀))) =
        fun n : ℕ => fun y : innerShrunkChart (X := X) x₀ =>
          localRep (αs n) x₀ y.val from funext h_simp] at this
    rw [h_id] at this
    exact this
  -- Step 4: Subtype-TendstoUniformly ⇒ TendstoUniformlyOn the set innerShrunkChart.
  have hUnifOn_shrunk : TendstoUniformlyOn
      (fun n : ℕ => fun y : X => localRep (αs n) x₀ y)
      (fun y : X => L y (e.symmL ℂ y 1))
      atTop
      (innerShrunkChart (X := X) x₀) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    exact hg_sub
  -- Step 5: Restrict to innerChartOpen ⊆ innerShrunkChart.
  have hUnifOn_inner : TendstoUniformlyOn
      (fun n : ℕ => fun y : X => localRep (αs n) x₀ y)
      (fun y : X => L y (e.symmL ℂ y 1))
      atTop
      (innerChartOpen (X := X) x₀) :=
    hUnifOn_shrunk.mono (subset_closure)
  -- Step 6: Push through chart.symm via TendstoUniformlyOn.comp + mono.
  have hUnifOn_preimage := hUnifOn_inner.comp (chartAt ℂ x₀).symm
  have h_img_subset :
      (chartAt ℂ x₀) '' innerChartOpen (X := X) x₀ ⊆
        (chartAt ℂ x₀).symm ⁻¹' (innerChartOpen (X := X) x₀) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy_src : y ∈ (chartAt ℂ x₀).source :=
      innerChartOpen_subset_source x₀ hx₀ hy
    rw [Set.mem_preimage, (chartAt ℂ x₀).left_inv hy_src]
    exact hy
  have hUnifOn_img := hUnifOn_preimage.mono h_img_subset
  -- Step 7: Uniform on open ⇒ locally uniform.
  exact hUnifOn_img.tendstoLocallyUniformlyOn

omit [ConnectedSpace X] [Nonempty X] in
/-- **Substep 2 of Path 2.** The chart-pullback of `y ↦ L y (e.symmL y 1)`
is analytic on `chart '' innerChartOpen x₀` — feeds substep 3. -/
theorem analyticOn_limit_pullback_inner
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (g : letI := innerShrunkChart_compactSpace (X := X) x₀
      BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ)
    (hg : letI := innerShrunkChart_compactSpace (X := X) x₀
      Tendsto (fun n : ℕ =>
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀))
        atTop (𝓝 g)) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    AnalyticOn ℂ
      (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
      ((chartAt ℂ x₀) '' innerChartOpen (X := X) x₀) :=
  analyticOn_of_pullback_tendsto_locally_uniformly_inner αs hx₀ _
    (tendstoLocallyUniformlyOn_pullback_on_innerChartOpen αs L hL hx₀ g hg)

omit [ConnectedSpace X] [Nonempty X] in
/-- **Substep 3 of Path 2.** Reverse of `localRep_analyticOn_chartTarget`:
analytic pullback on `chart '' innerChartOpen x₀` ⇒ `ContMDiffOn ω`
of `fun y => L y (e.symmL ℂ y 1)` on `innerChartOpen x₀`. -/
theorem contMDiffOn_limit_inner
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (g : letI := innerShrunkChart_compactSpace (X := X) x₀
      BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ)
    (hg : letI := innerShrunkChart_compactSpace (X := X) x₀
      Tendsto (fun n : ℕ =>
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀))
        atTop (𝓝 g)) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1))
      (innerChartOpen (X := X) x₀) := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  -- Substep 2: AnalyticOn of the chart pullback.
  have h_analytic := analyticOn_limit_pullback_inner αs L hL hx₀ g hg
  -- Package: use `contMDiffOn_iff_of_subset_source'` with x := x₀, y := 0.
  -- Need: innerChartOpen ⊆ extChartAt 𝓘(ℂ, ℂ) x₀ .source = chartAt ℂ x₀ .source.
  have hs : innerChartOpen (X := X) x₀ ⊆ (extChartAt 𝓘(ℂ, ℂ) x₀).source := by
    have : (extChartAt 𝓘(ℂ, ℂ) x₀).source = (chartAt ℂ x₀).source := by simp [extChartAt]
    rw [this]; exact innerChartOpen_subset_source x₀ hx₀
  have h2s : Set.MapsTo (fun y : X => L y (e.symmL ℂ y 1))
      (innerChartOpen (X := X) x₀) (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source := by
    have h_src : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source = Set.univ := by simp [extChartAt]
    rw [h_src]
    exact fun _ _ => Set.mem_univ _
  rw [contMDiffOn_iff_of_subset_source' hs h2s]
  -- Goal: ContDiffOn ℂ ω (extChartAt 0 ∘ f ∘ (extChartAt x₀).symm)
  --                    (extChartAt x₀ '' innerChartOpen x₀)
  -- extChartAt 0 = id, extChartAt x₀.symm = chart.symm, extChartAt x₀ '' = chart ''.
  have h_set_eq : extChartAt 𝓘(ℂ, ℂ) x₀ '' innerChartOpen (X := X) x₀ =
      (chartAt ℂ x₀) '' innerChartOpen (X := X) x₀ := by
    simp [extChartAt]
  have h_fun_eq : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ) ∘
      (fun y : X => L y (e.symmL ℂ y 1)) ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm) =
      fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1) := by
    funext z
    simp [extChartAt, Function.comp_def]
  rw [h_set_eq, h_fun_eq]
  -- Now: ContDiffOn ℂ ω (chart pullback of L) (chart '' innerChartOpen x₀).
  -- Use `contDiffOn_omega_iff_analyticOn.mpr` — open set has UniqueDiffOn.
  exact (contDiffOn_omega_iff_analyticOn
    (isOpen_chart_image_innerChartOpen x₀ hx₀).uniqueDiffOn).mpr h_analytic

omit [ConnectedSpace X] [Nonempty X] in
/-- **Substep 4 of Path 2.** The pointwise CLM limit, packaged as a
bundle-section, is `ContMDiff ω` on each `innerChartOpen x₀` for
`x₀ ∈ chartCover`.

Uses `toFun_eq_localRep_smul` to express `L y = (scalar) • (CLE)` and
combines smoothness of the scalar (substep 3) with smoothness of the
frame via `clm_bundle_apply`-style arguments. Concretely, we lift via
`Trivialization.contMDiffAt_section_iff` on the Hom bundle, reducing
section smoothness to smoothness of the `inCoordinates` CLM-valued
function. For `Trivial X ℂ`-target, `inCoordinates` collapses to
`c(y) • (ContinuousLinearMap.id ℂ ℂ)` where `c(y) = L y (e.symmL y 1)`. -/
theorem contMDiffOn_totalSpaceMk_L_inner
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hL : ∀ y : X, Tendsto (fun n : ℕ => (αs n).toFun y) atTop (𝓝 (L y)))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (g : letI := innerShrunkChart_compactSpace (X := X) x₀
      BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ)
    (hg : letI := innerShrunkChart_compactSpace (X := X) x₀
      Tendsto (fun n : ℕ =>
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀))
        atTop (𝓝 g)) :
    ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : X => TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        y (L y))
      (innerChartOpen (X := X) x₀) := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he_def
  -- Get scalar smoothness from substep 3.
  have h_scalar : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1))
      (innerChartOpen (X := X) x₀) :=
    contMDiffOn_limit_inner αs L hL hx₀ g hg
  -- Use the Hom-bundle trivialization centered at our chart center x₀.
  set eHom := trivializationAt (ℂ →L[ℂ] ℂ)
    (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) x₀ with heHom_def
  -- innerChartOpen x₀ ⊆ eHom.baseSet (= Tangent baseSet ∩ Trivial baseSet = chart source ∩ univ).
  have h_inner_sub_hom : innerChartOpen (X := X) x₀ ⊆ eHom.baseSet := by
    intro y hy
    rw [heHom_def, hom_trivializationAt_baseSet]
    refine ⟨?_tangent, Set.mem_univ _⟩
    rw [TangentBundle.trivializationAt_baseSet]
    exact innerChartOpen_subset_source x₀ hx₀ hy
  -- Reduce section smoothness to coordinate-function smoothness via the iff.
  intro y₀ hy₀
  rw [Trivialization.contMDiffWithinAt_section _ (h_inner_sub_hom hy₀)]
  -- Goal: ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
  --   (fun x => (eHom ⟨x, L x⟩).2) (innerChartOpen x₀) y₀
  -- By hom_trivializationAt_apply, (eHom ⟨x, L x⟩).2 = inCoordinates ... x₀ x x₀ x (L x).
  -- Via `inCoordinates` definition + `Bundle.Trivial.continuousLinearMapAt_trivialization = id` +
  -- `id.comp f = f`, this simplifies to `(L x).comp (e.symmL ℂ x) : ℂ →L[ℂ] ℂ`.
  -- By 1-dim scalar action, this equals `(L x (e.symmL ℂ x 1)) • (ContinuousLinearMap.id ℂ ℂ)`.
  -- Smoothness then follows from substep 3 + ContMDiffWithinAt.smul const.
  have h_simpl : ∀ y ∈ innerChartOpen (X := X) x₀,
      (eHom (TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (L y))).2 =
        (L y (e.symmL ℂ y 1)) • (ContinuousLinearMap.id ℂ ℂ) := by
    intro y hy
    rw [heHom_def]
    -- Unfold via hom_trivializationAt_apply.
    rw [hom_trivializationAt_apply]
    -- Now LHS: inCoordinates ℂ TangentSpace ℂ (Trivial X ℂ) x₀ y x₀ y (L y).
    -- Prove pointwise equality directly.
    apply ContinuousLinearMap.ext
    intro v
    -- Unfold inCoordinates and simplify Trivial's continuousLinearMapAt via rw.
    have h_triv_id : Trivialization.continuousLinearMapAt ℂ
        (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀) y = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ X ℂ y
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp',
               Function.comp_apply, h_triv_id, ContinuousLinearMap.id_apply,
               ContinuousLinearMap.smul_apply]
    -- Goal: L y (e.symmL y v) = (L y (e.symmL y 1)) • v.
    have hv : (v : ℂ) = v • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [hv, (e.symmL ℂ y).map_smul]
    rw [(L y).map_smul]
    simp only [smul_eq_mul]
    ring
  -- Use congr_of_eventuallyEq via ContMDiffWithinAt.congr with the h_simpl equality.
  have h_smul_smooth : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y : X => (L y (e.symmL ℂ y 1)) • (ContinuousLinearMap.id ℂ ℂ))
      (innerChartOpen (X := X) x₀) y₀ :=
    (h_scalar y₀ hy₀).smul contMDiffWithinAt_const
  exact h_smul_smooth.congr (fun y hy => h_simpl y hy) (h_simpl y₀ hy₀)

/-! ### Status

The substeps of the completeness argument are proven in this file and its
siblings:

- **Per-chart uniform Cauchy / limit** (`localRep` on `shrunkChart x₀`):
  `cauchySeq_alpha_toFun_apply_symmL`, `exists_toFun_limit`.
- **Pointwise CLM limit** (1-dim tangent reduction via
  `toFun_eq_localRep_smul`): `exists_toFun_limit`.
- **Smoothness of the limit** (chart-wise analytic ⇒ `ContMDiffSection ω`):
  `contMDiffOn_totalSpaceMk_L_inner`, assembled over the finite cover in
  `exists_convergent_subseq_of_bounded` (`Montel.lean`).
- **Convergence in supNormK** and **compactness of the closed ball**:
  `norm_localRep_sub_limit_le` and `closedBall_isCompact` (`Montel.lean`).

The full Montel route to `FiniteDimensional ℂ (HolomorphicOneForms X)` is
complete and axiom-clean. -/

end Jacobians.Montel
