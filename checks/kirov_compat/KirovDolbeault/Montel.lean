import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Seminorm
import KirovDolbeault.Genus
import KirovDolbeault.Montel.Cover
import KirovDolbeault.Montel.LocalRep
import KirovDolbeault.Montel.ChartNorm
import KirovDolbeault.Montel.SupNorm
import KirovDolbeault.Montel.Compactness
import KirovDolbeault.Montel.ChartTransition
import KirovDolbeault.Montel.Complete

/-!
# Montel path to finite-dimensionality of `HolomorphicOneForms`

**Goal**: prove `FiniteDimensional ℂ (HolomorphicOneForms X)` for X a
compact connected complex 1-manifold via the classical Montel /
compactness route (Ahlfors–Sario, Rudin).


## Classical textbook approach (Ahlfors–Sario Ch II §5)

1. **Finite atlas.** X compact ⇒ finite open cover by chart domains.
2. **Local representative.** In each chart, α = `f(z) dz` with `f` holomorphic.
3. **Sup-norm.** `‖α‖ := max_j sup_{z ∈ K_j} |f_j(z)|` where `K_j ⊂ V_j` is
   a compact shrinkage.
4. **Cauchy estimates.** Bound derivatives ⇒ equicontinuity.
5. **Arzelà–Ascoli.** Bounded + equicontinuous ⇒ relatively compact.
6. **Riesz.** Compact closed ball ⇒ finite-dimensional.

## File layout

Step 1 (**COMPLETE** — this is the norm on HOF X) is split across
four submodules:

- `Jacobians/Montel/Cover.lean` — finite chart cover + compact shrinking.
- `Jacobians/Montel/LocalRep.lean` — chart-local scalar representative
  `localRep` + continuity + vector ops.
- `Jacobians/Montel/ChartNorm.lean` — per-chart bounded sup-norm
  `chartNormK` + triangle + homogeneity.
- `Jacobians/Montel/SupNorm.lean` — assembled sup-norm `supNormK` +
  positive-definiteness.

This root file packages them into `NormedAddCommGroup` / `NormedSpace ℂ`
structures and derives `FiniteDimensional` from `closedBall_isCompact`
(Steps 2–6 of the classical outline), which is fully proven and axiom-clean.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff
open Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `NormedAddCommGroup` instance packaging

`HolomorphicOneForms X` is a `def` alias for `ContMDiffSection` (see
`Jacobians/Genus.lean`). We wrap `supNormK` in an `AddGroupNorm` and use
`AddGroupNorm.toNormedAddCommGroup` to produce a `NormedAddCommGroup`. -/

omit [ConnectedSpace X] in
/-- The `AddGroupNorm` structure on `HolomorphicOneForms X`. -/
noncomputable def HolomorphicOneForms.supNormKAsAddGroupNorm :
    AddGroupNorm (Jacobians.HolomorphicOneForms X) where
  toFun := fun α => HolomorphicOneForms.supNormK α
  map_zero' := HolomorphicOneForms.supNormK_zero
  add_le' := fun α β => HolomorphicOneForms.supNormK_add_le α β
  neg' := fun α => HolomorphicOneForms.supNormK_neg α
  eq_zero_of_map_eq_zero' := fun α h => HolomorphicOneForms.eq_zero_of_supNormK_eq_zero α h

omit [ConnectedSpace X] in
/-- `HolomorphicOneForms X` as a `NormedAddCommGroup`.

Non-instance: consumers opt in via `letI` or by promoting at a
higher level (as done in `Jacobians.HolomorphicForms`). -/
@[reducible] noncomputable def HolomorphicOneForms.normedAddCommGroup :
    NormedAddCommGroup (Jacobians.HolomorphicOneForms X) :=
  AddGroupNorm.toNormedAddCommGroup HolomorphicOneForms.supNormKAsAddGroupNorm

omit [ConnectedSpace X] in
/-- `HolomorphicOneForms X` as a `NormedSpace ℂ`. -/
@[reducible] noncomputable def HolomorphicOneForms.normedSpace :
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    NormedSpace ℂ (Jacobians.HolomorphicOneForms X) :=
  letI : NormedAddCommGroup (Jacobians.HolomorphicOneForms X) :=
    HolomorphicOneForms.normedAddCommGroup
  NormedSpace.mk (fun c α => le_of_eq (HolomorphicOneForms.supNormK_smul c α))

/-! ### Embedding norm bound (B.9 step 3b — boundedness)

Under the canonical supNormK-based `NormedAddCommGroup`, each
per-chart bcf component of the embedding satisfies `‖·‖ ≤ ‖α‖`. This
is the boundedness that gives continuity of the linear embedding
(Φ α x₀ := `mkOfCompact (localRepOnInnerShrunk α x₀)`) into the
product space. -/

/-- **Boundedness of the bcf-embedding component.**
Under `HolomorphicOneForms.normedAddCommGroup`, the norm of
`mkOfCompact (localRepOnInnerShrunk α x₀)` is bounded by `‖α‖`. -/
theorem norm_mkOfCompact_localRepOnInnerShrunk_le
    (α : Jacobians.HolomorphicOneForms X) (x₀ : X) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    ‖BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀)‖ ≤ ‖α‖ := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  -- BCF norm via mkOfCompact equals ContinuousMap norm.
  rw [BoundedContinuousFunction.norm_mkOfCompact]
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · exact norm_localRepOnInnerShrunk_le_supNormK α hx₀
  · -- Out of chartCover: innerShrunkChart empty, continuous map is 0.
    have h_iso : IsEmpty (innerShrunkChart (X := X) x₀) :=
      Set.isEmpty_coe_sort.mpr (innerShrunkChart_eq_empty x₀ hx₀)
    have h0 : localRepOnInnerShrunk α x₀ = 0 := by
      ext y; exact h_iso.false y |>.elim
    rw [h0, norm_zero]
    exact norm_nonneg _

/-! ### The per-chart continuous linear embedding (B.9 step 3b)

Packages the embedding `α ↦ mkOfCompact (localRepOnInnerShrunk α x₀)`
as a `ContinuousLinearMap` from `HOF X` (with the supNormK-based
normed structure) to `innerShrunkChart x₀ →ᵇ ℂ`. Continuity follows
from the boundedness `‖·‖ ≤ ‖α‖` via `LinearMap.mkContinuous`. -/

/-- Per-chart bcf-embedding as a `ContinuousLinearMap`. -/
noncomputable def HolomorphicOneForms.embedInnerBcf (x₀ : X) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    letI := HolomorphicOneForms.normedSpace (X := X)
    Jacobians.HolomorphicOneForms X →L[ℂ]
      BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  letI := HolomorphicOneForms.normedSpace (X := X)
  refine LinearMap.mkContinuous
    { toFun := fun α => BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀)
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro α β
    apply BoundedContinuousFunction.ext_iff.mpr
    intro y
    have hfn : localRepOnInnerShrunk (α + β) x₀ =
        localRepOnInnerShrunk α x₀ + localRepOnInnerShrunk β x₀ :=
      localRepOnInnerShrunk_add α β x₀
    simp only [BoundedContinuousFunction.mkOfCompact_apply,
      BoundedContinuousFunction.coe_add, Pi.add_apply, hfn,
      ContinuousMap.add_apply]
  · intro c α
    apply BoundedContinuousFunction.ext_iff.mpr
    intro y
    have hfn : localRepOnInnerShrunk (c • α) x₀ = c • localRepOnInnerShrunk α x₀ :=
      localRepOnInnerShrunk_smul c α x₀
    simp only [BoundedContinuousFunction.mkOfCompact_apply,
      BoundedContinuousFunction.coe_smul, RingHom.id_apply, hfn,
      ContinuousMap.smul_apply]
  · intro α
    calc ‖BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀)‖
        ≤ ‖α‖ := norm_mkOfCompact_localRepOnInnerShrunk_le α x₀
      _ = 1 * ‖α‖ := (one_mul _).symm

/-- **Cauchy preservation**: CauchySeq in HOF X maps to CauchySeq in bcf
under the per-chart embedding (via continuity of `embedInnerBcf`). -/
theorem HolomorphicOneForms.cauchySeq_embedInnerBcf_of_cauchySeq
    (x₀ : X)
    (αs : ℕ → Jacobians.HolomorphicOneForms X)
    (hCauchy : letI := HolomorphicOneForms.normedAddCommGroup (X := X)
      CauchySeq αs) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    letI := HolomorphicOneForms.normedSpace (X := X)
    CauchySeq fun n =>
      BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀) := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  letI := HolomorphicOneForms.normedSpace (X := X)
  -- Push CauchySeq through the continuous linear embedding.
  have h := hCauchy.map (HolomorphicOneForms.embedInnerBcf x₀).uniformContinuous
  convert h using 0

/-- **Chart-wise convergence**: CauchySeq in HOF X has per-chart bcf
limits, since bcf is complete. -/
theorem HolomorphicOneForms.exists_bcf_limit_of_cauchySeq
    (x₀ : X)
    (αs : ℕ → Jacobians.HolomorphicOneForms X)
    (hCauchy : letI := HolomorphicOneForms.normedAddCommGroup (X := X)
      CauchySeq αs) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    letI := HolomorphicOneForms.normedSpace (X := X)
    ∃ g : BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ,
      Filter.Tendsto
        (fun n => BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk (αs n) x₀))
        Filter.atTop (nhds g) := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  letI := HolomorphicOneForms.normedSpace (X := X)
  have hCSeq := HolomorphicOneForms.cauchySeq_embedInnerBcf_of_cauchySeq x₀ αs hCauchy
  exact cauchySeq_tendsto_of_complete hCSeq

/-- The continuous linear map's value at α is `mkOfCompact (localRepOnInnerShrunk α x₀)`. -/
theorem HolomorphicOneForms.embedInnerBcf_apply (x₀ : X) (α : Jacobians.HolomorphicOneForms X) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    letI := HolomorphicOneForms.normedSpace (X := X)
    (HolomorphicOneForms.embedInnerBcf x₀ : _ →L[ℂ] _) α =
      BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀) := rfl

/-! ### Montel conclusion: closed unit ball is compact + Riesz

Strategy (classical — Ahlfors-Sario, Rudin Ch. 14):
1. HOF X embeds into Π_{x₀ ∈ chartCover} C(innerShrunkChart x₀, ℂ) via
   `embedInnerBcf x₀` (continuous linear injection).
2. The image of the unit ball is bounded by 1 (by the embedding norm).
3. Cauchy estimates ⇒ equicontinuous (B.7b).
4. Arzelà-Ascoli ⇒ per-chart relative compactness (B.8).
5. Finite product of precompact = precompact (B.9).
6. Completeness via `exists_convergent_subseq_of_bounded` — the
   bundle-level form of "uniform limit of holomorphic is holomorphic",
   now fully proven (see `Complete.lean`).
7. Sequential compactness ⇒ compactness (metric). -/

/-- **Bounded sequences in HOF X have convergent subsequences**
(bundle-level Montel's theorem). Fully proven and axiom-clean.

Given a bounded supNormK sequence of holomorphic 1-forms, there exists
a supNormK-convergent subsequence with the limit in HOF X with
`supNormK limit ≤ 1`.

**Proof path (all ingredients proven in sibling modules):**
1. Per-chart Arzelà (B.8 in `Compactness.lean`) gives per-chart
   convergent subsequences in `bcf(innerShrunkChart x₀, ℂ)`.
2. Diagonal over finite `chartCover` gives a common subsequence
   with bcf-Cauchy per chart.
3. `exists_supNormK_le_const_sup_inner` (chart-transition bound in
   `ChartTransition.lean`) lifts this to supNormK-Cauchy.
4. Define `αLim.toFun` as the pointwise CLM limit (CLM space complete).
5. Show `αLim` is a `ContMDiffSection ω` via chart-wise analyticity of
   the pullback, using `analyticOn_of_pullback_tendsto_locally_uniformly`
   from `Compactness.lean` + chart characterization of ContMDiff.
6. Show `αs(φ k) → αLim` in supNormK and `supNormK αLim ≤ 1`.

Step 5 is the bundle-level "uniform limit of holomorphic sections is
holomorphic"; it is discharged in `Complete.lean` via
`contMDiffOn_totalSpaceMk_L_inner`. -/
theorem HolomorphicOneForms.exists_convergent_subseq_of_bounded
    (αs : ℕ → Jacobians.HolomorphicOneForms X)
    (h : ∀ n, HolomorphicOneForms.supNormK (αs n) ≤ 1) :
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    ∃ (φ : ℕ → ℕ) (_hφ : StrictMono φ) (αLim : Jacobians.HolomorphicOneForms X),
      HolomorphicOneForms.supNormK αLim ≤ 1 ∧
      Filter.Tendsto (fun k => αs (φ k)) Filter.atTop (nhds αLim) := by
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  -- Step 5a: common bcf-convergent subsequence on `chartCover`.
  obtain ⟨φ, hφ, h_bcf⟩ := exists_subseq_bcf_tendsto_on_chartCover αs h
  -- Step 5b: the subsequence is supNormK-Cauchy.
  have h_cauchy := cauchy_supNormK_of_bcf_tendsto αs φ h_bcf
  -- Step 5d-limit: pointwise CLM limit `L y`.
  obtain ⟨L, hL⟩ := exists_toFun_limit (fun n : ℕ => αs (φ n)) h_cauchy
  -- Step 5d-smooth: bundle-smoothness reconstruction via substeps 1-5.
  -- Substeps 1-4 handle the per-chart smoothness; substep 5 below
  -- assembles via the finite cover.
  have h_smooth : ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        x (L x)) := by
    intro y
    -- Find x₀' ∈ chartCover with y ∈ innerChartOpen x₀'.
    have hmem : y ∈ (Set.univ : Set X) := Set.mem_univ _
    rw [← iUnion_innerChartOpen_chartCover_eq (X := X)] at hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x₀', hx₀'mem, hy_in⟩ := hmem
    obtain ⟨g', hg'⟩ := h_bcf x₀' hx₀'mem
    -- Substep 4 gives ContMDiffOn on innerChartOpen x₀'.
    have h_on := contMDiffOn_totalSpaceMk_L_inner (fun n => αs (φ n)) L hL hx₀'mem g' hg'
    -- Lift ContMDiffOn + interior point → ContMDiffAt.
    exact (h_on y hy_in).contMDiffAt ((innerChartOpen_isOpen x₀').mem_nhds hy_in)
  -- Assemble αLim as a ContMDiffSection.
  let αLim : Jacobians.HolomorphicOneForms X := ⟨L, h_smooth⟩
  have hαLim_toFun : αLim.toFun = L := rfl
  -- Pointwise Tendsto transfers to αLim.toFun.
  have hL' : ∀ y : X,
      Filter.Tendsto (fun n : ℕ => (αs (φ n)).toFun y) Filter.atTop
        (nhds (αLim.toFun y)) := by
    intro y; rw [hαLim_toFun]; exact hL y
  refine ⟨φ, hφ, αLim, ?_supNormK_bound, ?_tendsto⟩
  · -- Step 6a: supNormK αLim ≤ 1 from scalar bound `norm_limit_localRep_le_one`.
    unfold HolomorphicOneForms.supNormK
    rw [Finset.sup'_le_iff]
    intro x₀ hx₀
    unfold HolomorphicOneForms.chartNormK
    by_cases hne : Set.Nonempty (shrunkChart (X := X) x₀)
    · apply csSup_le (hne.image _)
      rintro r ⟨y, hy, rfl⟩
      -- ‖localRep αLim x₀ y‖ = ‖L y (e.symmL ℂ y 1)‖ ≤ 1.
      show ‖localRep αLim x₀ y‖ ≤ 1
      set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      have heq : localRep αLim x₀ y = L y (e.symmL ℂ y 1) := by
        show αLim.toFun y _ = _
        rw [hαLim_toFun]
      rw [heq]
      exact norm_limit_localRep_le_one (fun n => αs (φ n))
        (fun n => h (φ n)) L hL hx₀ hy
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne, Real.sSup_empty]
  · -- Step 6b: Tendsto via supNormK from scalar bound `norm_localRep_sub_limit_le`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Use the scalar bound at ε/2.
    obtain ⟨N, hN⟩ := norm_localRep_sub_limit_le (fun n => αs (φ n)) h_cauchy L hL
      (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    -- supNormK (αs (φ n) - αLim) ≤ ε/2 < ε.
    have h_step : HolomorphicOneForms.supNormK (αs (φ n) - αLim) ≤ ε / 2 := by
      unfold HolomorphicOneForms.supNormK
      rw [Finset.sup'_le_iff]
      intro x₀ hx₀
      unfold HolomorphicOneForms.chartNormK
      by_cases hne : Set.Nonempty (shrunkChart (X := X) x₀)
      · apply csSup_le (hne.image _)
        rintro r ⟨y, hy, rfl⟩
        -- ‖localRep (αs (φ n) - αLim) x₀ y‖ ≤ ε/2
        show ‖localRep (αs (φ n) - αLim) x₀ y‖ ≤ ε / 2
        set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
        have h_sub_eq : localRep (αs (φ n) - αLim) x₀ y =
            localRep (αs (φ n)) x₀ y - L y (e.symmL ℂ y 1) := by
          show (αs (φ n) - αLim).toFun y (e.symmL ℂ y 1) =
              (αs (φ n)).toFun y (e.symmL ℂ y 1) - L y (e.symmL ℂ y 1)
          have h_eq : (αs (φ n) - αLim).toFun y =
              (αs (φ n)).toFun y - αLim.toFun y :=
            congr_fun (ContMDiffSection.coe_sub (αs (φ n)) αLim) y
          rw [h_eq, ContinuousLinearMap.sub_apply, hαLim_toFun]
        rw [h_sub_eq]
        exact hN n hn x₀ hx₀ y hy
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        simp [hne, Real.sSup_empty]
        linarith
    have h_norm_eq : ‖αs (φ n) - αLim‖ =
        HolomorphicOneForms.supNormK (αs (φ n) - αLim) := rfl
    rw [h_norm_eq]
    linarith

/-- **Montel's closedBall is compact**, under the canonical
supNormK-based normed structure. With `exists_convergent_subseq_of_bounded`
supplying the structural bundle-reconstruction piece, this closes via
sequential compactness.

Takes no typeclass arguments — uses the specific supNormK-based norm
(via `letI` in the type). At call sites where the canonical
`HolomorphicOneForms.normedAddCommGroup` is in scope as an instance,
types unify. -/
theorem HolomorphicOneForms.closedBall_isCompact :
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    letI := HolomorphicOneForms.normedSpace (X := X)
    IsCompact (Metric.closedBall
      (0 : Jacobians.HolomorphicOneForms X) 1) := by
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  letI := HolomorphicOneForms.normedSpace (X := X)
  rw [isCompact_iff_isSeqCompact]
  intro αs hαs
  have hsup : ∀ n, HolomorphicOneForms.supNormK (αs n) ≤ 1 := by
    intro n
    have h := hαs n
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  obtain ⟨φ, hφ, αLim, hαLim_norm, hαLim_tendsto⟩ :=
    HolomorphicOneForms.exists_convergent_subseq_of_bounded αs hsup
  refine ⟨αLim, ?_, φ, hφ, hαLim_tendsto⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hαLim_norm

/-
Consumer-friendly usage: once the NormedAddCommGroup / NormedSpace ℂ
instances are in scope (typically provided in Jacobians.HolomorphicForms),
the `FiniteDimensional` conclusion follows via Riesz:

    noncomputable instance : FiniteDimensional ℂ (HolomorphicOneForms X) :=
      FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one
        Jacobians.Montel.HolomorphicOneForms.closedBall_isCompact
-/

/-! ### Status

- **`closedBall_isCompact`**: PROVEN (axiom-clean) via sequential
  compactness using `exists_convergent_subseq_of_bounded`.
- **`exists_convergent_subseq_of_bounded`**: PROVEN — bundle-level
  Montel: bounded sequence has a supNormK-convergent subsequence.
- All Arzelà-Ascoli infrastructure (B.1-B.9) is in
  `Jacobians/Montel/Compactness.lean`, fully proven.
- All analytic-limit machinery (`analyticOn_of_tendstoLocallyUniformlyOn`
  etc.) is in place. The entire Montel route to
  `FiniteDimensional ℂ (HolomorphicOneForms X)` is complete. -/

end Jacobians.Montel
