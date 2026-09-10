/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.ProperMapDegreeConstruct
import KirovDolbeault.Discharge.Manifold.LocalKFoldMultiplicityUnconditional
import KirovDolbeault.Discharge.Manifold.AnalyticLocalFactorization
import KirovDolbeault.Discharge.Manifold.RoucheBridge
import KirovDolbeault.Discharge.Manifold.LocalNormalForm
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Conservation of number for the multiplicity sum: `IsLocallyConstant (N f)`

This file delivers the final analytic piece of `deg_div`: the **global** local
constancy of the fibre-*multiplicity* function

> `N f w = ∑_{x ∈ F⁻¹(w)} d_x(F)`        (`F = f.toRiemannSphere`, `d_x = localDeg`),

across **all** of `ℂℙ¹`, including the finitely many *branch* values where the
naive cardinality `#F⁻¹(w)` drops (sheets collide) but the multiplicity sum does
**not**.  This is the §17.9 "conservation of number" core; through
`ProperMapDegreeConstruct.ProperMapDegreeData.ofConservation` it discharges
`exists_properMapDegree` — the Riemann–Roch keystone `deg (div f) = 0`.

## The patching structure (multiplicity analogue of `HurwitzPatchingData`)

`MultiplicityPatchingData f w₀` mirrors
`Jacobians.Discharge.HurwitzPatchingData` (the *cardinality* patching package),
but each sheet `U x` around a fibre point `x ∈ F⁻¹(w₀)` carries a **weight**
`m x : ℤ` — its local degree `d_x(F)` — and the structural obligation is that for
every `w` in a common neighbourhood `W` of `w₀`, the multiplicity sum over the
sheet's slice of the fibre is constant `= m x`:

> `∑_{y ∈ U x ∩ F⁻¹(w)} d_y(F) = m x`     (for all `w ∈ W`).

At `w₀` itself this reads `m x = d_x(F)` (the fibre slice is `{x}`); for `w` near
but `≠ w₀` the slice is the `m x` simple preimages produced by the local normal
form `z ↦ z^{m x}·unit`, each of local degree `1`, summing to `m x` — even at a
branch value, where the ncard is `< ∑ m x`.  Properness of `F` (no preimage
escapes the finitely many sheets) closes the global count.

## What this file builds

* `structure MultiplicityPatchingData f w₀` — the per-`w₀` multiplicity patching
  package (sheets + weights + per-sheet multiplicity conservation + no-escape +
  the value reading `N f w₀ = ∑ m x`).
* `MultiplicityPatchingData.fibreMult_eq_sum_weights` — for `w ∈ W`, the global
  multiplicity sum `fibreMult f w` equals `∑ m x` (the partition-into-sheets
  computation, via `finsum_mem_biUnion`).
* `MultiplicityPatchingData.N_eq_of_mem_W` — for `w ∈ W`, `N f w = N f w₀`.
* `isLocallyConstant_N_of_pointwiseMultiplicityPatching` — a pointwise supply of
  `MultiplicityPatchingData f w₀` (one at every `w₀`) yields
  `IsLocallyConstant (N f)`.  This mirrors
  `fibreCard_isLocallyConstant_of_pointwiseHurwitz` and is the structure ⇒
  local-constancy bridge.

## Status

The structure and the structure ⇒ local-constancy bridge are delivered
complete and axiom-clean.  The per-`w₀` *construction* of a
`MultiplicityPatchingData` (the genuine §17.9 analytic content: finite fibre via
properness, per-sheet normal form, the `m`-fold simple-root multiplicity split,
no-escape) is the residual obligation; the structure isolates it into *true,
non-vacuous* fields, never `False`.

## References

* Forster, *Lectures on Riemann Surfaces*, §4 (the degree), Cor. 4.24–4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, §II.4 (conservation of number).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset OnePoint Filter

namespace Jacobians.MultiplicityPatching

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct

set_option linter.unusedSectionVars false

/-! ### The planar `m`-fold multiplicity split (step 3, the analytic core)

This is the genuine §17.9 content at the level of one chart.  In a chart at a
fibre point, `g := f.toFun ∘ chart.symm` minus the value admits a local normal
form `g z - w₀ = (z - x₀)^m · u(z)` with `u(x₀) ≠ 0`, `m ≥ 1` the local degree.
Equivalently (the `k`-th-root substitution of `LocalKFoldMultiplicity`), there is
an analytic `v` with `v x₀ = 0`, `deriv v x₀ ≠ 0` and `g z - w₀ = v(z)^m` on a
disk.  For `w` near (but `≠`) `w₀`:

* the equation `g z = w` has exactly `m` roots in a small ball
  (`localKFoldMultiplicity_preimage_card_unconditional`);
* **each root is simple**: at a root `z₁`, `v(z₁) ≠ 0` and `deriv v z₁ ≠ 0`
  (continuity, shrinking the ball), so `deriv g z₁ = m·v(z₁)^{m-1}·deriv v z₁ ≠ 0`,
  whence `meromorphicOrderAt (g − w) z₁ = 1` (`analyticOrderAt_eq_one_of_zero_deriv_ne_zero`);
* therefore the **multiplicity sum** over the root set is `m · 1 = m`.

This is the per-chart conservation that the patching structure's `sheetMult_eq`
field abstracts. -/

namespace Planar

open Metric Set Jacobians.Discharge.Manifold

variable {g v : ℂ → ℂ} {x₀ w₀ : ℂ} {ρ : ℝ} {m : ℕ}

/-- **Each root is a simple zero of `g − w`** (the simplicity at a root).

Given the substitution data `g z − w₀ = v(z)^m` on `closedBall x₀ ρ` with `v`
analytic, `deriv v` nonvanishing on `ball x₀ ε` (`ε ≤ ρ`), and `m ≥ 1`: at any
`z₁ ∈ ball x₀ ε` with `g z₁ = w` and `w ≠ w₀`, the chart-pullback meromorphic
order of `g − w` is exactly `1`.

Proof: `v(z₁)^m = g z₁ − w₀ = w − w₀ ≠ 0`, so `v(z₁) ≠ 0`; with `deriv v z₁ ≠ 0`
and the power rule, `deriv g z₁ = m·v(z₁)^{m-1}·deriv v z₁ ≠ 0`, hence
`g − w` has a simple zero at `z₁`. -/
lemma orderAt_root_eq_one
    (hm : 1 ≤ m) {ε : ℝ} (hε_le : ε ≤ ρ)
    (hv_an : AnalyticOnNhd ℂ v (closedBall x₀ ρ))
    (hg_an : AnalyticOnNhd ℂ g (closedBall x₀ ε))
    (hdv : ∀ z ∈ ball x₀ ε, deriv v z ≠ 0)
    (hpow : ∀ z ∈ closedBall x₀ ρ, g z - w₀ = (v z) ^ m)
    {z₁ w : ℂ} (hz₁ : z₁ ∈ ball x₀ ε) (hgz₁ : g z₁ = w) (hw_ne : w ≠ w₀) :
    (meromorphicOrderAt (fun ζ => g ζ - w) z₁).untop₀ = 1 := by
  have hz₁_ε_closed : z₁ ∈ closedBall x₀ ε := ball_subset_closedBall hz₁
  have hz₁_closed : z₁ ∈ closedBall x₀ ρ :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hε_le)) hz₁
  -- `v(z₁) ≠ 0`: `v(z₁)^m = w − w₀ ≠ 0`.
  have hvz_ne : v z₁ ≠ 0 := by
    intro h0
    have hpz : g z₁ - w₀ = (v z₁) ^ m := hpow z₁ hz₁_closed
    rw [h0, zero_pow (Nat.one_le_iff_ne_zero.mp hm), hgz₁] at hpz
    -- `hpz : w − w₀ = 0`, i.e. `w = w₀`.
    exact hw_ne (sub_eq_zero.mp hpz)
  -- `deriv g z₁ ≠ 0` (power rule via the substitution).
  have hdvz : deriv v z₁ ≠ 0 := hdv z₁ hz₁
  have hv_diff : HasDerivAt v (deriv v z₁) z₁ :=
    (hv_an z₁ hz₁_closed).differentiableAt.hasDerivAt
  have hpow_d : HasDerivAt (fun z => (v z) ^ m)
      ((m : ℂ) * (v z₁) ^ (m-1) * deriv v z₁) z₁ := by
    have := (hasDerivAt_pow m (v z₁)).comp z₁ hv_diff
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hball_nhds : ball x₀ ε ∈ 𝓝 z₁ := isOpen_ball.mem_nhds hz₁
  have hg_eq : g =ᶠ[𝓝 z₁] (fun z => (v z) ^ m + w₀) := by
    filter_upwards [hball_nhds] with z hz
    have hz_closed : z ∈ closedBall x₀ ρ :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hε_le)) hz
    have h := hpow z hz_closed
    rw [sub_eq_iff_eq_add] at h; exact h
  have hgder : HasDerivAt g ((m : ℂ) * (v z₁) ^ (m-1) * deriv v z₁) z₁ :=
    (by simpa using hpow_d.add_const w₀ :
      HasDerivAt (fun z => (v z) ^ m + w₀) _ z₁).congr_of_eventuallyEq hg_eq
  have hdg : deriv g z₁ ≠ 0 := by
    rw [hgder.deriv]
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
    exact mul_ne_zero (mul_ne_zero hm0 (pow_ne_zero _ hvz_ne)) hdvz
  -- `g` analytic at `z₁`, value `w`, derivative `≠ 0` ⟹ order of `g − w` is `1`.
  have hg_an' : AnalyticAt ℂ g z₁ := hg_an z₁ hz₁_ε_closed
  have hh_an : AnalyticAt ℂ (fun ζ => g ζ - w) z₁ := hg_an'.sub analyticAt_const
  have hhz : (fun ζ => g ζ - w) z₁ = 0 := by simp [hgz₁]
  have hdh : deriv (fun ζ => g ζ - w) z₁ ≠ 0 := by
    have hd : HasDerivAt (fun ζ => g ζ - w) (deriv g z₁) z₁ := by
      simpa using (hg_an'.differentiableAt.hasDerivAt).sub_const w
    rw [hd.deriv]; exact hdg
  have hord1 : analyticOrderAt (fun ζ => g ζ - w) z₁ = 1 :=
    hh_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hhz hdh
  rw [hh_an.meromorphicOrderAt_eq, hord1]; rfl

/-- **The planar `m`-fold multiplicity split** (the per-chart §17.9 content).

For `g : ℂ → ℂ` analytic at `x₀` with `g x₀ = w₀` and `analyticOrderAt (g − w₀) x₀
= m` (`m ≥ 1`, the local degree), there exist `ε, δ > 0` such that for every `w`
in the punctured ball `ball w₀ δ ∖ {w₀}` the **multiplicity sum** over the local
fibre `{z ∈ ball x₀ ε | g z = w}` is exactly `m`:

> `∑_{z : g z = w, z ∈ ball x₀ ε} ord_z(g − w) = m`.

The `m` roots (`kFold_count_radiusBounded`) are each *simple* (`orderAt_root_eq_one`,
order `1`), so the multiplicity sum is `m · 1 = m` — the conservation of number
that holds even at branch values (where the *cardinality* would drop for a
different `w`, but here every `w ≠ w₀` near `w₀` has `m` simple preimages).

The radius bound `ε ≤` (deriv-nonzero radius of the substitution `v`) is what
guarantees every root lies where `g` is *locally injective up to the `m`-fold
cover*, i.e. is a simple zero of `g − w`. -/
theorem orderSum_eq_of_analyticOrder
    (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g x₀) (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (m : ℕ∞)) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ ball w₀ δ, w ≠ w₀ →
        (∑ᶠ z ∈ {z ∈ ball x₀ ε | g z = w}, (meromorphicOrderAt (fun ζ => g ζ - w) z).untop₀)
          = (m : ℤ) := by
  classical
  -- Build the local factorization `g z − w₀ = (z − x₀)^m · u z`, `u x₀ ≠ 0`.
  obtain ⟨R₀, hR₀_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hm hg h_w₀ hord
  -- Build the `m`-th-root substitution `v` (with `g z − w₀ = v(z)^m`).
  have hsub : KthRootSubstitution g x₀ w₀ m :=
    kthRootSubstitution_of_localFactorization hR₀_pos hm hu_an hu_x₀ hfact
  obtain ⟨v, ρ, hρ_pos, hv_an, hv_x₀_eq, hv_d, hv_pow⟩ := hsub.exists_substitution
  -- A closed ball `closedBall x₀ R_g` on which `g` itself is analytic.
  obtain ⟨R_g, hR_g_pos, hg_anBall⟩ :
      ∃ r > (0 : ℝ), AnalyticOnNhd ℂ g (closedBall x₀ r) := by
    obtain ⟨s, hs_mem, hs_an⟩ := hg.exists_mem_nhds_analyticOnNhd
    rw [Metric.mem_nhds_iff] at hs_mem
    obtain ⟨r, hr_pos, hr_sub⟩ := hs_mem
    exact ⟨r / 2, by linarith, fun z hz => hs_an z (hr_sub (by
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz; linarith))⟩
  -- `deriv v ≠ 0` on a ball `ball x₀ R` with `R ≤ ρ`, `R ≤ R_g`
  -- (continuity of the analytic deriv).
  obtain ⟨R, hR_pos, hR_le_ρ, hR_le_Rg, hdv_ball⟩ :
      ∃ R > (0 : ℝ), R ≤ ρ ∧ R ≤ R_g ∧ ∀ z ∈ ball x₀ R, deriv v z ≠ 0 := by
    have hderiv_an : AnalyticOnNhd ℂ (deriv v) (closedBall x₀ ρ) := hv_an.deriv
    have hcont : ContinuousAt (deriv v) x₀ :=
      (hderiv_an x₀ (mem_closedBall_self hρ_pos.le)).continuousAt
    have hpre : (deriv v) ⁻¹' {z : ℂ | z ≠ 0} ∈ 𝓝 x₀ :=
      hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hv_d)
    rw [Metric.mem_nhds_iff] at hpre
    obtain ⟨r, hr_pos, hr_sub⟩ := hpre
    refine ⟨min r (min ρ R_g), lt_min hr_pos (lt_min hρ_pos hR_g_pos),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _),
      fun z hz => hr_sub (ball_subset_ball (min_le_left _ _) hz)⟩
  -- `g` is analytic on `closedBall x₀ R` (`R ≤ R_g`).
  have hg_anNhd : AnalyticOnNhd ℂ g (closedBall x₀ R) :=
    hg_anBall.mono (closedBall_subset_closedBall hR_le_Rg)
  -- Radius-bounded `m`-fold count, with the prescribed radius `R`.
  obtain ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, hcount⟩ :=
    Jacobians.Discharge.MMeromorphicAt.kFold_count_radiusBounded hR_pos hm hg h_w₀ hord
  refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  -- Reframe the count: it is stated for `w ∈ ball (g x₀) δ`, `w ≠ g x₀`.
  have hw_ball' : w ∈ ball (g x₀) δ := by rw [h_w₀]; exact hw_ball
  have hw_ne' : w ≠ g x₀ := by rw [h_w₀]; exact hw_ne
  have hncard : ({z ∈ ball x₀ ε | g z = w} : Set ℂ).ncard = m := hcount w hw_ball' hw_ne'
  -- The root set is finite (ncard = m ≥ 1).
  set S : Set ℂ := {z ∈ ball x₀ ε | g z = w} with hS_def
  have hS_fin : S.Finite := Set.finite_of_ncard_ne_zero (by rw [hncard]; omega)
  -- Each root has multiplicity-order `1` (simplicity).
  have hroot1 : ∀ z ∈ S, (meromorphicOrderAt (fun ζ => g ζ - w) z).untop₀ = 1 := by
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    -- `z ∈ ball x₀ ε ⊆ ball x₀ R` (since `ε ≤ R`), where `deriv v ≠ 0`.
    have hz_R : z ∈ ball x₀ R := ball_subset_ball hε_le_R hz_ball
    exact orderAt_root_eq_one (g := g) (v := v) (x₀ := x₀) (w₀ := w₀) (ρ := ρ) (m := m)
      hm hR_le_ρ hv_an hg_anNhd hdv_ball hv_pow hz_R hz_g hw_ne
  -- The multiplicity sum of constant `1` over `S` (ncard `m`) is `m`.
  rw [finsum_mem_eq_finite_toFinset_sum _ hS_fin,
    Finset.sum_congr rfl (fun z hz => hroot1 z (by rwa [hS_fin.mem_toFinset] at hz)),
    Finset.sum_const]
  have hc : hS_fin.toFinset.card = m := by rw [← Set.ncard_eq_toFinset_card S hS_fin, hncard]
  rw [hc]; simp

end Planar

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The multiplicity patching package

`MultiplicityPatchingData f w₀` is the conservation-of-number datum at the value
`w₀ : ℂℙ¹`.  It mirrors `HurwitzPatchingData f w₀` but tracks *multiplicities*:
each sheet contributes its weight `m x = localDeg f w₀ x` to the multiplicity sum
of every nearby fibre, even across branch values. -/

/-- **Multiplicity patching package** for the holomorphic proper map
`F = f.toRiemannSphere` at a value `w₀ : ℂℙ¹`.

Bundles, around the (finite) fibre `F⁻¹(w₀) = ↑xs`:

* a sheet `U x` around each `x ∈ xs`, open and pairwise disjoint;
* a weight `m x : ℤ` (the local degree `localDeg f w₀ x`);
* a common neighbourhood `W` of `w₀`;
* for each sheet and each `w ∈ W`, the **multiplicity-conservation** identity
  `∑_{y ∈ U x ∩ F⁻¹(w)} localDeg f w y = m x`;
* finiteness of every fibre over `W`;
* the **no-escape** property `F⁻¹(W) ⊆ ⋃ x ∈ xs, U x`;
* the value reading `N f w₀ = ∑ x ∈ xs, m x`.

From these, the fibre-multiplicity `N f` is constantly `∑ m x` on `W`, hence
locally constant at `w₀`. -/
structure MultiplicityPatchingData (f : MeromorphicFunction X) (w₀ : RiemannSphere) where
  /-- Finite enumeration of the fibre `F⁻¹(w₀)`. -/
  xs : Finset X
  /-- `↑xs` *is* the fibre over `w₀`. -/
  xs_coe : (xs : Set X) = f.toRiemannSphere ⁻¹' {w₀}
  /-- A sheet `U x` around each fibre point `x ∈ xs`. -/
  U : X → Set X
  /-- Each sheet is open. -/
  U_open : ∀ x ∈ xs, IsOpen (U x)
  /-- Each sheet contains its fibre point. -/
  mem_U_self : ∀ x ∈ xs, x ∈ U x
  /-- Sheets indexed by distinct fibre points are disjoint. -/
  U_pairwiseDisjoint : ∀ x ∈ xs, ∀ x' ∈ xs, x ≠ x' → Disjoint (U x) (U x')
  /-- The weight (local degree) of each sheet. -/
  m : X → ℤ
  /-- A common open neighbourhood `W` of `w₀`. -/
  W : Set RiemannSphere
  /-- `W` is open. -/
  W_open : IsOpen W
  /-- `w₀ ∈ W`. -/
  w₀_mem_W : w₀ ∈ W
  /-- **Multiplicity conservation per sheet**: for `w ∈ W`, the multiplicity sum
      over the sheet's slice of the fibre is constantly the weight `m x`. -/
  sheetMult_eq : ∀ x ∈ xs, ∀ w ∈ W,
    (∑ᶠ y ∈ U x ∩ f.toRiemannSphere ⁻¹' {w}, localDeg f w y) = m x
  /-- Every fibre over `W` is finite (properness of `F`). -/
  fibre_finite : ∀ w ∈ W, (f.toRiemannSphere ⁻¹' {w}).Finite
  /-- **No escape**: every preimage of a point of `W` lies in one of the sheets. -/
  preimage_W_subset : f.toRiemannSphere ⁻¹' W ⊆ ⋃ x ∈ xs, U x
  /-- **The fibre-multiplicity reading on `W`**: at every `w ∈ W`, the value
      `N f w` equals the genuine multiplicity sum `fibreMult f w`.  Away from the
      two special values this is *definitional* (`N = fibreMult` there); at `coe
      0` / `∞` it is the special-fibre identity `fibreMult f (coe 0) = zerosCount
      f` / `fibreMult f ∞ = polesCount f` (Forster §4), restricted to `W`. -/
  N_eq_fibreMult : ∀ w ∈ W, N f w = fibreMult f w

namespace MultiplicityPatchingData

variable {f : MeromorphicFunction X} {w₀ : RiemannSphere}

/-! ### The partition-into-sheets computation

For `w ∈ W`, the fibre `F⁻¹(w)` decomposes as the disjoint union of the sheet
slices `U x ∩ F⁻¹(w)` (by no-escape: every preimage lies in some sheet; by
disjointness of the sheets the union is disjoint).  The multiplicity sum
therefore splits as `∑ x ∈ xs, (sheet multiplicity)`, each term `= m x` by
`sheetMult_eq`, giving `∑ m x`. -/

/-- The fibre over `w ∈ W` is the disjoint union of the sheet slices
`U x ∩ F⁻¹(w)`. -/
lemma fibre_eq_iUnion_sheets (h : MultiplicityPatchingData f w₀)
    {w : RiemannSphere} (hw : w ∈ h.W) :
    f.toRiemannSphere ⁻¹' {w} = ⋃ x ∈ (h.xs : Set X), (h.U x ∩ f.toRiemannSphere ⁻¹' {w}) := by
  apply Set.Subset.antisymm
  · intro y hy
    -- `y ∈ F⁻¹{w} ⊆ F⁻¹ W`, so `y ∈ ⋃ U x` by no-escape.
    have hyW : y ∈ f.toRiemannSphere ⁻¹' h.W := by
      have : f.toRiemannSphere y = w := hy
      show f.toRiemannSphere y ∈ h.W; rw [this]; exact hw
    have hy_union := h.preimage_W_subset hyW
    rw [Set.mem_iUnion₂] at hy_union
    obtain ⟨x, hxxs, hyUx⟩ := hy_union
    rw [Set.mem_iUnion₂]
    exact ⟨x, hxxs, hyUx, hy⟩
  · intro y hy
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨_, _, _, hyfib⟩ := hy
    exact hyfib

/-- **Multiplicity sum over a nearby fibre = total weight.**  For `w ∈ W`, the
global fibre-multiplicity sum `fibreMult f w` equals `∑ x ∈ xs, m x`. -/
lemma fibreMult_eq_sum_weights (h : MultiplicityPatchingData f w₀)
    {w : RiemannSphere} (hw : w ∈ h.W) :
    fibreMult f w = ∑ x ∈ h.xs, h.m x := by
  classical
  -- Pairwise disjointness of the sheet slices over the index set `↑xs`.
  have hdisj : (h.xs : Set X).PairwiseDisjoint
      (fun x => h.U x ∩ f.toRiemannSphere ⁻¹' {w}) := by
    intro x hx x' hx' hne
    exact (h.U_pairwiseDisjoint x hx x' hx' hne).mono inter_subset_left inter_subset_left
  -- Each sheet slice is finite (subset of the finite fibre over `w`).
  have hfin : ∀ x ∈ (h.xs : Set X),
      (h.U x ∩ f.toRiemannSphere ⁻¹' {w}).Finite := by
    intro x _
    exact (h.fibre_finite w hw).subset inter_subset_right
  -- Unfold `fibreMult`, rewrite the fibre as the disjoint union, partition the sum.
  rw [fibreMult, h.fibre_eq_iUnion_sheets hw,
    finsum_mem_biUnion hdisj h.xs.finite_toSet hfin]
  -- Now: `∑ᶠ x ∈ ↑xs, ∑ᶠ y ∈ (U x ∩ F⁻¹{w}), localDeg f w y = ∑ x ∈ xs, m x`.
  rw [finsum_mem_coe_finset]
  apply Finset.sum_congr rfl
  intro x hx
  exact h.sheetMult_eq x hx w hw

/-! ### The value of `N` on `W` is constant

On `W`, the value `N f w` agrees with the multiplicity sum `fibreMult f w` (the
field `N_eq_fibreMult` — definitional away from the special values, the
special-fibre identity at `coe 0` / `∞`), and `fibreMult f w = ∑ m x` is constant
by `fibreMult_eq_sum_weights`.  Hence `N f` is constantly `N f w₀` on `W`. -/

/-- **`N f` is constantly `N f w₀` on `W`.**  For `w ∈ W`, both `N f w` and
`N f w₀` equal the total weight `∑ x ∈ xs, m x` (`N_eq_fibreMult` ∘
`fibreMult_eq_sum_weights`), hence agree. -/
lemma N_eq_of_mem_W (h : MultiplicityPatchingData f w₀)
    {w : RiemannSphere} (hw : w ∈ h.W) :
    N f w = N f w₀ := by
  rw [h.N_eq_fibreMult w hw, h.N_eq_fibreMult w₀ h.w₀_mem_W,
    h.fibreMult_eq_sum_weights hw, h.fibreMult_eq_sum_weights h.w₀_mem_W]

end MultiplicityPatchingData

/-! ### The structure ⇒ local-constancy bridge

Mirroring `fibreCard_isLocallyConstant_of_pointwiseHurwitz`: a pointwise supply
of `MultiplicityPatchingData f w₀` at *every* `w₀ : ℂℙ¹` yields
`IsLocallyConstant (N f)`.  The witness `h w₀` provides the open neighbourhood
`(h w₀).W` of `w₀` on which `N f` is constantly `N f w₀`. -/

/-- **Local constancy of `N f` from a pointwise multiplicity-patching supply.**

If for *every* `w₀ : ℂℙ¹` we are given a `MultiplicityPatchingData f w₀`, then
`N f` is locally constant on `ℂℙ¹`.  The witness `h w₀` supplies the open
neighbourhood `(h w₀).W` of `w₀` on which `N f` is constantly `N f w₀`
(`N_eq_of_mem_W`).

This is the multiplicity analogue of
`Jacobians.Discharge.fibreCard_isLocallyConstant_of_pointwiseHurwitz`, and the
structure ⇒ local-constancy half of the conservation-of-number assembly. -/
theorem isLocallyConstant_N_of_pointwiseMultiplicityPatching
    (f : MeromorphicFunction X)
    (h : ∀ w₀ : RiemannSphere, MultiplicityPatchingData f w₀) :
    IsLocallyConstant (N f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro w₀
  have hW_mem : (h w₀).W ∈ nhds w₀ :=
    (h w₀).W_open.mem_nhds (h w₀).w₀_mem_W
  filter_upwards [hW_mem] with w hw
  exact (h w₀).N_eq_of_mem_W hw

/-! ### Non-vacuity: the structure is satisfiable

`MultiplicityPatchingData f w₀` is a genuine, true, *satisfiable* package — not a
disguised `False`.  We certify this at a value `w₀` *outside the range* of
`F = f.toRiemannSphere` (and not one of the two special points): there `F⁻¹{w₀}`
is empty, and on the open neighbourhood `(range F)ᶜ ∖ {∞, coe 0}` of `w₀` every
fibre is empty, so the empty patching datum (`xs = ∅`, `m = 0`) satisfies every
field.  Since `F` is proper, `range F` is closed, so its complement is open; such
`w₀` exist whenever `F` is non-surjective (e.g. a non-constant `f` omitting a
value).  This is the multiplicity analogue of
`ProperMapDegree.ProperMapDegreeData.ofDivEqZero`. -/

/-- **Non-vacuity witness.**  At a value `w₀` outside `range (f.toRiemannSphere)`
and distinct from `∞` and `coe 0`, the empty multiplicity-patching datum
satisfies every field of `MultiplicityPatchingData f w₀`.  Hence the structure's
obligations are *satisfiable* — it is not a disguised `False`. -/
noncomputable def MultiplicityPatchingData.ofNotMemRange (f : MeromorphicFunction X)
    {w₀ : RiemannSphere} (h_notmem : w₀ ∉ Set.range f.toRiemannSphere)
    (h_infty : w₀ ≠ OnePoint.infty) (h_zero : w₀ ≠ ((0 : ℂ) : RiemannSphere)) :
    MultiplicityPatchingData f w₀ := by
  classical
  -- `range F` is closed (properness), so its complement is open.
  have h_rangeClosed : IsClosed (Set.range f.toRiemannSphere) :=
    f.isProperMap_toRiemannSphere.isClosedMap.isClosed_range
  -- `W := (range F)ᶜ ∖ {∞, coe 0}` is open and contains `w₀`.
  set W : Set RiemannSphere :=
    (Set.range f.toRiemannSphere)ᶜ ∩ {OnePoint.infty}ᶜ ∩ {((0 : ℂ) : RiemannSphere)}ᶜ with hW_def
  have hW_open : IsOpen W :=
    ((h_rangeClosed.isOpen_compl).inter (isClosed_singleton.isOpen_compl)).inter
      (isClosed_singleton.isOpen_compl)
  have hw₀_W : w₀ ∈ W :=
    ⟨⟨h_notmem, by simpa using h_infty⟩, by simpa using h_zero⟩
  -- On `W`, every fibre is empty (`w ∉ range F`).
  have hfib_empty : ∀ w ∈ W, f.toRiemannSphere ⁻¹' {w} = ∅ := by
    intro w hw
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact hw.1.1 ⟨y, hy⟩
  refine
    { xs := ∅
      xs_coe := ?_
      U := fun _ => ∅
      U_open := by intro x hx; simp at hx
      mem_U_self := by intro x hx; simp at hx
      U_pairwiseDisjoint := by intro x hx; simp at hx
      m := fun _ => 0
      W := W
      W_open := hW_open
      w₀_mem_W := hw₀_W
      sheetMult_eq := by intro x hx; simp at hx
      fibre_finite := fun w hw => by rw [hfib_empty w hw]; exact Set.finite_empty
      preimage_W_subset := ?_
      N_eq_fibreMult := ?_ }
  · -- `↑(∅ : Finset X) = F⁻¹{w₀}`: both empty (`w₀ ∉ range F`).
    rw [Finset.coe_empty, (hfib_empty w₀ hw₀_W).symm]
  · -- No escape: `F⁻¹ W = ∅` since `F y ∈ W ⊆ (range F)ᶜ` is impossible (`F y ∈ range F`).
    intro y hy
    have hFy_W : f.toRiemannSphere y ∈ W := hy
    exact absurd ⟨y, rfl⟩ hFy_W.1.1
  · -- `N f w = fibreMult f w` on `W`: `w` is non-special there, so by definition
    -- of `N` the `else`-branch fires (`N w = fibreMult w`).
    intro w hw
    have hw_infty : w ≠ OnePoint.infty := by simpa using hw.1.2
    have hw_zero : w ≠ ((0 : ℂ) : RiemannSphere) := by simpa using hw.2
    show N f w = fibreMult f w
    simp only [N, if_neg hw_infty, if_neg hw_zero]

/-! ### The headline: discharging `exists_properMapDegree` from the patching supply

The pointwise multiplicity-patching supply yields `IsLocallyConstant (N f)`
(above), which `ProperMapDegreeConstruct.ProperMapDegreeData.ofConservation`
packages into a `ProperMapDegreeData f` — and from there the proven
connectedness/nonnegativity reductions give the proper-map-degree existential
that `Jacobians.exists_properMapDegree` expects.  This is the exact wiring the
parent invokes; the only remaining input is the construction of the patching
supply (the genuine §17.9 analytic content, whose per-chart core is delivered
complete above as `Planar.orderSum_eq_of_analyticOrder`). -/

/-- **`ProperMapDegreeData f` from the multiplicity-patching supply.** -/
def properMapDegreeData_of_pointwiseMultiplicityPatching
    (f : MeromorphicFunction X)
    (h : ∀ w₀ : RiemannSphere, MultiplicityPatchingData f w₀) :
    Jacobians.ProperMapDegree.ProperMapDegreeData f :=
  ProperMapDegreeData.ofConservation f (isLocallyConstant_N_of_pointwiseMultiplicityPatching f h)

/-- **`zerosCount = polesCount`** (the argument-principle equality) from the
multiplicity-patching supply, via the connectedness globalization. -/
theorem zerosCount_eq_polesCount_of_pointwiseMultiplicityPatching
    (f : MeromorphicFunction X)
    (h : ∀ w₀ : RiemannSphere, MultiplicityPatchingData f w₀) :
    zerosCount f = polesCount f :=
  Jacobians.ProperMapDegree.zerosCount_eq_polesCount_of_properMapDegreeData f
    (properMapDegreeData_of_pointwiseMultiplicityPatching f h)

/-- **The proper-map-degree existential** (the exact shape of
`Jacobians.exists_properMapDegree`: a common `d : ℕ` with `zerosCount f = d =
polesCount f`) from the multiplicity-patching supply. -/
theorem exists_properMapDegree_of_pointwiseMultiplicityPatching
    (f : MeromorphicFunction X)
    (h : ∀ w₀ : RiemannSphere, MultiplicityPatchingData f w₀) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) :=
  Jacobians.ProperMapDegree.exists_properMapDegree_of_properMapDegreeData f
    (properMapDegreeData_of_pointwiseMultiplicityPatching f h)

end Jacobians.MultiplicityPatching

end
