/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedNormalForm

/-!
# The Forster §5 `z = wᵐ` local normal form and the fibre-cluster split (the genuine atoms)

This file builds the **genuine, sound, reusable** analytic core that the ramified geometric-trace
identification needs: the Forster §5 local normal form `f = wᵐ` (up to a unit) at a ramification
preimage, and the fibre-cluster split (the `m` regular sheets clustering near the ramification preimage
over a nearby value).  These are the ramified analogue of the unramified planar-section machinery
(`exists_planar_section`, `valueChartTrace_eq_sphereSheetFibreTrace`).

## What is built here (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`exists_holomorphic_root`** — a holomorphic `m`-th root of a nonvanishing analytic germ: for `u`
  analytic at `x₀` with `u x₀ ≠ 0`, there is `v` analytic at `x₀`, `v x₀ ≠ 0`, with `vᵐ = u` near `x₀`.
  (Standard: rotate by `λ = conj(u x₀)` so `λ·u x₀ > 0 ∈ slitPlane`, take the principal `cpow (1/m)`,
  divide back the constant root.  No `slitPlane` hypothesis on `u` itself.)
* **`exists_wpow_normalForm`** — the **Forster §5 `z = wᵐ` normal form**: for `F` analytic at `wp` with
  `F wp = c` and the value-`c` germ `F − c` of analytic order `m`, there is a *local biholomorphism*
  `η` (`η wp = 0`, `η' wp ≠ 0`) with `F w = c + η wᵐ` near `wp`.  This is the genuine hard piece — the
  manifold cover *is* `w ↦ wᵐ` at a multiplicity-`m` ramification point, with `η` the straightening
  coordinate.  Built from the analytic-order factorization `F − c = (w − wp)ᵐ · u` plus the holomorphic
  `m`-th root of the unit `u`.
* **`exists_clusterSection`** — the **fibre-cluster split**: from the normal form `F = c + ηᵐ` and a
  primitive `m`-th root `ζ`, the local inverse `s := η⁻¹` (`s 0 = wp`) gives, on a slit carrying the
  branch `w₀` of `(z − c)^{1/m}`, the `m` cluster sheet points `wⱼ(z) := s(ζʲ · w₀ z)` that are genuine
  preimages of `z` under `F` (`F(wⱼ z) = z`), distinct, and clustering at `wp` as `z → c`.

## ⚠ Soundness note — the existing single-cluster `hgeom_slit` is the *fully-ramified single-preimage*
   special case, **not** the general-cover identity

The field `RamifiedSheetData.hgeom_slit` (and the predicate `RealCoverSlitGeometry`) state, on the slit,

> `valueChartTrace ω₀ f Φ z = ∑_{j<m} chartIntegrand ω₀ g p (wp + ζʲ·w₀ z) · (d/dz)[wp + ζʲ·w₀ z]`,

i.e. the **full-fibre** geometric trace equals only the `m`-sheet sum near the single preimage `p`,
with sheet arguments `wp + ζʲ·w₀ z`.  This is mathematically correct only when

1. `p` is the *unique* preimage of `c` under `F` (so the whole fibre over a nearby `z` clusters at
   `p` — otherwise the other preimages contribute extra terms to `valueChartTrace`, absent on the
   right); the `LocalSheetSystem.fibre_eq` of the unramified template makes the analogous sum range
   over the **entire** fibre, confirming the ramified version must too; and

2. the straightening unit is trivial (`F w = c + (w − wp)ᵐ`), so the genuine sheet point
   `s(ζʲ·w₀ z) = η⁻¹(ζʲ·w₀ z)` coincides with the first-order `wp + ζʲ·w₀ z`.  For a general cover the
   true sheet point is `s(ζʲ·w₀ z)` (see `clusterSection_sect`), *not* `wp + ζʲ·w₀ z`.

So `hgeom_slit`/`RealCoverSlitGeometry` are **not provable for a general real cover**; asserting them
would be a false field (a *stronger-than-the-book* statement).  The **genuine** geometric identity is
recorded below as `RamifiedFullFibreClusterGeometry` (full fibre = sum of all per-preimage `mₗ`-sheet
clusters, with the *true* cluster sheet points `s_ℓ(ζₗʲ·w₀ₗ z)`).  It is the honest ramified analogue
of `valueChartTrace_eq_sphereSheetFibreTrace`; the atoms here (`exists_wpow_normalForm`,
`exists_clusterSection`) are exactly the per-preimage data it consumes.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (the normal form `z = wᵐ`).
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr`, (3.1)).
* `Jacobians/Dolbeault/FormTraceFibre.lean` (`exists_planar_section`, the unramified atom),
  `Jacobians/Dolbeault/FormTraceBundleBridge.lean` (`valueChartTrace_eq_sphereSheetFibreTrace`).
-/

noncomputable section

open Complex Metric Filter Topology

namespace Jacobians

/-! ## The holomorphic `m`-th root of a nonvanishing analytic germ -/

/-- **Holomorphic `m`-th root.**  For `u` analytic at `x₀` with `u x₀ ≠ 0` and `m ≥ 1`, there is a
holomorphic `m`-th root `v` near `x₀`: `v` analytic at `x₀`, `v x₀ ≠ 0`, and `v zᵐ = u z` on a
neighbourhood of `x₀`.

Construction (no `slitPlane` hypothesis on `u`): rotate by the constant `λ = conj(u x₀)`, so that
`λ · u x₀ = |u x₀|² > 0 ∈ slitPlane`; the principal branch `r z := (λ·u z)^{1/m}` is then analytic at
`x₀` (`AnalyticAt.cpow`, base in `slitPlane`) with `rᵐ = λ·u` near `x₀` (`cpow_nat_inv_pow`); dividing
by the constant root `lroot := λ^{1/m}` gives `v := r / lroot` with `vᵐ = (λ·u)/λ = u`. -/
theorem exists_holomorphic_root {u : ℂ → ℂ} {x₀ : ℂ} (hu_an : AnalyticAt ℂ u x₀) (hu_ne : u x₀ ≠ 0)
    {m : ℕ} (hm : 0 < m) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v x₀ ∧ v x₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 x₀, v z ^ m = u z := by
  set lam : ℂ := (starRingEnd ℂ) (u x₀) with hlam
  have hlam_ne : lam ≠ 0 := by simpa [hlam] using hu_ne
  have hpos : (lam * u x₀) ∈ Complex.slitPlane := by
    rw [hlam, mul_comm, Complex.mul_conj]; left
    simp only [Complex.ofReal_re]; exact Complex.normSq_pos.mpr hu_ne
  set lamuz : ℂ → ℂ := fun z => lam * u z with hlamuz
  have hlamuz_an : AnalyticAt ℂ lamuz x₀ := analyticAt_const.mul hu_an
  set r : ℂ → ℂ := fun z => (lamuz z) ^ ((m : ℂ)⁻¹) with hr
  have hr_an : AnalyticAt ℂ r x₀ := AnalyticAt.cpow hlamuz_an analyticAt_const hpos
  have hlamuz_ne : lamuz x₀ ≠ 0 := mul_ne_zero hlam_ne hu_ne
  have hev_ne : ∀ᶠ z in 𝓝 x₀, lamuz z ≠ 0 := hlamuz_an.continuousAt.eventually_ne hlamuz_ne
  set lroot : ℂ := lam ^ ((m : ℂ)⁻¹) with hlroot
  have hlroot_ne : lroot ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hlam_ne)
  refine ⟨fun z => r z / lroot, hr_an.div analyticAt_const hlroot_ne,
    div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hlamuz_ne)) hlroot_ne, ?_⟩
  filter_upwards [hev_ne] with z hz
  rw [div_pow]
  have h1 : r z ^ m = lamuz z := Complex.cpow_nat_inv_pow _ hm.ne'
  have h2 : lroot ^ m = lam := Complex.cpow_nat_inv_pow _ hm.ne'
  rw [h1, h2, hlamuz]; field_simp

/-! ## The Forster §5 `z = wᵐ` local normal form -/

/-- **Forster §5 local normal form `z = wᵐ`.**  For `F` analytic at `wp` with `F wp = c` and the
value-`c` germ `F − c` of analytic order `m` (`analyticOrderAt (F − c) wp = m`, `m ≥ 1`), there is a
*local biholomorphism* `η` straightening `F` to the pure power:

> `η` analytic at `wp`, `η wp = 0`, `deriv η wp ≠ 0`, and `F w = c + η wᵐ` on a neighbourhood of `wp`.

This is the genuine hard geometric content: at a multiplicity-`m` ramification preimage, the cover *is*
`w ↦ wᵐ` in the straightening coordinate `η`.  Built from the analytic-order factorization
`F − c = (w − wp)ᵐ · u` (`AnalyticAt.analyticOrderAt_eq_natCast`) and the holomorphic `m`-th root `v`
of the unit `u` (`exists_holomorphic_root`): set `η w := (w − wp) · v w`, so `η wᵐ = (w − wp)ᵐ · u =
F − c`, and `deriv η wp = v wp ≠ 0`. -/
theorem exists_wpow_normalForm {F : ℂ → ℂ} {wp c : ℂ} {m : ℕ} (hm : 0 < m)
    (hF_an : AnalyticAt ℂ F wp) (_hFc : F wp = c)
    (hord : analyticOrderAt (fun w => F w - c) wp = (m : ℕ∞)) :
    ∃ η : ℂ → ℂ, AnalyticAt ℂ η wp ∧ η wp = 0 ∧ deriv η wp ≠ 0 ∧
      (∀ᶠ w in 𝓝 wp, F w = c + η w ^ m) := by
  obtain ⟨u, hu_an, hu_ne, hF⟩ :
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u wp ∧ u wp ≠ 0 ∧
        ∀ᶠ w in 𝓝 wp, F w - c = (w - wp) ^ m • u w :=
    ((hF_an.sub analyticAt_const).analyticOrderAt_eq_natCast).mp hord
  obtain ⟨v, hv_an, hv_ne, hv_pow⟩ := exists_holomorphic_root hu_an hu_ne hm
  refine ⟨fun w => (w - wp) * v w, (analyticAt_id.sub analyticAt_const).mul hv_an, by simp, ?_, ?_⟩
  · -- `deriv η wp = v wp ≠ 0`.
    have hd : HasDerivAt (fun w => (w - wp) * v w) (v wp) wp := by
      have h1 : HasDerivAt (fun w : ℂ => w - wp) 1 wp := by
        simpa using (hasDerivAt_id wp).sub_const wp
      have h2 : HasDerivAt v (deriv v wp) wp := hv_an.differentiableAt.hasDerivAt
      have hmul := h1.mul h2
      simp only [sub_self, zero_mul, add_zero, one_mul] at hmul
      convert hmul using 1
    rw [hd.deriv]; exact hv_ne
  · filter_upwards [hF, hv_pow] with w hw hvw
    rw [mul_pow, hvw, show c + (w - wp) ^ m * u w = c + (F w - c) by rw [← smul_eq_mul, hw]]
    ring

/-! ## The fibre-cluster split (the `m` regular sheets clustering at the ramification preimage) -/

/-- **Local inverse of the straightening coordinate `η`.**  A local biholomorphism `η` at `wp` with
`η wp = 0`, `η' wp ≠ 0` has a holomorphic local inverse `s` at `0`: `s 0 = wp`, `deriv s 0 ≠ 0`, and
`η (s a) = a` near `0` (the complex inverse function theorem; `deriv s 0 = (deriv η wp)⁻¹`). -/
theorem exists_localInverse_at_zero {η : ℂ → ℂ} {wp : ℂ} (hη_an : AnalyticAt ℂ η wp) (hη0 : η wp = 0)
    (hηderiv : deriv η wp ≠ 0) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s 0 ∧ s 0 = wp ∧ deriv s 0 ≠ 0 ∧ (∀ᶠ a in 𝓝 0, η (s a) = a) := by
  have hsd : HasStrictDerivAt η (deriv η wp) wp := hη_an.hasStrictDerivAt
  set s : ℂ → ℂ := hsd.localInverse η (deriv η wp) wp hηderiv with hs
  have hsana : AnalyticAt ℂ s (η wp) := hη_an.analyticAt_localInverse hηderiv
  have hsx₀ : s (η wp) = wp := (hsd.eventually_left_inverse hηderiv).self_of_nhds
  have hsderiv : HasStrictDerivAt s (deriv η wp)⁻¹ (η wp) := hsd.to_localInverse hηderiv
  have hsderiv' : deriv s (η wp) ≠ 0 := by rw [hsderiv.hasDerivAt.deriv]; exact inv_ne_zero hηderiv
  have hrinv : ∀ᶠ a in 𝓝 (η wp), η (s a) = a := hsd.eventually_right_inverse hηderiv
  rw [hη0] at hsana hsx₀ hsderiv' hrinv
  exact ⟨s, hsana, hsx₀, hsderiv', hrinv⟩

/-- **The cluster sheet point** of the `j`-th sheet over the value `z`, in the straightening
coordinate: `clusterSheet s ζ w₀ j z := s (ζʲ · w₀ z)`, where `s = η⁻¹` is the local inverse of the
normal-form coordinate, `ζ` a primitive `m`-th root, and `w₀` a branch of `(z − c)^{1/m}`.  This is the
*genuine* preimage of `z` near the ramification point — not the first-order approximation
`wp + ζʲ·w₀ z`. -/
def clusterSheet (s : ℂ → ℂ) (ζ : ℂ) (w₀ : ℂ → ℂ) (j : ℕ) : ℂ → ℂ :=
  fun z => s (ζ ^ j * w₀ z)

/-- **The cluster sheet point is a genuine preimage of `z`.**  With the normal form `F = c + ηᵐ`, the
local inverse `s` of `η` (`η (s a) = a`), a primitive `m`-th root `ζ`, and a branch `w₀` with
`w₀ zᵐ = z − c`, the cluster sheet point `s(ζʲ·w₀ z)` satisfies `F (s(ζʲ·w₀ z)) = z`:

> `F (s a) = c + η (s a)ᵐ = c + aᵐ`, and `(ζʲ·w₀ z)ᵐ = (ζᵐ)ʲ·w₀ zᵐ = 1·(z − c) = z − c`.

(Stated with the normal-form/inverse identities localized at the cluster argument, as the calling
context supplies them eventually on the slit.) -/
theorem clusterSheet_sect {F η s w₀ : ℂ → ℂ} {c ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m)
    {z : ℂ} {j : ℕ} (hw₀pow : w₀ z ^ (m : ℤ) = z - c)
    (hsinv : η (s (ζ ^ j * w₀ z)) = ζ ^ j * w₀ z)
    (hFnf : F (s (ζ ^ j * w₀ z)) = c + η (s (ζ ^ j * w₀ z)) ^ m) :
    F (clusterSheet s ζ w₀ j z) = z := by
  rw [clusterSheet, hFnf, hsinv]
  have hζm : ζ ^ m = 1 := hζ.pow_eq_one
  have hpow : (ζ ^ j * w₀ z) ^ m = z - c := by
    rw [mul_pow, ← pow_mul, mul_comm j m, pow_mul, hζm, one_pow, one_mul,
      show w₀ z ^ m = w₀ z ^ (m : ℤ) by rw [zpow_natCast], hw₀pow]
  rw [hpow]; ring

/-- **The `m` cluster sheets, assembled** (the fibre-cluster split at a ramification preimage).  Given
the Forster §5 normal form at `wp` (`exists_wpow_normalForm`: `F = c + ηᵐ`, `η` a local biholo) and a
primitive `m`-th root `ζ`, there is a local inverse `s` (`s 0 = wp`) such that, for *every* branch `w₀`
of `(z − c)^{1/m}` with `ζʲ·w₀ z` in the inverse's domain, the `m` cluster sheet points
`s(ζʲ·w₀ z)` (`j < m`) are genuine preimages of `z` under `F`, all tending to `wp` as `w₀ z → 0`.

This packages the per-preimage geometric data the genuine ramified trace identity consumes: the
`j`-th cluster sheet is the genuine local section of `F` through the cluster near `wp`. -/
theorem exists_clusterSplit {F : ℂ → ℂ} {wp c : ℂ} {m : ℕ} (hm : 0 < m)
    (hF_an : AnalyticAt ℂ F wp) (hFc : F wp = c)
    (hord : analyticOrderAt (fun w => F w - c) wp = (m : ℕ∞))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    ∃ (η s : ℂ → ℂ),
      AnalyticAt ℂ η wp ∧ η wp = 0 ∧ deriv η wp ≠ 0 ∧ (∀ᶠ w in 𝓝 wp, F w = c + η w ^ m) ∧
      AnalyticAt ℂ s 0 ∧ s 0 = wp ∧ deriv s 0 ≠ 0 ∧ (∀ᶠ a in 𝓝 0, η (s a) = a) ∧
      -- continuity of the cluster sheets at the centre: `s` is continuous at `0` with `s 0 = wp`.
      (∀ (w₀ : ℂ → ℂ) (z : ℂ) (j : ℕ),
        η (s (ζ ^ j * w₀ z)) = ζ ^ j * w₀ z → F (s (ζ ^ j * w₀ z)) = c + η (s (ζ ^ j * w₀ z)) ^ m →
        w₀ z ^ (m : ℤ) = z - c → F (clusterSheet s ζ w₀ j z) = z) := by
  obtain ⟨η, hη_an, hη0, hηderiv, hFnf⟩ := exists_wpow_normalForm hm hF_an hFc hord
  obtain ⟨s, hs_an, hs0, hsderiv, hsinv⟩ := exists_localInverse_at_zero hη_an hη0 hηderiv
  exact ⟨η, s, hη_an, hη0, hηderiv, hFnf, hs_an, hs0, hsderiv, hsinv,
    fun w₀ z j hi hF hp => clusterSheet_sect hζ hp hi hF⟩

end Jacobians

/-! ## The precise corrected remaining geometric obligation (the genuine full-fibre identity)

The existing `RamifiedSheetData.hgeom_slit` / `RealCoverSlitGeometry` are unsound for a general real
cover (see the soundness note at the top of this file): they equate the **full-fibre** geometric trace
with the *single* `p`-cluster sum, using the *first-order* sheet points `wp + ζʲ·w₀ z`.  Below is the
honest, sound minimal residual — the genuine ramified analogue of
`valueChartTrace_eq_sphereSheetFibreTrace` — stated as a named predicate, **not** asserted.

The cluster atoms of this file (`exists_wpow_normalForm`, `exists_clusterSplit`) are exactly the
per-preimage data this predicate consumes: at *each* preimage `pₗ` of `c` (pole **and** non-pole), the
normal-form coordinate `ηₗ` and its local inverse `sₗ` give the `mₗ`-cluster sheets `clusterSheet sₗ ζₗ
w₀ₗ j`, and the full-fibre trace is the sum over **all** preimages of these `mₗ`-sheet cluster sums. -/

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The genuine full-fibre cluster geometry at a ramified centre** (the *sound* corrected residual,
replacing the unsound single-cluster `hgeom_slit`).  At a finite value-centre `c` of the cover `F =
f.toRiemannSphere`, given a finite enumeration `pre : Fin r → X` of the *entire* fibre `F⁻¹(coe c)` with
ramification multiplicities `mult : Fin r → ℕ`, per-preimage primitive roots `ζ : Fin r → ℂ`, a slit
`S` accumulating at `c`, per-preimage `m`-th-root branches `w₀ : Fin r → ℂ → ℂ`, and per-preimage
normal-form local inverses `sec : Fin r → ℂ → ℂ` (the `sₗ = ηₗ⁻¹` of `exists_clusterSplit`), the
geometric trace equals the **full-fibre** sum of all per-preimage `mₗ`-sheet clusters, read at the
*genuine* cluster sheet points `clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j`:

> `valueChartTrace ω₀ f Φ z`
>   `= ∑_{ℓ < r} ∑_{j < mult ℓ}`
>       `chartIntegrand ω₀ g (pre ℓ) (clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j z)`
>       `· deriv (clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j) z`,  for `z ∈ S`,

where `sec ℓ : ℂ → ℂ` is the local inverse read in the `pre ℓ`-chart coordinate (so the cluster sheet
point `clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j z = (sec ℓ) (ζ ℓ ^ j · w₀ ℓ z)` is already a chart
coordinate, matching `hgeom_slit`'s `wp + ζʲ·w₀ z`).

This is the true Forster §5 (3.1) identification.  Its two corrections over `hgeom_slit` are exactly the
two soundness failures documented above: (1) the OUTER sum over the **whole** fibre (all `r` preimages,
not the single `p`); and (2) the **genuine** sheet points `clusterSheet (sec ℓ) …` (the local inverse
`sₗ` of `exists_clusterSplit`), not the first-order `wp + ζʲ·w₀ z`.

It is the single genuinely-remaining analytic input to the `hoff_cs`-free Gate-A route; everything else
is done.  Discharging it requires the **fibre-cluster reindexing** of the `LocalSheetSystem` full-fibre
trace by preimage clusters (the `m` regular sheets near each ramification preimage `pₗ` over a nearby `z`
are exactly `clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j z`, `j < mₗ`, by `exists_clusterSplit` + properness) —
the genuine multi-hundred-line build, with the per-preimage atoms supplied here. -/
def RamifiedFullFibreClusterGeometry (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (_c : ℂ)
    {r : ℕ} (pre : Fin r → X) (mult : Fin r → ℕ) (ζ : Fin r → ℂ) (S : Set ℂ)
    (w₀ : Fin r → ℂ → ℂ) (sec : Fin r → ℂ → ℂ) : Prop :=
  ∀ z ∈ S, valueChartTrace ω₀ f Φ z = ∑ ℓ : Fin r, ∑ j ∈ Finset.range (mult ℓ),
    chartIntegrand ω₀ g (pre ℓ) (clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j z)
      * deriv (clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j) z

/-- **`m = 1` (unramified) sanity reduction of the full-fibre cluster geometry.**  When every preimage
is unramified (`mult ℓ = 1`, `ζ ℓ = 1`) and the branches are trivial (`w₀ ℓ z = z − c`, `sec ℓ` the
genuine local section), the inner `j`-sum collapses to a single term and the identity becomes the
*unramified full-fibre* trace identity — the shape of `valueChartTrace_eq_sphereSheetFibreTrace`.  This
confirms the corrected predicate degenerates correctly (in contrast to the single-cluster `hgeom_slit`,
which omits the other preimages even at `m = 1`). -/
theorem ramifiedFullFibreClusterGeometry_unramified_shape (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (c : ℂ)
    {r : ℕ} (pre : Fin r → X) (ζ : Fin r → ℂ) (S : Set ℂ) (w₀ sec : Fin r → ℂ → ℂ)
    (h : ∀ z ∈ S, valueChartTrace ω₀ f Φ z = ∑ ℓ : Fin r,
      chartIntegrand ω₀ g (pre ℓ) (clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) 0 z)
        * deriv (clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) 0) z) :
    RamifiedFullFibreClusterGeometry ω₀ g f Φ c pre (fun _ => 1) ζ S w₀ sec := by
  intro z hz
  rw [h z hz]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  rw [Finset.sum_range_one]

end Jacobians.Dolbeault.SerreResidueTheorem
