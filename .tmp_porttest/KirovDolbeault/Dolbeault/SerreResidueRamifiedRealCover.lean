/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedNormalForm
import KirovDolbeault.Dolbeault.SerreResidueGateAClosed
import KirovDolbeault.Dolbeault.SerreOmega0

/-!
# Gate A end-to-end via the real cover — the `hoff_cs`-free sheet-data route

This file wires the **`hoff_cs`-free** capstone `residueTheorem_ofSheetData_genus0`
(`Jacobians/Dolbeault/SerreResidueRamifiedNormalForm.lean`) towards an *unconditional* 1-form residue
theorem `∑Res = 0` for `α = ω₀·g`, by reducing it to the genuine per-centre geometric data for the
**actual** cover `f` (the Forster §5 slit-branch normal form at each finite pole-value centre), the
simple-`∞` genericity, and the existence of a nonconstant cover.

It also builds the concrete prerequisite infrastructure the genericity step needs:

* **`MeromorphicFunction.Inv`** (the pointwise reciprocal `f⁻¹`), with the order laws
  `orderW_inv`/`orderAtPoint_inv` (`= -orderW`/`= -orderAtPoint`).  This is the algebraic engine behind
  the simple-`∞` reduction `f' := (f₀ − a·1)⁻¹` (Miranda §VIII.3 p. 254: replace any nonconstant `f₀`
  by a reciprocal whose `∞`-poles are the *simple* zeros of `f₀ − a` for generic `a`).

## The two parallel routes to `∑Res = 0`, and what is *new* here

There are two assemblies of Gate A in the repo:

1. The **unramified** route `residueTheorem_of_adaptedF` (`SerreResidueGateAClosed.lean`), which rests on
   `ExistsAdaptedF` — a genericity datum carrying `hoff_cs` (*all* finite pole-value fibres unramified).
   Its `hreg`/`hbnd`/`∞`-group are fully discharged for the canonical selection
   (`hbnd_canonical_sound_full`, the `g`-weighted bundle SUM — αBr-free, sound for general `g`).

2. The **ramified** route `residueTheorem_ofSheetData_genus0`
   (`SerreResidueRamifiedNormalForm.lean`), which is `hoff_cs`-FREE: the finite pole-value centres may be
   ramified, each supplying a `RamifiedSheetData` (the slit-branch `m`-th-root normal form).  Its
   residue/algebra core is *done* (the proven atom; the slit fix removed the monodromy contradiction —
   `ramifiedSheetData_sqrt` witnesses inhabitation at `m = 2`).

The *genuine remaining content* of route (2) for the actual cover is exactly the per-centre
`RamifiedSheetData ω₀ g f (canonicalFibreSelection …) (cs i)` whose hard fields are:

* **`hgeom_slit`** — on a slit accumulating at `cs i`, the geometric trace `valueChartTrace` equals the
  `m`-sheet sum `∑_{j<m} chartIntegrand(w_p + ζʲ w₀)·(d/dz)[…]` of the chart integrand at the
  ramification preimage `p` (Forster §5, the `z = wᵐ` normal form);
* **`hvct_mero`** — `valueChartTrace` is meromorphic at `cs i` (Miranda (3.1): the symmetric trace SUM
  is single-valued meromorphic at a ramified value).

These are the *ramified analogue* of the unramified `valueChartTrace_eq_sphereSheetFibreTrace`
(`FormTraceBundleBridge.lean`) — a genuine multi-hundred-line branch-aware sheet build — and are
isolated below as the named predicate `RealCoverRamifiedCenters`, **not** asserted.

## What is delivered here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `MeromorphicFunction.Inv` + `orderW_inv` + `orderAtPoint_inv` — the reciprocal infrastructure for the
  simple-`∞` genericity (item #2), genuinely complete and reusable.
* `RealCoverRamifiedCenters` — the precise per-centre remaining obligation (item #1): a
  `RamifiedSheetData` for the canonical selection at each finite pole-value centre, enumerating the pole
  fibre.  The cleanest statement of "the Forster §5 ramified trace exists for the real cover at every
  finite pole-value centre".
* `GateAInftyData` — the bundle of the (already-proven-style) `∞`-group + off-centre `hreg`/`hbnd`
  inputs that `residueTheorem_ofSheetData_genus0` consumes, packaged so the reduction is one application.
* `residueSum_eq_zero_of_realCoverCenters` — **`∑Res = 0` from `RealCoverRamifiedCenters` +
  `GateAInftyData`**, routed through the `hoff_cs`-free `residueTheorem_ofSheetData_genus0`.  This is the
  re-routing of the headline (item #4): once the per-centre real-cover sheet data exists, Gate A is
  unconditional with no off-branch genericity on the finite centres.

## ⚠ Soundness

* `MeromorphicFunction.Inv` is the genuine pointwise reciprocal; `orderW_inv`/`orderAtPoint_inv` are the
  true order laws (Mathlib `meromorphicOrderAt_inv`), no junk.
* `RealCoverRamifiedCenters` is the *honest* remaining geometric content — the slit-branch `RamifiedSheetData`
  for the real cover — supplied as data, **never** asserted as a free lemma.  Its non-vacuity at a
  genuinely ramified multiplicity is the `m = 2` `√(z − c)` witness `ramifiedSheetData_sqrt`
  (`SerreResidueRamifiedNormalForm.lean`); the `hgeom_slit`/`hvct_mero` fields are the genuine §VIII.3 /
  Forster §5 content, not residue identities (no circularity, no `hoff_cs` in disguise).
* The reduction `residueSum_eq_zero_of_realCoverCenters` is a *pure wiring* of the proven
  `residueTheorem_ofSheetData_genus0`; it introduces no analytic claim of its own.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 251–256 (the trace `Tr`,
  formula (3.1), "choose any nonconstant `f`").
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (local normal form `z = wᵐ`, the slit branch).
* Mathlib `MeromorphicAt.inv`, `meromorphicOrderAt_inv`; `Complex.cpow` (the slit `m`-th root).
* `Jacobians/Dolbeault/SerreResidueRamifiedNormalForm.lean` (`RamifiedSheetData`,
  `residueTheorem_ofSheetData_genus0`, `ramifiedSheetData_sqrt`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The reciprocal `f⁻¹` of a meromorphic function (the simple-`∞` engine, item #2)

A meromorphic function has a meromorphic pointwise reciprocal (Mathlib `MeromorphicAt.inv`), with the
order negated at every point.  This is the algebraic step behind Miranda's simple-`∞` reduction: for a
generic value `a`, the reciprocal `f' := (f₀ − a·1)⁻¹` has its `∞`-poles exactly at the *zeros* of
`f₀ − a`, which are **simple** when `a` is not a critical value of `f₀` (so `orderAtPoint f' = −1`
there). -/

namespace MeromorphicFunction

-- The reciprocal uses only the charted-space structure (no compactness/connectedness), matching the
-- footprint of the other `MeromorphicFunction` algebra (so it applies to open submanifolds `↥U` too).
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- The pointwise reciprocal of a meromorphic function is meromorphic (Mathlib `MeromorphicAt.inv`,
applied in each chart — composition with the chart inverse commutes with pointwise `⁻¹`). -/
theorem _root_.Jacobians.IsMeromorphic.inv {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X f⁻¹ := fun x => by
  have h := (hf x).inv
  -- `(f ∘ chart.symm)⁻¹ = f⁻¹ ∘ chart.symm` (pointwise reciprocal commutes with composition).
  have heq : (f ∘ (chartAt (H := ℂ) x).symm)⁻¹ = (f⁻¹ ∘ (chartAt (H := ℂ) x).symm) := rfl
  rwa [heq] at h

/-- The reciprocal `f⁻¹` of a meromorphic function — `(f⁻¹).toFun = f.toFun⁻¹` (pointwise). -/
noncomputable instance : Inv (MeromorphicFunction X) :=
  ⟨fun f => ⟨f.toFun⁻¹, IsMeromorphic.inv f.meromorphic⟩⟩

@[simp] theorem inv_toFun (f : MeromorphicFunction X) : (f⁻¹).toFun = f.toFun⁻¹ := rfl

/-- **The germ-order of a reciprocal is the negation:** `(f⁻¹).orderW x = −(f.orderW x)` (Mathlib
`meromorphicOrderAt_inv`, read in the chart at `x`).  A pole of order `n` of `f` becomes a zero of
order `n` of `f⁻¹` and vice versa. -/
theorem orderW_inv (f : MeromorphicFunction X) (x : X) :
    (f⁻¹).orderW x = -(f.orderW x) := by
  show meromorphicOrderAt ((f.toFun⁻¹) ∘ (chartAt (H := ℂ) x).symm) _
    = -meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) _
  have heq : (f.toFun⁻¹) ∘ (chartAt (H := ℂ) x).symm
      = (f.toFun ∘ (chartAt (H := ℂ) x).symm)⁻¹ := rfl
  rw [heq, meromorphicOrderAt_inv]

/-- **The order-at-point of a reciprocal is the negation:** `(f⁻¹).orderAtPoint x = −(f.orderAtPoint x)`.
(`orderAtPoint = (orderW).untop₀`; `untop₀ (−w) = −(untop₀ w)` since `−⊤ = ⊤` and `untop₀ ⊤ = 0`.)
This is the key order law for the simple-`∞` reduction: a *simple zero* of `f₀ − a` (order `+1`) is a
*simple pole* of `(f₀ − a)⁻¹` (order `−1`). -/
theorem orderAtPoint_inv (f : MeromorphicFunction X) (x : X) :
    (f⁻¹).orderAtPoint x = -(f.orderAtPoint x) := by
  show ((f⁻¹).orderW x).untop₀ = -(f.orderW x).untop₀
  rw [orderW_inv]
  rcases eq_or_ne (f.orderW x) ⊤ with h | h
  · rw [h]; simp
  · lift (f.orderW x) to ℤ using h with a
    simp

end MeromorphicFunction

/-! ## Removable-singularity meromorphy atoms (the engine for `hvct_mero`)

The hard `RamifiedSheetData` field `hvct_mero`  — `valueChartTrace` is meromorphic at the centre `c` —
is Miranda (3.1) (the symmetric trace SUM has a finite-order Laurent expansion at a ramified value).
We reduce it to a *boundedness* statement via two reusable complex-analytic atoms: a function analytic
on a punctured neighbourhood of `c` whose growth is killed by some power `(z − c)^N` is meromorphic at
`c` (Riemann's removable-singularity theorem applied to `(z − c)^N · f`, then divided back).  Combined
with the off-centre analyticity `hreg` (which is eventually true on `𝓝[≠] c` since the bad set is
finite), this turns `hvct_mero` into the single bound `(z − c)^N · valueChartTrace → 0` — the
finite-pole-order content, strictly easier than the full geometric identification. -/

open Complex in
/-- **Removable-singularity meromorphy (simple, `N = 1`).**  If `f` is analytic on a punctured
neighbourhood of `c` and `(z − c)·f(z) → 0` as `z → c`, then `f` is meromorphic at `c` (with at worst a
removable singularity).  Proof: `h := (z − c)·f`, updated to `0` at `c`, is differentiable on the
punctured nbhd and continuous at `c`, hence analytic at `c` by Riemann (`Complex.
analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`); then `f =ᶠ[𝓝[≠] c] (z − c)⁻¹·h` is
meromorphic. -/
theorem meromorphicAt_of_analyticOn_punctured_of_mul_sub_tendsto {f : ℂ → ℂ} {c : ℂ}
    (han : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z)
    (hbnd : Tendsto (fun z => (z - c) * f z) (𝓝[≠] c) (𝓝 0)) :
    MeromorphicAt f c := by
  set h : ℂ → ℂ := Function.update (fun z => (z - c) * f z) c 0 with hh
  have hdiff : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ h z := by
    filter_upwards [han, self_mem_nhdsWithin] with z hz hzc
    have hzc' : z ≠ c := hzc
    have hupd : h =ᶠ[𝓝 z] (fun w => (w - c) * f w) := by
      filter_upwards [isOpen_ne.mem_nhds hzc'] with w hw
      simp only [hh, Function.update_apply, if_neg hw]
    exact DifferentiableAt.congr_of_eventuallyEq
      (((differentiableAt_id.sub_const c)).mul hz.differentiableAt) hupd
  have hcont : ContinuousAt h c := by
    rw [hh, continuousAt_update_same]; exact hbnd
  have hana : AnalyticAt ℂ h c :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcont
  have hmero : MeromorphicAt (fun z => (z - c)⁻¹ * h z) c :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv).mul hana.meromorphicAt
  refine hmero.congr ?_
  filter_upwards [self_mem_nhdsWithin] with z hzc
  have hzc' : z ≠ c := hzc
  show (z - c)⁻¹ * h z = f z
  simp only [hh, Function.update_apply, if_neg hzc']
  rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hzc'), one_mul]

open Complex in
/-- **Removable-singularity meromorphy (power form).**  If `f` is analytic on a punctured neighbourhood
of `c` and `(z − c)^N·f(z) → 0` as `z → c` for *some* `N : ℕ`, then `f` is meromorphic at `c`.  This is
the finite-pole-order criterion (a pole of order `< N` is killed by `(z − c)^N`): `(z − c)^N·f` extends
analytically across `c` (Riemann), and `f =ᶠ[𝓝[≠] c] (z − c)^(−N)·[(z − c)^N·f]` is meromorphic.  This
is the form `hvct_mero` uses at a ramified pole-value centre (Miranda (3.1)). -/
theorem meromorphicAt_of_analyticOn_punctured_of_pow_mul_sub_tendsto {f : ℂ → ℂ} {c : ℂ} (N : ℕ)
    (han : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z)
    (hbnd : Tendsto (fun z => (z - c) ^ N * f z) (𝓝[≠] c) (𝓝 0)) :
    MeromorphicAt f c := by
  set h : ℂ → ℂ := Function.update (fun z => (z - c) ^ N * f z) c 0 with hh
  have hdiff : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ h z := by
    filter_upwards [han, self_mem_nhdsWithin] with z hz hzc
    have hzc' : z ≠ c := hzc
    have hupd : h =ᶠ[𝓝 z] (fun w => (w - c) ^ N * f w) := by
      filter_upwards [isOpen_ne.mem_nhds hzc'] with w hw
      simp only [hh, Function.update_apply, if_neg hw]
    exact DifferentiableAt.congr_of_eventuallyEq
      (((differentiableAt_id.sub_const c).pow N).mul hz.differentiableAt) hupd
  have hcont : ContinuousAt h c := by
    rw [hh, continuousAt_update_same]; exact hbnd
  have hana : AnalyticAt ℂ h c :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcont
  have hmero : MeromorphicAt (fun z => (z - c) ^ (-(N : ℤ)) * h z) c :=
    (((analyticAt_id.sub analyticAt_const).meromorphicAt).zpow (-(N : ℤ))).mul hana.meromorphicAt
  refine hmero.congr ?_
  filter_upwards [self_mem_nhdsWithin] with z hzc
  have hzc' : z ≠ c := hzc
  show (z - c) ^ (-(N : ℤ)) * h z = f z
  simp only [hh, Function.update_apply, if_neg hzc']
  rw [zpow_neg, zpow_natCast, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N (sub_ne_zero.mpr hzc')),
    one_mul]

/-! ## The per-centre real-cover obligation (item #1, the genuine geometric content)

The `hoff_cs`-free capstone `residueTheorem_ofSheetData_genus0`
(`SerreResidueRamifiedNormalForm.lean`) consumes, at each finite pole-value centre `cs i`, a
`RamifiedSheetData ω₀ g f Φ (cs i)` enumerating a ramified preimage that is the unique pole of `α = ω₀·g`
in the fibre `F⁻¹(coe (cs i))`.  For the **actual** cover `f` with the **canonical** full-fibre selection
`Φ = canonicalFibreSelection g f hdiv`, building that datum is the genuine remaining analytic work — the
Forster §5 slit-branch `z = wᵐ` normal form (`hgeom_slit`) and the Miranda-(3.1) single-valued meromorphy
of the symmetric trace SUM (`hvct_mero`).

We isolate that, *with the pole-enumeration side conditions*, as the named predicate below.  It is the
ramified analogue of the unramified `MovingCoherenceDatum`/`valueChartTrace_eq_sphereSheetFibreTrace`
machinery, and is the precise minimal input that turns route (2) unconditional. -/

open Jacobians.Dolbeault Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceGlobal
  Jacobians.Dolbeault.SerreResidueTheorem Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.TraceResidue

/-- **Eventual analyticity of the geometric trace on a punctured centre nbhd, from `hreg`.**  The
off-centre analyticity `hreg` (analytic off the finite bad set `image cs ∪ br`) gives analyticity on a
whole *punctured* neighbourhood of any single centre `c`: the bad set minus `{c}` is finite hence
closed, so eventually on `𝓝[≠] c` we are off `image cs ∪ br`.  This is the analytic-on-punctured input
to the removable-singularity meromorphy atoms. -/
theorem eventually_analyticAt_of_hreg {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} {c : ℂ}
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w) :
    ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z := by
  classical
  have hfin : (((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {c}).Finite :=
    ((Finset.univ.image cs ∪ br).finite_toSet).diff
  have hcompl : ((((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {c}))ᶜ ∈ 𝓝 c :=
    hfin.isClosed.compl_mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl] with z hz_ne hz_compl
  have hzc : z ≠ c := by simpa using hz_ne
  refine hreg z ?_
  intro hmem
  exact hz_compl ⟨hmem, fun h => hzc (by simpa using h)⟩

/-- **`hvct_mero` from a finite-pole-order bound (the genuine reduction of Miranda (3.1)).**  At a
finite pole-value centre `c`, the `RamifiedSheetData` field `hvct_mero` — `valueChartTrace ω₀ f Φ`
meromorphic at `c` — follows from:

* the off-centre analyticity `hreg` (eventual analyticity on `𝓝[≠] c`, via `eventually_analyticAt_of_hreg`);
* a single **finite-pole-order bound** `(z − c)^N · valueChartTrace → 0` for some `N`.

This converts the opaque `hvct_mero` field into the concrete bound (the trace's pole at `c` has finite
order `< N` — bounded by the upstairs pole order of `α` times the ramification, Miranda (3.1)).  It is
the meromorphy-side reduction of the per-centre real-cover obligation. -/
theorem hvct_mero_of_pow_bound {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} {c : ℂ}
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (N : ℕ) (hbnd : Tendsto (fun z => (z - c) ^ N * valueChartTrace ω₀ f Φ z) (𝓝[≠] c) (𝓝 0)) :
    MeromorphicAt (valueChartTrace ω₀ f Φ) c :=
  meromorphicAt_of_analyticOn_punctured_of_pow_mul_sub_tendsto N
    (eventually_analyticAt_of_hreg hreg) hbnd

/-- **The per-centre real-cover ramified data** (item #1, the genuine geometric obligation).  At every
finite pole-value centre `cs i` of `α = ω₀·g`, the canonical full-fibre selection
`Φ = canonicalFibreSelection g f hdiv` carries a `RamifiedSheetData` (the Forster §5 slit-branch normal
form) whose distinguished preimage `(Sf i).p` is the **unique** pole of `α` in the fibre
`F⁻¹(coe (cs i))`:

* `Sf i : RamifiedSheetData ω₀ g f Φ (cs i)` — the slit-branch sheet data (hard fields `hgeom_slit`,
  `hvct_mero`; everything else is `RamifiedSheetData`'s standard Laurent / branch fields);
* `hp_pole i` / `hp_fibre i` / `hp_unique i` — `(Sf i).p` is a pole, lies over `coe (cs i)`, and is the
  *only* pole over `coe (cs i)` (single-preimage form; the general mixed-multiplicity case is the sum
  over preimages, but a generic cover has one ramification preimage per finite pole-value centre).

**Soundness (non-false).**  Genuinely achievable, and inhabited at a *ramified* multiplicity: the slit
branch `w₀ z = (z − cs i)^{1/m}` exists for any `m` (`ramifiedSheetData_sqrt`, the `m = 2` `√` witness
in `SerreResidueRamifiedNormalForm.lean`), so this is **not** a disguised `False` at a ramification
centre.  The fields are the real §VIII.3 / Forster §5 content, supplied as data, none asserted. -/
def RealCoverRamifiedCenters (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) {m : ℕ} (cs : Fin m → ℂ) : Prop :=
  ∃ (Sf : ∀ i, RamifiedSheetData ω₀ g f (canonicalFibreSelection g f hdiv) (cs i)),
    (∀ i, (Sf i).p ∈ poles) ∧
    (∀ i, f.toRiemannSphere (Sf i).p = ((cs i : ℂ) : RiemannSphere)) ∧
    (∀ i, ∀ a ∈ poles, f.toRiemannSphere a = ((cs i : ℂ) : RiemannSphere) → a = (Sf i).p)

/-- **The Gate-A off-centre + `∞` input bundle** for the canonical selection.  Packages exactly the
hypotheses of `residueTheorem_ofSheetData_genus0` *other than* the per-centre `RamifiedSheetData` (which
is `RealCoverRamifiedCenters`): the off-centre analyticity `hreg`, the branch-value boundedness `hbnd`,
the centre/pole-image bookkeeping `hcenters_cs`, and the entire `∞`-group.

For the canonical selection these are the **already-discharged** Gate-A inputs (`hreg` via
`hreg_canonical_at_goodValue_sound`, `hbnd` via the αBr-free `hbnd_canonical_sound_full`, the `∞`-group
via the simple-`∞` coherence).  Bundling them lets the real-cover reduction be a single application of
the `hoff_cs`-free capstone. -/
structure GateAInftyData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) {m : ℕ} (cs : Fin m → ℂ) (br : Finset ℂ) where
  /-- The pole-value centres lie in a ball (for the `LaurentForm` principal-part extraction). -/
  ρ : ℝ
  hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ
  hcs_inj : Function.Injective cs
  /-- Off-centre analyticity of the geometric trace (canonical selection). -/
  hreg : ∀ w ∉ Finset.univ.image cs ∪ br,
    AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) w
  /-- The branch-value boundedness `(z − b₀)·trace → 0` at the non-centre `br`-values. -/
  hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
      (𝓝[≠] b₀) (𝓝 0)
  /-- The finite pole-value centres are exactly the finite (non-`∞`) pole-values of `α`. -/
  hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- The `∞`-fibre normal-form data. -/
  Dinf_full : InftyFibreDataNF g f
  /-- The `∞`-coherence (the reciprocal-chart germ-equality). -/
  hcoh_full : recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br)
    =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full)
  hfullInf_inj : Function.Injective Dinf_full.xs
  /-- The `∞`-pole enumeration. -/
  ιInfP : Type
  fintype_ιInfP : Fintype ιInfP
  xsInf_po : ιInfP → X
  hpoInf_inj : Function.Injective xsInf_po
  hpoInf_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty
  hpoInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a
  hpole_image_inf : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
    = Finset.univ.image xsInf_po
  hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
    AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
      ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k))

attribute [instance] GateAInftyData.fintype_ιInfP

/-- **Gate A `∑Res = 0` for the real cover, `hoff_cs`-FREE.**  Given the per-centre real-cover ramified
data `RealCoverRamifiedCenters` (item #1 — the Forster §5 slit-branch normal form at each finite
pole-value centre, admitting ramification) and the off-centre + `∞` input bundle `GateAInftyData`, the
total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g a = 0`.

This routes through the `hoff_cs`-free capstone `residueTheorem_ofSheetData_genus0` — the finite centres
may be **ramified**.  The *only* genuinely-remaining content is `RealCoverRamifiedCenters` (the real-cover
`hgeom_slit`/`hvct_mero`); the bundle `GateAInftyData` is the already-Gate-A-discharged off-centre/`∞`
machinery for the canonical selection. -/
theorem residueSum_eq_zero_of_realCoverCenters {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {m : ℕ}
    {cs : Fin m → ℂ} {br : Finset ℂ}
    (A : GateAInftyData ω₀ g f hdiv poles cs br)
    (hRC : RealCoverRamifiedCenters ω₀ g f hdiv poles cs) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 := by
  obtain ⟨Sf, hp_pole, hp_fibre, hp_unique⟩ := hRC
  exact residueTheorem_ofSheetData_genus0 (canonicalFibreSelection g f hdiv) m cs A.ρ A.hcs_ball
    A.hcs_inj br A.hreg A.hbnd A.hcenters_cs Sf hp_pole hp_fibre hp_unique A.Dinf_full A.hcoh_full
    A.hfullInf_inj A.xsInf_po A.hpoInf_inj A.hpoInf_mem A.hpoInf_surj A.hpole_image_inf
    A.hnonpole_inf_an

/-- **Non-vacuity of `RealCoverRamifiedCenters` (no finite pole-value centres).**  When there are no
finite pole-value centres (`m = 0` — e.g. `α` holomorphic except possibly at `∞`), the per-centre data
is vacuously inhabited.  This confirms `RealCoverRamifiedCenters` is **not** a disguised `False`; the
genuinely-ramified non-vacuity (a single `m = 2` centre) rides on the `√(z − c)` slit-branch witness
`ramifiedSheetData_sqrt` (`SerreResidueRamifiedNormalForm.lean`), which inhabits one `RamifiedSheetData`
at a ramification multiplicity. -/
theorem realCoverRamifiedCenters_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) :
    RealCoverRamifiedCenters ω₀ g f hdiv poles (m := 0) Fin.elim0 :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-! ## The precise remaining real-cover obligation (the Forster §5 sheet-tracking wall)

`RealCoverRamifiedCenters` is the per-centre `RamifiedSheetData` for the canonical selection.  Its hard
fields, isolated:

* **`hvct_mero`** — now *reduced* to a finite-pole-order bound `(z − cs i)^N · valueChartTrace → 0` via
  `hvct_mero_of_pow_bound` (using the already-available off-centre `hreg`).  This is the meromorphy side
  (Miranda (3.1)), and is the strictly-easier obligation.
* **`hgeom_slit`** — the genuine geometric wall: on a slit accumulating at `cs i`, the geometric trace
  `valueChartTrace` (the full-fibre sum) equals the `m`-sheet sum `∑_{j<m} chartIntegrand(w_p + ζʲ w₀)·
  (d/dz)[…]` at the ramification preimage `p`.  This is the **Forster §5 `z = wᵐ` local normal form +
  fibre-cluster splitting** — the ramified analogue of `valueChartTrace_eq_sphereSheetFibreTrace`
  (`FormTraceBundleBridge.lean`), a genuine multi-hundred-line branch-aware sheet build not yet in the
  repo.

We record the exact target as a named predicate.  It is the *single* genuinely-remaining analytic input
to the `hoff_cs`-free Gate-A route; everything else (the residue/algebra atom, the identity-theorem
globalisation, the meromorphy reduction, the off-centre/∞ machinery, the wiring) is done. -/

/-- **The precise remaining per-centre geometric obligation** (the Forster §5 sheet-tracking wall).  At a
finite pole-value centre `c` with ramification preimage `p` of multiplicity `m`, a primitive `m`-th root
`ζ`, and the slit `S` carrying the `m`-th-root branch `w₀`, the two hard `RamifiedSheetData` facts:

* a **finite-pole-order bound** `(z − c)^N · valueChartTrace ω₀ f Φ → 0` (feeds `hvct_mero` via
  `hvct_mero_of_pow_bound`);
* the **geometric `m`-sheet identification on the slit** `hgeom_slit` (Forster §5 `z = wᵐ`).

Stated as the precise minimal residual — a *true* statement (Miranda (3.1) + Forster §5), the ramified
analogue of `valueChartTrace_eq_sphereSheetFibreTrace`, to be discharged by the local normal-form +
fibre-cluster build.  **Not** asserted as a free lemma; it is the named target for the remaining work. -/
def RealCoverSlitGeometry (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (c : ℂ) (p : X) (m : ℕ) (ζ : ℂ) (S : Set ℂ)
    (w₀ : ℂ → ℂ) : Prop :=
  (∃ N : ℕ, Tendsto (fun z => (z - c) ^ N * valueChartTrace ω₀ f Φ z) (𝓝[≠] c) (𝓝 0)) ∧
  (∀ z ∈ S, valueChartTrace ω₀ f Φ z = ∑ j ∈ Finset.range m,
    chartIntegrand ω₀ g p ((chartAt ℂ p) p + ζ ^ j * w₀ z)
      * deriv (fun ζz => (chartAt ℂ p) p + ζ ^ j * w₀ ζz) z)

/-! ## The simple-`∞` reduction skeleton (item #2/#3, the genericity)

Miranda §VIII.3 (p. 254): for the residue theorem it suffices to "choose *any* nonconstant `f`".  The
repo already proves a nonconstant meromorphic function exists (`exists_nonconstant_meromorphic`,
`SerreOmega0.lean`, via the Riemann inequality — Serre-independent).  The generic-position adjustment
that makes the `∞`-poles **simple** is the reciprocal trick `f' := (f₀ − a·1)⁻¹`: the `∞`-poles of `f'`
are the zeros of `f₀ − a`, which are simple for `a` off `f₀`'s (finite) critical values.

The order law `MeromorphicFunction.orderAtPoint_inv` (above) is the algebraic heart: a *simple zero*
(`orderAtPoint (f₀ − a) y = 1`) is a *simple pole of the reciprocal* (`orderAtPoint f' y = −1`).  The
remaining genericity — that a good `a` exists (simple zeros of `f₀ − a` and the finite pole-values of
`α` avoiding `f'`'s branch values) — is recorded as the precise obligation `ExistsAdaptedRealCover`
below. -/

/-- **Simple `∞`-pole from a simple zero of `f₀ − a`** (the reciprocal order law in action).  If
`f₀ − a·1` has a *simple zero* at `y` (`orderAtPoint (f₀ − a·1) y = 1`), then the reciprocal
`f' := (f₀ − a·1)⁻¹` has a *simple pole* at `y` (`orderAtPoint f' y = −1`).  This is `orderAtPoint_inv`
specialised — the algebraic step that makes `hsimpleInf` true for the reciprocal cover. -/
theorem orderAtPoint_inv_eq_neg_one_of_simpleZero (f₀ : MeromorphicFunction X) (a : ℂ) {y : X}
    (hy : (f₀ - a • (Jacobians.Dolbeault.constOneMero (X := X))).orderAtPoint y = 1) :
    ((f₀ - a • (Jacobians.Dolbeault.constOneMero (X := X)))⁻¹).orderAtPoint y = -1 := by
  rw [MeromorphicFunction.orderAtPoint_inv, hy]

/-- **The remaining genericity obligation for the real cover (`hoff_cs`-free route).**  An adapted real
cover exists for `α = ω₀·g` over any finite `poles` off which `g`'s chart-pullback is analytic: a
nonconstant `f` (with `f.div ≠ 0`), the finite pole-value centres `cs`, the per-centre real-cover
ramified data `RealCoverRamifiedCenters` (item #1 — the slit-branch normal form, admitting ramification,
so **no** `hoff_cs`), and the off-centre/`∞` bundle `GateAInftyData`.

**Soundness (non-false).**  Genuinely achievable for a general meromorphic `g` (Miranda p. 254): take a
nonconstant meromorphic function (`exists_nonconstant_meromorphic`) and the reciprocal `f' := (f₀ − a)⁻¹`
for a generic `a` (simple `∞`-poles via `orderAtPoint_inv`, the finite "bad `a`" set being finite).  The
finite pole-value fibres are then handled by `RealCoverRamifiedCenters` *even if ramified* (the slit
branch exists for any multiplicity — `ramifiedSheetData_sqrt`).  So this is a TRUE existential, not a
disguised `False`.  It is the `hoff_cs`-FREE analogue of `ExistsAdaptedF` (`SerreResidueGateAClosed.lean`),
relaxing the unramified-pole-fibre demand to the genuine ramified normal-form data. -/
def ExistsAdaptedRealCover (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X) : Prop :=
  (∀ x : X, x ∉ poles →
    AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) →
  ∃ (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (m : ℕ) (cs : Fin m → ℂ)
    (br : Finset ℂ) (_A : GateAInftyData ω₀ g.toFun f hdiv poles cs br),
    RealCoverRamifiedCenters ω₀ g.toFun f hdiv poles cs

/-- **UNCONDITIONAL 1-form residue theorem `∑Res = 0` for `α = ω₀·g`, modulo the `hoff_cs`-free
real-cover obligation.**  For a genuine meromorphic numerator `g` and any finite `poles` containing the
poles of `α = ω₀·g`, the total residue vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`,

given `ExistsAdaptedRealCover` (the adapted real cover — Miranda §VIII.3's "choose any nonconstant `f`"
plus the per-centre Forster §5 slit-branch data, admitting ramified pole fibres).  This is the
`hoff_cs`-free route to the well-definedness content underlying the global `Res : H¹(X,Ω) → ℂ`
(Forster 17.3) → the §17.5 Serre pairing. -/
theorem residueTheorem_realCover (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X)
    (hpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hAdapt : ExistsAdaptedRealCover ω₀ g poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 := by
  obtain ⟨f, hdiv, m, cs, br, A, hRC⟩ := hAdapt hpoles
  exact residueSum_eq_zero_of_realCoverCenters A hRC

end Jacobians
