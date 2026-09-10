/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormResidueTheorem
import KirovDolbeault.ManifoldIFT
import KirovDolbeault.ProperMapDegreeSheets

/-!
# The per-fibre trace data of `α = ω₀·g` (Gate A, node A-ii — bridges (a)/(b)/(c))

This file builds the **per-fibre** geometric content of the general 1-form residue theorem: the
construction of a `Jacobians.MeromorphicTrace.FibreTrace` over an *unramified* fibre `f⁻¹(b)` of the
cover `F = f.toRiemannSphere`, and the **per-fibre residue bridge**

> `resAt (T.coeff i) (T.pre i) = formFnResidue ω₀ g (xs i)`   (definitional, bridge (c)),

so that Miranda's Lemma 3.2 (`FibreTrace.resAt_traceCoeff'`, the now-unconditional residue
change-of-variables) gives

> `Res_b (Tr_F α over the fibre) = ∑_{x ∈ f⁻¹(b)} Res_x(α)`.

This is the genuinely-new **manifold-bundle** layer that feeds the `FormResidueTrace` assembly
(`Jacobians.Dolbeault.FormResidueTheorem`).  The remaining piece *after* this file — the global
**rationality** of the trace `Tr_F α` on `ℂℙ¹` (assembling the per-fibre data over *all* fibres into
a single `LaurentForm`) — is the last obligation, diagnosed precisely at the bottom of this file.

## The design — `coeff i`/`pre i` chosen to make bridge (c) definitional

The crucial design decision (mirroring the close-path's A-ii analysis): a `FibreTrace` over `b` with
sheets indexed by the fibre points `xs : ι → X` uses
* `pre i := (chartAt ℂ (xs i)) (xs i)` — the source-chart coordinate of `xs i`;
* `coeff i := fun w => coeffAt ω₀ (xs i) w * g ((chartAt ℂ (xs i)).symm w)` — the **chart integrand
  of `α = ω₀·g`** at `xs i`, exactly the function whose `resAt` at `pre i` is `formFnResidue ω₀ g
  (xs i)` *by definition* (`Jacobians.Dolbeault.formFnResidue`).

With this choice the per-fibre residue bridge (c) is **definitional** (`resAt_coeff_eq_formFnResidue`),
and the only genuinely-analytic inputs are
* (a) the **section germ** `sheet i`: a local holomorphic biholomorphism `ℂ → ℂ` sending the base
  coordinate `b'` (the value-chart coordinate at `F (xs i) = coe b`) to the source coordinate `pre i`
  — supplied by the manifold inverse function theorem `Jacobians.exists_holo_localInverse` applied to
  `F = f.toRiemannSphere` at `xs i` (a regular point), read in charts;
* (b) the **trivialization↔chart compatibility** of `coeffAt` (already discharged: `coeffAt ω₀ (xs i)`
  is analytic on the chart target, `Jacobians.Dolbeault.coeffAt_analyticAt`, so each `coeff i` is
  meromorphic at `pre i`).

`FibreTrace.coeff_mero` then holds because `coeffAt ω₀ (xs i)` is analytic at `pre i` and `g`'s
chart-pullback is meromorphic there.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17; §4.22–4.25 (sheets, local normal form).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.ProperMapDegreeSheets

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Bridge (c) — the per-fibre residue bridge (definitional)

With `coeff i` chosen to be the chart integrand of `α = ω₀·g` at `xs i`, and `pre i` the chart image
of `xs i`, the residue `resAt (coeff i) (pre i)` is `formFnResidue ω₀ g (xs i)` by the very
definition of `formFnResidue`.  This is the bridge (c) that turns the abstract `FibreTrace` residue
sum into the geometric fibre residue sum of `α`. -/

/-- The **chart integrand of `α = ω₀·g` at `a`**: `w ↦ coeffAt ω₀ a w · g (chart_a⁻¹ w)`, the
function in the canonical chart at `a` whose `resAt` at `chart_a a` is `formFnResidue ω₀ g a`. -/
def chartIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (a : X) : ℂ → ℂ :=
  fun w => coeffAt ω₀ a w * g ((chartAt ℂ a).symm w)

/-- **Bridge (c), definitional.**  The residue of the chart integrand of `α = ω₀·g` at `a`, read at
the chart image `chart_a a`, *is* `formFnResidue ω₀ g a` — by the definition of `formFnResidue`. -/
@[simp] theorem resAt_chartIntegrand_eq_formFnResidue (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (a : X) :
    resAt (chartIntegrand ω₀ g a) ((chartAt ℂ a) a) = formFnResidue ω₀ g a := rfl

/-- The chart integrand `chartIntegrand ω₀ g a` is **meromorphic at the chart image of `a`** whenever
`g`'s chart-pullback is meromorphic there: it is the product of the analytic coefficient
`coeffAt ω₀ a` (`coeffAt_analyticAt`) with the meromorphic `g ∘ chart_a⁻¹`.  (Bridge (b): the
trivialization-defined `coeffAt` is analytic in the chart, so it does not spoil meromorphy.) -/
theorem meromorphicAt_chartIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hg : MeromorphicAt (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    MeromorphicAt (chartIntegrand ω₀ g a) ((chartAt ℂ a) a) := by
  have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target :=
    (chartAt ℂ a).map_source (mem_chart_source ℂ a)
  exact (coeffAt_analyticAt ω₀ a hmem).meromorphicAt.mul hg

/-! ### Bridge (a) — the planar section germ (local biholomorphism inverse)

The local section of the cover, read entirely in charts, is a *planar* local biholomorphism inverse:
given an analytic `φ : ℂ → ℂ` at `x₀` with `φ'(x₀) ≠ 0` and `φ x₀ = b`, the complex inverse function
theorem (`HasStrictDerivAt.localInverse` + `AnalyticAt.analyticAt_localInverse` +
`HasStrictDerivAt.to_localInverse`) produces a section `s` analytic at `b` with `s b = x₀`,
`deriv s b = (deriv φ x₀)⁻¹ ≠ 0`, and `φ (s w) = w` near `b`.  This is the analytic core of
`FibreTrace.sheet`, packaged with **all** the `FibreTrace` field hypotheses (`sheet_analytic`,
`sheet_deriv_ne`, `sheet_base`). -/

/-- **Planar section germ of a local biholomorphism.**  For `φ : ℂ → ℂ` analytic at `x₀` with
`deriv φ x₀ ≠ 0` and `φ x₀ = b`, there is a section `s : ℂ → ℂ` analytic at `b` with `s b = x₀`,
`deriv s b ≠ 0`, and `φ (s w) = w` on a neighbourhood of `b`.  (The complex inverse function
theorem; `deriv s b = (deriv φ x₀)⁻¹`.) -/
theorem exists_planar_section {φ : ℂ → ℂ} {x₀ b : ℂ} (hφ : AnalyticAt ℂ φ x₀)
    (hφ' : deriv φ x₀ ≠ 0) (hb : φ x₀ = b) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s b ∧ s b = x₀ ∧ deriv s b ≠ 0 ∧
      (∀ᶠ w in 𝓝 b, φ (s w) = w) := by
  -- The Mathlib local inverse `s := localInverse φ (deriv φ x₀) x₀`.
  have hsd : HasStrictDerivAt φ (deriv φ x₀) x₀ := hφ.hasStrictDerivAt
  set s : ℂ → ℂ := hsd.localInverse φ (deriv φ x₀) x₀ hφ' with hs
  -- `s` analytic at `φ x₀ = b`.
  have hsana : AnalyticAt ℂ s (φ x₀) := hφ.analyticAt_localInverse hφ'
  -- `s (φ x₀) = x₀` (left inverse at the centre).
  have hsx₀ : s (φ x₀) = x₀ :=
    (hsd.eventually_left_inverse hφ').self_of_nhds
  -- `deriv s (φ x₀) = (deriv φ x₀)⁻¹` (the inverse strict derivative), hence `≠ 0`.
  have hsderiv : HasStrictDerivAt s (deriv φ x₀)⁻¹ (φ x₀) := hsd.to_localInverse hφ'
  have hsderiv' : deriv s (φ x₀) ≠ 0 := by
    rw [hsderiv.hasDerivAt.deriv]; exact inv_ne_zero hφ'
  -- `φ (s w) = w` near `φ x₀` (right inverse).
  have hrinv : ∀ᶠ w in 𝓝 (φ x₀), φ (s w) = w := hsd.eventually_right_inverse hφ'
  subst hb
  exact ⟨s, hsana, hsx₀, hsderiv', hrinv⟩

/-! ### The `FibreTrace` over an unramified fibre

Assembling (a)+(b)+(c): given a base value `b : ℂ` and a finite family of fibre points `xs : ι → X`,
each a **regular non-pole point** of `f` mapping to `b` (the chart pullback `g_{xs i} = f.holoRepr ∘
chart⁻¹` is analytic with nonzero derivative at `pre i = chart (xs i)`, and `f.holoRepr (xs i) = b`),
we build a `FibreTrace` over `b` whose per-sheet coefficient is the chart integrand of `α = ω₀·g` at
`xs i`.  Lemma 3.2 (`resAt_traceCoeff'`) then identifies its trace residue with the fibre residue sum
`∑ i, formFnResidue ω₀ g (xs i)`.

The per-sheet section `sheet i` is the planar inverse `s_i` of `g_{xs i}` (bridge (a)); `coeff_mero`
holds via bridge (b).  We bundle the *regularity inputs* (per-point analytic + deriv-nonzero) as
explicit hypotheses; they are exactly "`b` is a regular value off the pole/branch locus", to be
supplied by the global assembly from the finite critical-value set. -/

/-- **Per-fibre regularity data** for the cover `f` over the base value `b : ℂ`: a finite family of
fibre points `xs : ι → X`, each a non-pole regular point with `f.holoRepr (xs i) = b` and chart
pullback `g_{xs i}` a local biholomorphism at `pre i = chart (xs i)`.  This is the *honest geometric
input* the unramified-fibre `FibreTrace` is built from (supplied by the regular-value/IFT machinery
in the global assembly).  Parameterized by the form function `g` (its chart-pullback meromorphy
`hg_mero` is recorded so each per-sheet coefficient is meromorphic). -/
structure FibreRegularData (g : X → ℂ) (f : MeromorphicFunction X) (b : ℂ) where
  /-- The sheet index. -/
  ι : Type
  /-- Finiteness of the index. -/
  fintype_ι : Fintype ι
  /-- The fibre points. -/
  xs : ι → X
  /-- The chart pullback `f.holoRepr ∘ chart⁻¹` is analytic at `pre i = chart (xs i)`. -/
  hg_an : ∀ i, AnalyticAt ℂ (fun z => f.holoRepr ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i))
  /-- `xs i` is a regular point: the chart-pullback derivative is nonzero. -/
  hg_deriv : ∀ i, deriv (fun z => f.holoRepr ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i)) ≠ 0
  /-- `xs i` maps to the base value `b`: `f.holoRepr (xs i) = b`. -/
  hval : ∀ i, f.holoRepr (xs i) = b
  /-- `g`'s chart-pullback is meromorphic at each `pre i` (so `α·g` has an isolated singularity). -/
  hg_mero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i))

attribute [instance] FibreRegularData.fintype_ι

variable {g : X → ℂ}

/-- **`FibreRegularData` from per-point non-pole + regular + value data.**  The `hg_an` field (chart
pullback analytic at `pre i`) is *automatic* from non-poleness via the proven
`Jacobians.ProperMapDegreeSheets.analyticAt_holoRepr_chartPullback_target` (so it need not be
supplied); the caller provides only:

* `xs : ι → X` — the fibre points;
* `hnp` — each `xs i` is a **non-pole** (`0 ≤ orderAtPoint (xs i)`), so `f.holoRepr` is analytic there;
* `hderiv` — each `xs i` is a **regular point** (chart-pullback derivative of `f.holoRepr` nonzero);
* `hval` — `f.holoRepr (xs i) = b`;
* `hmero` — `g`'s chart-pullback is meromorphic at each `pre i`.

This is the honest reduced interface the regular-value machinery feeds — `hg_an` is discharged. -/
noncomputable def FibreRegularData.ofRegular (g : X → ℂ) (f : MeromorphicFunction X) (b : ℂ)
    {ι : Type} [Fintype ι] (xs : ι → X)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (xs i))
    (hderiv : ∀ i, deriv (fun z => f.holoRepr ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i)) ≠ 0)
    (hval : ∀ i, f.holoRepr (xs i) = b)
    (hmero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i))) :
    FibreRegularData g f b where
  ι := ι
  fintype_ι := inferInstance
  xs := xs
  hg_an := fun i => by
    have hz : (chartAt ℂ (xs i)) (xs i) ∈ (chartAt ℂ (xs i)).target :=
      (chartAt ℂ (xs i)).map_source (mem_chart_source ℂ (xs i))
    have hnp' : 0 ≤ f.orderAtPoint ((chartAt ℂ (xs i)).symm ((chartAt ℂ (xs i)) (xs i))) := by
      rw [(chartAt ℂ (xs i)).left_inv (mem_chart_source ℂ (xs i))]; exact hnp i
    exact ProperMapDegreeSheets.analyticAt_holoRepr_chartPullback_target f (xs i) hz hnp'
  hg_deriv := hderiv
  hval := hval
  hg_mero := hmero

/-- The chart pullback `f.holoRepr ∘ chart⁻¹` evaluated at `pre i = chart (xs i)` is `b`. -/
theorem FibreRegularData.gval (_ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) (i : D.ι) :
    (fun z => f.holoRepr ((chartAt ℂ (D.xs i)).symm z)) ((chartAt ℂ (D.xs i)) (D.xs i)) = b := by
  show f.holoRepr ((chartAt ℂ (D.xs i)).symm ((chartAt ℂ (D.xs i)) (D.xs i))) = b
  rw [(chartAt ℂ (D.xs i)).left_inv (mem_chart_source ℂ (D.xs i))]
  exact D.hval i

/-- **The `FibreTrace` over an unramified fibre.**  From the regularity data `D`, build the fibre
trace over `b` whose sheets are the planar section germs (bridge (a)) and whose coefficients are the
chart integrands of `α = ω₀·g` (bridges (b)/(c)).  The `pre i` are the source-chart coordinates of
the fibre points, so `resAt (coeff i) (pre i) = formFnResidue ω₀ g (xs i)` definitionally. -/
noncomputable def fibreTrace (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) : FibreTrace where
  ι := D.ι
  fintype_ι := D.fintype_ι
  b := b
  sheet := fun i =>
    Classical.choose (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval ω₀ f i))
  pre := fun i => (chartAt ℂ (D.xs i)) (D.xs i)
  sheet_analytic := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval ω₀ f i))).1
  sheet_deriv_ne := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval ω₀ f i))).2.2.1
  sheet_base := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hg_an i) (D.hg_deriv i) (D.gval ω₀ f i))).2.1
  coeff := fun i => chartIntegrand ω₀ g (D.xs i)
  coeff_mero := fun i => meromorphicAt_chartIntegrand ω₀ g (D.xs i) (D.hg_mero i)

@[simp] theorem fibreTrace_b (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) : (fibreTrace ω₀ f D).b = b := rfl

@[simp] theorem fibreTrace_pre (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) (i : D.ι) :
    (fibreTrace ω₀ f D).pre i = (chartAt ℂ (D.xs i)) (D.xs i) := rfl

@[simp] theorem fibreTrace_coeff (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) (i : D.ι) :
    (fibreTrace ω₀ f D).coeff i = chartIntegrand ω₀ g (D.xs i) := rfl

/-- **Bridge (c), assembled.**  The per-sheet residue of the fibre trace equals `formFnResidue`:
`resAt ((fibreTrace ω₀ f D).coeff i) ((fibreTrace ω₀ f D).pre i) = formFnResidue ω₀ g (xs i)`. -/
@[simp] theorem resAt_fibreTrace_coeff (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    {b : ℂ} (D : FibreRegularData g f b) (i : D.ι) :
    resAt ((fibreTrace ω₀ f D).coeff i) ((fibreTrace ω₀ f D).pre i)
      = formFnResidue ω₀ g (D.xs i) := by
  rw [fibreTrace_coeff, fibreTrace_pre]
  exact resAt_chartIntegrand_eq_formFnResidue ω₀ g (D.xs i)

/-- **Lemma 3.2 over the unramified fibre.**  The trace residue at the base equals the fibre residue
sum of `α = ω₀·g`:

> `Res_b (Tr_F α over the fibre) = ∑ i, formFnResidue ω₀ g (xs i)`.

This is the now-unconditional `FibreTrace.resAt_traceCoeff'` composed with bridge (c)
(`resAt_fibreTrace_coeff`).  It is the per-fibre identity the `FormResidueTrace` aggregates. -/
theorem resAt_traceCoeff_fibreTrace (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) :
    resAt (fibreTrace ω₀ f D).traceCoeff (fibreTrace ω₀ f D).b
      = ∑ i, formFnResidue ω₀ g (D.xs i) := by
  rw [(fibreTrace ω₀ f D).resAt_traceCoeff']
  exact Finset.sum_congr rfl (fun i _ => resAt_fibreTrace_coeff ω₀ f D i)

/-! ### The per-fibre residue sum as a fibre-restricted sum over the pole set (bridge (d), part 1)

For the global assembly we need the per-center fibre residue sum `∑ i, formFnResidue ω₀ g ((D p).xs i)`
(over a `FibreRegularData` whose `xs` *enumerates* the poles in the fibre `F⁻¹(coe p)`) to equal the
fibre-restricted sum `∑_{a ∈ poles, F a = coe p} formFnResidue ω₀ g a` that appears in
`FormResidueTrace.finite_eq`.  When `xs` is an injective enumeration of exactly that pole fibre, this
is `Finset.sum_image` / a bijection re-indexing — pure `Finset` combinatorics, no analysis. -/

/-- **Per-fibre residue sum = fibre-restricted pole-set sum.**  If the regularity data `D` over the
finite center `p` has `xs` injectively enumerating exactly the poles in the fibre `F⁻¹(coe p)`
(`hxs_inj`, `hxs_mem`, `hxs_surj`), then the per-fibre residue sum over `D` equals the
fibre-restricted residue sum over the pole set:

> `∑ i, formFnResidue ω₀ g ((D p).xs i) = ∑_{a ∈ poles, F a = coe p} formFnResidue ω₀ g a`. -/
theorem fibreResidueSum_eq_filter (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    {p : ℂ} (D : FibreRegularData g f p) (poles : Finset X)
    (hxs_inj : Function.Injective D.xs)
    (hxs_mem : ∀ i, D.xs i ∈ poles ∧ f.toRiemannSphere (D.xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) → ∃ i, D.xs i = a) :
    ∑ i, formFnResidue ω₀ g (D.xs i)
      = ∑ a ∈ poles with f.toRiemannSphere a = ((p : ℂ) : RiemannSphere), formFnResidue ω₀ g a := by
  classical
  -- The fibre filter set is the image of the (injective) enumeration `xs`.
  have hImg : (Finset.univ : Finset D.ι).image D.xs
      = poles.filter (fun a => f.toRiemannSphere a = ((p : ℂ) : RiemannSphere)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨(hxs_mem i).1, (hxs_mem i).2⟩
    · rintro ⟨ha_pole, ha_fib⟩; exact hxs_surj a ha_pole ha_fib
  -- `∑ i = ∑_{a ∈ univ.image xs}` (injective re-indexing), and that image is the filter set.
  rw [← hImg, Finset.sum_image (fun i _ j _ h => hxs_inj h)]

end Jacobians.Dolbeault.FormTraceFibre
