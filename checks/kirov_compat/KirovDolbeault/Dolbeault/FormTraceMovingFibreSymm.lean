/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceMovingFibreSheet

/-!
# The symmetric-invariance lever for the moving-fibre coherence (Gate A, §VIII.3)

`Jacobians.Dolbeault.FormTraceMovingFibreSheet` reduced Gate A's `∑Res = 0` to a single
`MovingSheetSelection`, whose per-value moving data is reduced (via
`MovingCoherenceDatum.ofSheetSections`) to the **§VIII.3 re-selection bijection** `hsel`: near each
base value `b₀`, an index bijection `e : (Φ b').ι ≃ D.ι` with `(Φ b').xs i' = sec (e i') b'`.

A prior round flagged a *false* obstruction here — "there is no global continuous sheet-labeling".  The
key architectural unlock is that **the trace is monodromy-INVARIANT**: `valueChartTrace ω₀ f Φ b' =
(fibreTrace ω₀ f (Φ b')).traceCoeff b'` is a *symmetric sum over the sheets* of the fibre `Φ b'`, so it
depends only on the fibre `Φ b'` **as a set**, not on any sheet ordering/labeling.  Consequently:

* The re-selection bijection `e` of `hsel` is quantified **pointwise per `b'`** (`∀ᶠ b', ∃ e, …`), *not*
  as a single continuous family.  No global continuous labeling is ever required.
* A pointwise bijection `e : (Φ b').ι ≃ D.ι` with `(Φ b').xs i' = sec (e i') b'` **exists automatically**
  whenever the re-selected fibre points `(Φ b').xs` and the moving-section values `sec · b'` enumerate
  the **same finite set** (both injective with equal range) — by `Equiv.ofInjective` on each side and the
  range identification.

This file builds that lever: the value-matching index bijection from set-equality of two injective
enumerations (`equivOfInjective_image_eq`), and the **set-form** moving-coherence constructor
`MovingCoherenceDatum.ofSheetSectionsSet`, whose geometric input is the *labeling-independent* fact that
the moving fibre `Φ b'` and the sections enumerate the same fibre set — no bijection supplied by the
caller, no global continuity.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `equivOfInjective_image_eq` — from two injective `p q : · → X` with the same finite image, an index
  bijection `e : ι ≃ κ` with `p i = q (e i)` (the value-matching pointwise bijection; the symmetric
  lever's combinatorial core).
* `MovingCoherenceDatum.ofSheetSectionsSet` — `MovingCoherenceDatum.ofSheetSections` with the
  re-selection bijection `hsel` replaced by the **set-form** hypothesis `hset`: near `b₀`, the
  re-selected fibre `(Φ b').xs` is injective and its image equals the image of the section values
  `sec · b'`, with each section value in the matching chart source.  The bijection is reconstructed
  pointwise — *no labeling supplied by the caller*.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; the trace is
  single-valued **by symmetry**, not by a global sheet choice).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceMovingFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceGlobal

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The value-matching index bijection from set-equality (the symmetric lever's core)

The combinatorial heart of the symmetric-invariance lever: two injective enumerations `p : ι → Y`,
`q : κ → Y` of the **same set** (`Set.range p = Set.range q`) are matched by a bijection `e : ι ≃ κ`
with `p i = q (e i)`.  The bijection is `(ofInjective p) ⬝ (range congr) ⬝ (ofInjective q)⁻¹`; the
value-matching is `Equiv.apply_ofInjective_symm`.  This is exactly what produces the per-`b'`
re-selection bijection of `hsel` from the labeling-independent fact that the two fibre enumerations have
the same image — *no continuity, no global labeling*. -/

/-- **Value-matching bijection from equal ranges.**  For injective `p : ι → Y` and `q : κ → Y` with
`Set.range p = Set.range q`, there is a bijection `e : ι ≃ κ` with `p i = q (e i)` for all `i`.  The
symmetric lever: two injective enumerations of the same fibre set are matched by *some* bijection, with
no continuity requirement. -/
theorem equivOfInjective_image_eq {ι κ Y : Type*} {p : ι → Y} {q : κ → Y}
    (hp : Function.Injective p) (hq : Function.Injective q) (hrange : Set.range p = Set.range q) :
    ∃ e : ι ≃ κ, ∀ i, p i = q (e i) := by
  -- `e := (ofInjective p) ⬝ (setCongr hrange) ⬝ (ofInjective q)⁻¹`.
  refine ⟨(Equiv.ofInjective p hp).trans
    ((Equiv.setCongr hrange).trans (Equiv.ofInjective q hq).symm), fun i => ?_⟩
  -- Unfold: `e i = (ofInjective q hq).symm ⟨p i, _⟩` (the range element `⟨p i, ·⟩` carried across).
  show p i = q ((Equiv.ofInjective q hq).symm ((Equiv.setCongr hrange) ((Equiv.ofInjective p hp) i)))
  rw [Equiv.ofInjective_apply]
  -- `(setCongr hrange) ⟨p i, _⟩ = ⟨p i, _⟩` (same underlying value, retyped into `range q`).
  rw [show (Equiv.setCongr hrange) (⟨p i, Set.mem_range_self i⟩ : Set.range p)
        = (⟨p i, hrange ▸ Set.mem_range_self i⟩ : Set.range q) from rfl]
  -- `q ((ofInjective q hq).symm ⟨p i, _⟩) = p i` by `apply_ofInjective_symm`.
  rw [Equiv.apply_ofInjective_symm hq]

/-! ### The set-form moving-coherence constructor (no labeling supplied)

`MovingCoherenceDatum.ofSheetSections` already quantifies its re-selection bijection `hsel` **pointwise
per `b'`** (`∀ᶠ b', ∃ e, …`) — there is *no* global-continuity requirement, contrary to the prior
round's flagged obstruction.  The only residual is to *produce* that pointwise bijection.  By the
symmetric lever, it exists automatically from set-equality: we supply the re-selection in **set form** —
near `b₀`, the re-selected fibre points `(Φ b').xs` are injective and enumerate the *same set* as the
section values `sec · b'` — and reconstruct `e` pointwise via `equivOfInjective_image_eq`.  This is the
labeling-independent input: the caller asserts only that the moving fibre *is* the sheet fibre as a set,
never a sheet ordering. -/

/-- **A moving-fibre coherence datum from sheet sections, set form (no labeling).**  Identical to
`MovingCoherenceDatum.ofSheetSections` except the re-selection bijection `hsel` is replaced by the
**labeling-independent set form** `hset`: near `b₀`,

> the re-selected fibre points `(Φ b').xs` and the section values `fun i => sec i b'` are *both*
> injective and have the *same image*, and each `sec i b'` lies in `chart_{D.xs i}.source`.

The per-`b'` index bijection `e : (Φ b').ι ≃ D.ι` with `(Φ b').xs i' = sec (e i') b'` is reconstructed
*pointwise* by `equivOfInjective_image_eq` (the symmetric lever) — **no global continuous labeling**,
which the trace's monodromy-invariance (symmetric fibre sum) makes unnecessary.  All differentiability
content is discharged by `MovingCoherenceDatum.ofSheetSections`. -/
noncomputable def MovingCoherenceDatum.ofSheetSectionsSet
    {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (D : FibreRegularData g f b₀) (sec : D.ι → ℂ → X)
    (hbase : ∀ i, sec i b₀ = D.xs i)
    (hsmooth : ∀ i, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sec i) b₀)
    (hsec : ∀ i, ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec i b') = b')
    (hset : ∀ᶠ b' in 𝓝 b₀, Function.Injective (Φ b').xs ∧
      Function.Injective (fun i => sec i b') ∧
      Set.range (Φ b').xs = Set.range (fun i => sec i b') ∧
      (∀ i, sec i b' ∈ (chartAt ℂ (D.xs i)).source)) :
    MovingCoherenceDatum ω₀ g f Φ b₀ := by
  refine MovingCoherenceDatum.ofSheetSections D sec hbase hsmooth hsec ?_
  filter_upwards [hset] with b' hb'
  obtain ⟨hΦinj, hsecb', hrange, hmem⟩ := hb'
  -- The symmetric lever: a value-matching pointwise bijection exists from set-equality.
  obtain ⟨e, he⟩ := equivOfInjective_image_eq hΦinj hsecb' hrange
  exact ⟨e, fun i' => he i', fun i => hmem i⟩
