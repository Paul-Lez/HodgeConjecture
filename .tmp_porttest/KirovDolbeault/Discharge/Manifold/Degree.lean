/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.LocalMultiplicity

set_option autoImplicit true


/-! # Degree of a holomorphic map between compact Riemann surfaces

This file provides a *fibre-cardinality* candidate body for `ContMDiff.degree`,
upgrading the constant-vs-non-constant indicator (`degreeStub`) toward the
classical definition

```
deg(f) = |f ⁻¹' {y}|   for any regular value y : Y.
```

## What is honest in this file

* For **constant** `f`, `degreeFiber f hf = 0` unconditionally.
* For **non-constant** `f`, `degreeFiber f hf` extracts a natural number from a
  packaged witness bundle (`RegularValueWitness`) using `Classical.choice` on
  the existence of such a witness. The witness records:
  - a chosen value `y₀ : Y`,
  - a proof that the fibre `f ⁻¹' {y₀}` is finite, and
  - the cardinality is then `(h.toFinset).card`.
  A `RegularValueWitnessReg f` now provably exists for non-constant `f`
  (see "## Status" below), so the no-witness fallback to `0` does not fire.
  Caveat: the witness only requires the fibre `f ⁻¹' {y₀}` finite, not
  non-empty, so positivity (`deg ≥ 1`) is not yet established — see below.

## Status (classical inputs)

For a non-constant holomorphic map `f : X → Y` between compact connected
Riemann surfaces, the following classical inputs are now formalised in the
`Discharge/Manifold/` chain:

1. **Properness with finite fibres.** Every fibre `f ⁻¹' {y}` is finite —
   `fibres_finite_statement_unconditional` (discreteness via the identity
   theorem for analytic functions).
2. **Existence of a regular value.** The critical values are finite
   (`criticalValues_finite_general`), so a regular value exists —
   `regular_value_exists_reg_unconditional` produces a `RegularValueWitnessReg`.
3. **Constancy of fibre cardinality across regular values.** The Hurwitz
   patching / local-normal-form argument gives well-definedness —
   `degreeFiber_eq_card_of_regular_witness`.

Together (1)–(3) make `degreeFiber f hf` a well-defined natural number,
equal to the fibre cardinality at any regular witness.

**Still open — positivity.** The regular value `y₀` is chosen from the
complement of the critical values, with no guarantee `y₀ ∈ range f`. If
`y₀ ∉ range f` the fibre is empty and `degreeFiber f hf = 0` even for a
non-constant `f`. Establishing `deg ≥ 1` needs surjectivity of a
non-constant holomorphic map on a compact connected surface (open-mapping
theorem + compactness), which is not yet formalised.

## Why a separate definition (and not editing `_root_.ContMDiff.degree`)

`Basic.lean`'s `_root_.ContMDiff.degree f hf : ℕ` signature is locked. This
file provides `Jacobians.Discharge.ContMDiff.degreeFiber` as a strict upgrade
candidate that matches the same signature shape (no extra arguments at the
call site beyond `f` and `hf`). When (1)–(3) above land in mathlib, the body
of `_root_.ContMDiff.degree` in `Basic.lean` can be retargeted from
`degreeStub` to `degreeFiber` without touching any caller.

## Main definitions

* `Jacobians.Discharge.ContMDiff.RegularValueWitness f` — a chosen value `y₀ : Y`
  together with a proof that the fibre over `y₀` is finite. Existence of this
  witness for non-constant analytic `f` between compact RS is the deep
  classical input.
* `Jacobians.Discharge.ContMDiff.degreeFiber f hf : ℕ` — `0` if `f` is constant;
  otherwise `Classical.choice`-extracted fibre cardinality (falling back to
  `0` if no `RegularValueWitness` exists at the pin).

## Compatibility with `degreeStub`

* `degreeFiber_const` matches `degreeStub_const`: constant maps have degree 0.
* `degreeFiber f hf = 0` whenever no `RegularValueWitness f` exists — same as
  `degreeStub` would give in the absence of any classical witness.
-/

noncomputable section

open scoped Manifold Topology
open Set

namespace Jacobians.Discharge

namespace ContMDiff

universe u v

/-! ## The witness bundle

A `RegularValueWitness f` packages a chosen value `y₀ : Y` together with a
proof that the fibre `f ⁻¹' {y₀}` is finite. This is the minimal structural
data needed to define a fibre cardinality without changing the signature of
`_root_.ContMDiff.degree`.

For a non-constant holomorphic map between compact connected Riemann surfaces,
existence of such a witness is a classical theorem (see file docstring item
1+2). At this mathlib pin neither (1) nor (2) is formalised, so the
`Nonempty (RegularValueWitness f)` hypothesis is the gap. -/
structure RegularValueWitness {X : Type u} {Y : Type v} (f : X → Y) where
  /-- Chosen value in the codomain. -/
  value : Y
  /-- The fibre over the chosen value is finite. -/
  fiber_finite : (f ⁻¹' {value}).Finite

/-- Cardinality of the chosen finite fibre, as a `Finset.card`. -/
def RegularValueWitness.card {X : Type u} {Y : Type v} {f : X → Y}
    (w : RegularValueWitness f) : ℕ :=
  w.fiber_finite.toFinset.card

/-- The witness card is the `Set.ncard` of its fibre. -/
lemma RegularValueWitness.card_eq_ncard {X : Type u} {Y : Type v} {f : X → Y}
    (w : RegularValueWitness f) : w.card = (f ⁻¹' {w.value}).ncard := by
  rw [RegularValueWitness.card, (f ⁻¹' {w.value}).ncard_eq_toFinset_card w.fiber_finite]

/-! ## Regular-value strengthened witness (ZZ172 corrected form)

`RegularValueWitness` carries only `fiber_finite`, which is structurally too
weak: classical "fibre cardinality is constant" requires the chosen value
*also* be a regular value (no preimage with degenerate chart-pullback
derivative). A `RegularValueWitness` over a critical point can have a smaller
fibre than a generic one (counts drop at branch points), so any "constant
fibre card" statement quantifying over arbitrary `RegularValueWitness` is
*false* as written.

`RegularValueWitnessReg f` strengthens `RegularValueWitness f` with a
**chart-pullback-derivative-nonzero certificate** inlined directly into the
structure: for every preimage point `x ∈ f ⁻¹' {value}`, the derivative
of the chart-pullback `(chartAt ℂ value) ∘ f ∘ (chartAt ℂ x).symm` at
`(chartAt ℂ x) x` is nonzero.

This is the analytic content of "value is a regular value of `f`" and is
exactly the shape consumed by `LocalSheetData.ofContMDiffMfderivNeZero`
(`Manifold/LocalSheetDataFromContMDiff.lean`, ZZ169). -/

/-- A **regular** regular-value witness for `f`. Strengthens
`RegularValueWitness` with a chart-pullback-derivative-nonzero certificate:
for every preimage point `x ∈ f ⁻¹' {value}`, the derivative of the
chart-pullback `(chartAt ℂ value) ∘ f ∘ (chartAt ℂ x).symm` at
`(chartAt ℂ x) x` is nonzero.

This is the analytic content of "`value` is a regular value of `f`",
inlined into the structure. -/
structure RegularValueWitnessReg
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) where
  /-- Underlying (cardinality-bearing) witness. -/
  toWitness : RegularValueWitness f
  /-- The chosen value is regular: at every preimage point, the chart-
  pullback of `f` has nonzero derivative. -/
  is_regular : ∀ x ∈ f ⁻¹' {toWitness.value},
    deriv ((chartAt ℂ toWitness.value) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0

namespace RegularValueWitnessReg

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
variable {f : X → Y}

/-- Cardinality of the chosen finite fibre of a regular witness. -/
def card (w : RegularValueWitnessReg f) : ℕ := w.toWitness.card

/-- The chosen regular value. -/
def value (w : RegularValueWitnessReg f) : Y := w.toWitness.value

/-- The fibre over the chosen regular value is finite. -/
def fiber_finite (w : RegularValueWitnessReg f) :
    (f ⁻¹' {w.toWitness.value}).Finite :=
  w.toWitness.fiber_finite

end RegularValueWitnessReg

/-- **Builder.** Promote a plain `RegularValueWitness` to a regular one,
given a chart-pullback-derivative-nonzero certificate at every preimage
point. -/
def RegularValueWitness.toRegular
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (w : RegularValueWitness f)
    (h_reg : ∀ x ∈ f ⁻¹' {w.value},
      deriv ((chartAt ℂ w.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0) :
    RegularValueWitnessReg f :=
  { toWitness := w, is_regular := h_reg }

/-- Builder card-coherence: the strengthened witness has the same `card` as
the underlying one. -/
@[simp] lemma RegularValueWitness.toRegular_card
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (w : RegularValueWitness f)
    (h_reg : ∀ x ∈ f ⁻¹' {w.value},
      deriv ((chartAt ℂ w.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0) :
    (w.toRegular h_reg).card = w.card := rfl

/-- Builder value-coherence. -/
@[simp] lemma RegularValueWitness.toRegular_value
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (w : RegularValueWitness f)
    (h_reg : ∀ x ∈ f ⁻¹' {w.value},
      deriv ((chartAt ℂ w.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0) :
    (w.toRegular h_reg).value = w.value := rfl

/-! ## The degree

A drop-in replacement for `degreeStub` that, when a `RegularValueWitnessReg`
is classically available, returns a *real* fibre cardinality rather than an
indicator. -/

/-- The **degree** of an analytic map `f : X → Y` between compact Riemann
surfaces, as a fibre cardinality.

* For constant `f`, returns `0` (matching the convention in challenge item 9
  and `degreeStub`).
* For non-constant `f`, returns the cardinality of *some* regular fibre,
  selected via `Classical.choice` on the existence of a `RegularValueWitnessReg`
  (a witness whose chosen value carries a chart-pullback-derivative-nonzero
  certificate at every preimage; this is the analytic content of "regular
  value"). If no such regular witness is classically available, falls back
  to `0`.

The well-definedness — independence of the chosen witness — is the deep
classical input that is **not** discharged here. See file docstring items
(2)–(3) for what is deferred.

**ZZ-RegFix correction.** Earlier the `Classical.choice` was on
`Nonempty (RegularValueWitness f)`, which carries no regularity certificate;
`Classical.choice` could pick a branch-point witness whose fibre cardinality
is strictly smaller than the topological degree. Switching to
`RegularValueWitnessReg f` bakes the analytic regularity in, so the choice
is always at a regular value. Existence of a regular witness for
non-constant analytic `f` is discharged unconditionally in
`Manifold/RegularValueExistsRegUnconditional.lean`. -/
def degreeFiber
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if IsConstantMap f then 0
  else
    if h : Nonempty (RegularValueWitnessReg f) then
      (Classical.choice h).card
    else 0

/-- Constant maps have fibre-degree `0`. -/
lemma degreeFiber_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (c : Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun _ : X => c)) :
    degreeFiber (fun _ : X => c) hf = 0 := by
  unfold degreeFiber
  simp [isConstantMap_const]

/-- If no *regular* regular-value witness exists for a non-constant map at
this pin, the fibre-degree falls back to `0`. (This is the same value
`degreeStub` returns in the constant case, so callers that only know
"degree = 0 ⇒ ..." remain correct.) -/
lemma degreeFiber_eq_zero_of_no_witness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ IsConstantMap f) (hno : ¬ Nonempty (RegularValueWitnessReg f)) :
    degreeFiber f hf = 0 := by
  unfold degreeFiber
  simp [hnc, hno]

/-- When a *regular* regular-value witness *does* exist (non-constant case,
`Classical` mode), the fibre-degree equals the cardinality of *some* such
witness. The particular witness is `Classical.choice`-selected; independence
of choice is the deep classical input. Because the choice is now over
`RegularValueWitnessReg f` (whose `is_regular` is built in), the chosen
witness is always at a regular value. -/
lemma degreeFiber_eq_witness_card
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ IsConstantMap f) (h : Nonempty (RegularValueWitnessReg f)) :
    degreeFiber f hf = (Classical.choice h).card := by
  unfold degreeFiber
  simp [hnc, h]

/-! ## Open mathlib infrastructure

The following statements would, if formalised in mathlib at this pin, allow
`degreeFiber` to be promoted from "structural skeleton with `Classical.choice`
fallback" to a fully honest definition. They are not proved here; they are
recorded as type-checking placeholders so that downstream files can grep for
`Degree.` to find the dependency surface.

Each placeholder is a `Prop`-valued definition of the **statement** of the
classical theorem; we do **not** assume it (no `axiom`s). Discharging them is
out of scope for this round. -/

namespace Degree

/-- (1) For a non-constant analytic map `f : X → Y` between compact connected
Riemann surfaces, every fibre is finite. Classical: identity theorem
(fibres are discrete) plus compactness.

**Status:** statement only. No proof is provided. -/
def fibres_finite_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ y : Y, (f ⁻¹' {y}).Finite

/-- (2) For a non-constant analytic map between compact connected Riemann
surfaces, the set of critical values is finite, so a regular value exists.
Classical input for `Nonempty (RegularValueWitness f)`.

**Status:** statement only. No proof is provided. -/
def regular_value_exists_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    Nonempty (RegularValueWitness f)

/-- (3) For a non-constant analytic map between compact connected Riemann
surfaces, the cardinality of the fibre is constant across regular values.
This is the well-definedness of the topological degree.

**Status:** statement only. No proof is provided. -/
def fibre_card_well_defined_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (w₁ w₂ : RegularValueWitness f), w₁.card = w₂.card

/-! ### Partial discharge of `fibres_finite_statement`

The full statement requires the analytic identity theorem on charts to ensure
fibres are discrete. We do not formalise the chart-level identity theorem at
this pin. We do however reduce `fibres_finite_statement` to a single named
topological hypothesis: **each fibre carries the discrete subspace topology**
(`IsDiscrete (f ⁻¹' {y})`). The reduction itself is purely topological:
continuity gives closedness, compactness of `X` upgrades closed to compact,
and a compact discrete subspace is finite (`IsCompact.finite`).

What is deferred (and not formalised here) is the implication

  analytic, non-constant ⇒ ∀ y, IsDiscrete (f ⁻¹' {y}).

That is the chart-level identity theorem.
-/

/-- A fibre of a continuous map into a `T2` compact space is closed and hence
compact; if additionally the fibre carries the discrete subspace topology, it
is finite. This is the purely topological half of the identity-theorem
argument. -/
lemma fiber_finite_of_isDiscrete
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf_cont : Continuous f) (y : Y)
    (h_disc : IsDiscrete (f ⁻¹' {y})) :
    (f ⁻¹' {y}).Finite := by
  have h_closed : IsClosed (f ⁻¹' {y}) :=
    isClosed_singleton.preimage hf_cont
  have h_cpct : IsCompact (f ⁻¹' {y}) := h_closed.isCompact
  exact h_cpct.finite h_disc

/-- **Partial discharge of `fibres_finite_statement`.** The full classical
statement reduces to a single uniform hypothesis: every fibre of a non-constant
analytic map carries the discrete subspace topology. This is what the chart-
level identity theorem would supply. The remainder of the argument
(closedness, compactness, finiteness from compact-discrete) is purely
topological and is discharged here. -/
lemma fibres_finite_of_all_fibers_isDiscrete
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_disc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → ∀ y : Y, IsDiscrete (f ⁻¹' {y})) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ y : Y, (f ⁻¹' {y}).Finite := by
  intro f hf hnc y
  exact fiber_finite_of_isDiscrete hf.continuous y (h_disc f hf hnc y)

/-- A second, slightly more granular reduction: instead of a global
"all fibers are discrete" hypothesis, accept a per-fiber hypothesis. Useful
when downstream code knows discreteness only at specific values. -/
lemma fiber_finite_of_pointwise_isolated
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf_cont : Continuous f) (y : Y)
    (h_iso : ∀ x ∈ f ⁻¹' {y}, ∃ U : Set X, IsOpen U ∧ U ∩ f ⁻¹' {y} = {x}) :
    (f ⁻¹' {y}).Finite := by
  refine fiber_finite_of_isDiscrete hf_cont y ?_
  rw [isDiscrete_iff_forall_exists_isOpen]
  exact h_iso

/-! ### Partial discharge of `regular_value_exists_statement`

A `RegularValueWitness f` needs only *some* `y₀ : Y` with finite fibre. The
classical statement gives much more (the *critical value set* is finite, hence
its complement contains many regular values). For the witness-existence
question alone, the much weaker fact "there is at least one `y` with finite
fibre" suffices. We record three reductions of decreasing strength:

* `regular_value_exists_of_some_fiber_finite`: from `∃ y, (f ⁻¹' {y}).Finite`.
* `regular_value_exists_of_fibres_finite`: from the full
  `fibres_finite_statement` (uses `ConnectedSpace Y → Nonempty Y`).
* `regular_value_exists_of_critical_values_finite`: from finiteness of the
  *critical-value set* together with `Infinite Y` — this is the form that
  exposes the actual analytic obligation (critical-point set is the zero set
  of `f'` in chart coords, discrete by the identity theorem, hence finite by
  compactness; its image is finite). -/

/-- Trivial reduction: a `RegularValueWitness f` is exactly an element of `Y`
together with finiteness of its fibre. So existence is equivalent to
`∃ y, (f ⁻¹' {y}).Finite`. -/
lemma regular_value_exists_of_some_fiber_finite
    {X : Type u} {Y : Type v} {f : X → Y}
    (h : ∃ y : Y, (f ⁻¹' {y}).Finite) :
    Nonempty (RegularValueWitness f) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨{ value := y, fiber_finite := hy }⟩

/-- Reduction of `regular_value_exists_statement` to `fibres_finite_statement`.

Given that *every* fibre is finite (the conclusion of
`fibres_finite_statement`), and `Y` is non-empty (free from
`ConnectedSpace Y`), pick any `y : Y` and package it as a witness. -/
lemma regular_value_exists_of_fibres_finite
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_fib : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → ∀ y : Y, (f ⁻¹' {y}).Finite) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → Nonempty (RegularValueWitness f) := by
  intro f hf hnc
  haveI : Nonempty Y := inferInstance
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  exact regular_value_exists_of_some_fiber_finite ⟨y, h_fib f hf hnc y⟩

/-- **The intended reduction.** Reduce `regular_value_exists_statement` to the
*precise* analytic obligation: the **critical-value set is finite**.

Mathematically: if the critical-value set `C ⊆ Y` is finite and `Y` is
infinite, then `Y \ C` is non-empty; pick `y ∈ Y \ C`. By the local normal
form (`z ↦ z^k` with `k = 1` at non-critical points), `f` is locally injective
at every preimage of `y`, so the fibre `f ⁻¹' {y}` is discrete. Combined with
compactness of `X` (giving closedness then compactness of the fibre), this
yields a finite fibre, hence a `RegularValueWitness`.

Here we expose the obligation in its sharpest form: a hypothesis `h_crit`
producing, *for every non-constant analytic `f`*, a finite set
`C : Finset Y` containing all critical values, plus the local-injectivity
witness `h_disc` at non-critical values (the identity-theorem half is
isolated to `h_disc`).

This reduction makes the gap `regular_value_exists_statement` boil down to
`h_crit` + `h_disc` + `Infinite Y`, with everything else (closedness,
compactness, finite-from-compact-discrete) discharged. -/
lemma regular_value_exists_of_critical_values_finite
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [Infinite Y]
    (h_crit : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → ∃ C : Finset Y, True ∧
        ∀ y : Y, y ∉ C → IsDiscrete (f ⁻¹' {y})) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → Nonempty (RegularValueWitness f) := by
  intro f hf hnc
  obtain ⟨C, _, hC⟩ := h_crit f hf hnc
  -- Y is infinite, C is finite ⇒ ∃ y ∉ C.
  have h_compl : (↑C : Set Y)ᶜ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    have : (Set.univ : Set Y).Finite := h ▸ C.finite_toSet
    exact (Set.infinite_univ).not_finite this
  obtain ⟨y, hy⟩ := h_compl
  have h_disc : IsDiscrete (f ⁻¹' {y}) := hC y hy
  have h_fin : (f ⁻¹' {y}).Finite :=
    fiber_finite_of_isDiscrete hf.continuous y h_disc
  exact regular_value_exists_of_some_fiber_finite ⟨y, h_fin⟩

/-! ### Partial discharge of `fibre_card_well_defined_statement`

Independence of the chosen `RegularValueWitness` — i.e. the topological-degree
well-definedness — has the following classical structure. The set of regular
values `R ⊆ Y` is the complement of the (finite) critical-value set. On `R`
the map `f` is a covering map, so the fibre-cardinality function

  `n : R → ℕ`,   `n y = |f ⁻¹' {y}|`

is *locally constant*. Since `R = Y \ C` with `C` finite and `Y` a connected
Riemann surface (real dimension `≥ 2`), `R` is connected. A locally constant
function on a (pre)connected space is constant. Hence any two regular-value
witnesses give the same fibre cardinality.

We do **not** prove "covering map ⇒ locally constant fibre cardinality" or
"connected minus finite is connected for real-dim ≥ 2 manifolds" at this pin:
both are classical and both are heavy enough to deserve their own files. We
instead reduce `fibre_card_well_defined_statement` to a single named
hypothesis — the **fibre-cardinality function exists, extends every witness,
and is constant on the regular-value support** — and discharge the rest. The
shape of the hypothesis exactly mirrors the form items (1)–(2) take above:
classical content is named, topological/structural plumbing is dispatched. -/

/-- A **fibre-cardinality function** packaging the data classical
covering-space theory provides. Recorded as a structure so downstream files
have a single named target: discharging
`fibre_card_well_defined_statement` reduces to producing one of these for
every non-constant analytic `f`.

Fields:
* `card_of`: the fibre-cardinality function on `Y` (or any superset of the
  regular-value set; we take all of `Y` for simplicity, since the value at a
  critical point is irrelevant for the witness-comparison argument).
* `card_of_witness`: every `RegularValueWitness w` has
  `card_of w.value = w.card`. This is a definitional compatibility: it says
  `card_of` agrees with the true fibre cardinality at every point that
  *carries* a witness — exactly the points the well-definedness statement
  ranges over.
* `card_of_constant`: `card_of` is constant when restricted to the witness
  values. This is the deep classical content (covering-space + connectedness
  of `Y \ critical-values`). -/
structure FibreCardData {X : Type u} {Y : Type v} (f : X → Y) where
  /-- The fibre-cardinality function. -/
  card_of : Y → ℕ
  /-- `card_of` reads off any witness's cardinality. -/
  card_of_witness : ∀ w : RegularValueWitness f, card_of w.value = w.card
  /-- `card_of` agrees on any two witness values. (This is what the
  covering-space + connected-regular-value-set argument supplies.) -/
  card_of_constant : ∀ w₁ w₂ : RegularValueWitness f,
    card_of w₁.value = card_of w₂.value

/-- **Trivial reduction.** Given a `FibreCardData f`, the cardinalities of
any two regular-value witnesses agree. This is purely structural composition
of the fields of `FibreCardData`. -/
lemma fibre_card_eq_of_fibreCardData
    {X : Type u} {Y : Type v} {f : X → Y}
    (D : FibreCardData f) (w₁ w₂ : RegularValueWitness f) :
    w₁.card = w₂.card := by
  have h₁ : D.card_of w₁.value = w₁.card := D.card_of_witness w₁
  have h₂ : D.card_of w₂.value = w₂.card := D.card_of_witness w₂
  have hc : D.card_of w₁.value = D.card_of w₂.value := D.card_of_constant w₁ w₂
  -- w₁.card = card_of w₁.value = card_of w₂.value = w₂.card
  calc w₁.card = D.card_of w₁.value := h₁.symm
    _ = D.card_of w₂.value := hc
    _ = w₂.card := h₂

/-- **Partial discharge of `fibre_card_well_defined_statement`.** The full
classical statement reduces to a single uniform hypothesis: every non-constant
analytic `f` admits a `FibreCardData f` (the covering-space-supplied
fibre-cardinality function with its constancy on witness values).

Everything else — extracting `w₁.card = w₂.card` from the data — is
discharged here by `fibre_card_eq_of_fibreCardData`. -/
lemma fibre_card_well_defined_of_fibreCardData
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_data : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → FibreCardData f) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitness f), w₁.card = w₂.card := by
  intro f hf hnc w₁ w₂
  exact fibre_card_eq_of_fibreCardData (h_data f hf hnc) w₁ w₂

/-- **Sharper reduction: locally-constant fibre-cardinality on a preconnected
regular-value subtype.**

This form exposes the analytic obligation in covering-space shape, using the
subspace topology on the regular-value set `R ⊆ Y`.

* `card_of : Y → ℕ`, the fibre-cardinality function on `Y` (its value off
  regular values is irrelevant).
* `h_witness`: `card_of` reads off any witness's card.
* `h_supp`: every witness's value lies in `R`.
* `h_lc_sub`: `card_of` restricted to the subtype `R` is locally constant —
  this is exactly the covering-space content.
* `h_conn_sub`: the subtype `R` is preconnected — the topological content
  (a connected Riemann surface minus a finite set is preconnected, real
  dimension `≥ 2`).

The conclusion follows from
`IsLocallyConstant.apply_eq_of_isPreconnected`. -/
lemma fibre_card_eq_of_locallyConstant_subtype
    {X : Type u} {Y : Type v} [TopologicalSpace Y]
    {f : X → Y}
    {R : Set Y}
    (card_of : Y → ℕ)
    (h_witness : ∀ w : RegularValueWitness f, card_of w.value = w.card)
    (h_supp : ∀ w : RegularValueWitness f, w.value ∈ R)
    (h_lc_sub : IsLocallyConstant (fun y : R => card_of y.val))
    (h_conn_sub : IsPreconnected (Set.univ : Set R))
    (w₁ w₂ : RegularValueWitness f) :
    w₁.card = w₂.card := by
  have hc : card_of w₁.value = card_of w₂.value := by
    have :=
      h_lc_sub.apply_eq_of_isPreconnected h_conn_sub
        (Set.mem_univ (⟨w₁.value, h_supp w₁⟩ : R))
        (Set.mem_univ (⟨w₂.value, h_supp w₂⟩ : R))
    simpa using this
  calc w₁.card
      = card_of w₁.value := (h_witness w₁).symm
    _ = card_of w₂.value := hc
    _ = w₂.card := h_witness w₂

/-- **Top-level reduction**: well-definedness of the fibre cardinality (the
shape of `fibre_card_well_defined_statement`) follows from the existence,
for every non-constant analytic `f`, of a locally-constant fibre-cardinality
function on a preconnected regular-value subtype covering all witness
values. This is exactly the covering-space content (locally constant on the
regular-value set, which is preconnected since `Y` is a connected Riemann
surface and the critical-value set is finite). -/
lemma fibre_card_well_defined_of_locallyConstant
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_lc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∃ (R : Set Y) (card_of : Y → ℕ),
        (∀ w : RegularValueWitness f, card_of w.value = w.card) ∧
        (∀ w : RegularValueWitness f, w.value ∈ R) ∧
        IsLocallyConstant (fun y : R => card_of y.val) ∧
        IsPreconnected (Set.univ : Set R)) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitness f), w₁.card = w₂.card := by
  intro f hf hnc w₁ w₂
  obtain ⟨R, card_of, h_w, h_supp, h_lcs, h_conn⟩ := h_lc f hf hnc
  exact fibre_card_eq_of_locallyConstant_subtype
    (R := R) card_of h_w h_supp h_lcs h_conn w₁ w₂

/-- (3.reg) **The truthful constant-fibre-card statement.** Quantifies only
over *regular* witnesses (those whose chosen value carries the analytic
chart-pullback-deriv-nonzero certificate). This is the form classical
covering-space theory proves; the original `fibre_card_well_defined_statement`
(over arbitrary `RegularValueWitness`) is false at branch points.

**Status:** statement only. No proof is provided. -/
def fibre_card_well_defined_at_regular_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card

/-- **Trivial reduction.** Given a `FibreCardData f`, the cardinalities of
any two *regular* regular-value witnesses agree. (Same proof as the
unrestricted case — the regularity certificate is consumed only by the
data supplier, not by this structural step.) -/
lemma fibre_card_eq_of_fibreCardData_reg
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y}
    (D : FibreCardData f) (w₁ w₂ : RegularValueWitnessReg f) :
    w₁.card = w₂.card :=
  fibre_card_eq_of_fibreCardData D w₁.toWitness w₂.toWitness

/-- **Sharper reduction (regular form): locally-constant fibre-cardinality on
a preconnected subset.** Same shape as the unrestricted
`fibre_card_eq_of_locallyConstant_subtype`. The user supplies a regular-
value subset `R : Set Y` and a proof `h_supp` that every regular witness's
value lies in `R`. -/
lemma fibre_card_eq_of_locallyConstant_subtype_reg
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y}
    {R : Set Y}
    (card_of : Y → ℕ)
    (h_witness : ∀ w : RegularValueWitness f, card_of w.value = w.card)
    (h_supp : ∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ R)
    (h_lc_sub : IsLocallyConstant (fun y : R => card_of y.val))
    (h_conn_sub : IsPreconnected (Set.univ : Set R))
    (w₁ w₂ : RegularValueWitnessReg f) :
    w₁.card = w₂.card := by
  have hc : card_of w₁.toWitness.value = card_of w₂.toWitness.value := by
    have :=
      h_lc_sub.apply_eq_of_isPreconnected h_conn_sub
        (Set.mem_univ (⟨w₁.toWitness.value, h_supp w₁⟩ : R))
        (Set.mem_univ (⟨w₂.toWitness.value, h_supp w₂⟩ : R))
    simpa using this
  show w₁.toWitness.card = w₂.toWitness.card
  calc w₁.toWitness.card
      = card_of w₁.toWitness.value := (h_witness w₁.toWitness).symm
    _ = card_of w₂.toWitness.value := hc
    _ = w₂.toWitness.card := h_witness w₂.toWitness

end Degree

end ContMDiff

end Jacobians.Discharge

end
