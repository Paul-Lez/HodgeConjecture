/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.MeromorphicAt
import KirovDolbeault.Discharge.Manifold.MeromorphicDivisor
import KirovDolbeault.Discharge.Manifold.LocalMultiplicity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit true


/-! # Local normal form for analytic / meromorphic maps and local multiplicity

This file lays the framework for the **(R3) local-multiplicity = local-order**
gap of `Manifold/ResidueTheorem.lean`. The classical statement is:

> Let `f : X → ℂ` be meromorphic at `x : X` on a complex manifold, and let
> `k := (mmeromorphicOrderAt I f x).untop₀` be the chart-pulled-back integer
> order. Then in any chart at `x`, the function `f ∘ chart⁻¹` admits the
> local normal form
>
>   `(f ∘ chart⁻¹)(z) = (z - chart x) ^ k • g(z)`
>
> for some analytic `g` with `g (chart x) ≠ 0` (interpreting `k < 0` as the
> meromorphic-power case `(z - chart x) ^ (k : ℤ)`).
>
> Consequently the *topological local multiplicity* of `f` at `x` (cardinality
> of `f⁻¹{w}` near `x` for `w` near `f x`, in the analytic case) equals
> `k.natAbs`.

## Status: framework + chart-coordinate proof

What is **proven** in this file:

1. `localOrder I f x : ℤ` — a structural rename of
   `MMeromorphicOn.orderFun I f x`. Definitionally equal; serves as the named
   replacement for the `degreeStub` indicator in `LocalMultiplicity.lean`.
2. `localOrder_eq_orderFun` — the structural identity.
3. `localOrder_eq_zero_iff` — under the no-germ-zero hypothesis, vanishing
   of `localOrder` matches vanishing of `mmeromorphicOrderAt`.
4. **`MMeromorphicAt.exists_local_normal_form`** — the *honest* local-form
   theorem in chart coordinates. For `f` meromorphic at `x` with finite
   order `k`, the chart representative `f ∘ chart⁻¹` admits the form
   `(z - chart x) ^ k • g(z)` for some analytic `g` with `g(chart x) ≠ 0`,
   on a punctured neighborhood. **Proof: direct application of the mathlib
   lemma `meromorphicOrderAt_eq_int_iff`.** Zero gaps.
5. **`MMeromorphicAt.exists_local_normal_form_of_nonneg`** — the analytic
   case (`k ≥ 0`) strengthens the punctured neighborhood to a full
   neighborhood (no zero-divisor singularity to remove).

Stated as inert `Prop`-valued `def`s here (NOT axioms), kept for reference:

6. `localMultiplicity_eq_localOrder_statement` and the sibling `*_statement`
   `def`s package the connection between `localOrder` and the topological
   local multiplicity (cardinality of `f⁻¹{w}` near `x` for `w` near `f x`).
   These specific placeholder `def`s are left unproven, but the underlying
   fact — `(z - x₀) ^ k · u(z) = w` has exactly `k` solutions near `x₀` for
   small `w ≠ 0` when `u(x₀) ≠ 0` — IS proven, via the k-th-root
   substitution route, in `LocalKFoldMultiplicityUnconditional.lean` /
   `LocalKFoldMultiplicityFullyUnconditional.lean` (not via Rouché).

The file therefore provides definitions, structural identities, and the
chart-coordinate local-form theorem, all proven; the `*_statement` defs are
inert `Prop`-valued placeholders (NOT axioms), superseded by the proven
k-fold count in the sibling files.

## Open mathlib lemmas (catalogued for the next pass)

The following mathlib names are what the eventual filling will route through:

* `AnalyticAt.analyticOrderAt_eq_natCast`
  — `Mathlib/Analysis/Analytic/Order.lean`. The analytic local form
  `f z = (z - z₀) ^ n • g z` for analytic `f` with order `n : ℕ`.
* `meromorphicOrderAt_eq_int_iff`
  — `Mathlib/Analysis/Meromorphic/Order.lean`. The meromorphic local form
  `f z = (z - x) ^ n • g z` (with `n : ℤ`) on the punctured neighborhood.
* `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`
  — `Mathlib/Analysis/Analytic/IsolatedZeros.lean`. The existence side of
  the analytic decomposition (used in the proof of (4) above via
  `meromorphicOrderAt_eq_int_iff`).
* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
  — companion isolated-zeros lemma; not invoked here but useful for the
  topological-multiplicity discharge.

The topological-multiplicity discharge (Rouché-via-degree-theory) will need
an argument analogous to mathlib's
`Complex.exists_count_preimage_of_eq_pow` (does not exist at the pin) or
the Rouché theorem applied to `f(z) - w = (z - x₀)^k u(z) - w`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace Jacobians.Discharge

universe u

/-! ## The structural local-order definition

`localOrder I f x` is the integer-valued local order of `f` at `x`,
expressed as the chart-pulled-back `mmeromorphicOrderAt` cast through
`WithTop.untop₀` (positive at zeros, negative at poles, `0` at regular
nonzero points and at germ-zero points).

This is **definitionally equal** to `MMeromorphicOn.orderFun I f x` from
`Manifold/MeromorphicDivisor.lean` — we just give it the structural name
that `R3_localMultiplicity_statement` in `Manifold/ResidueTheorem.lean`
should ultimately route through. -/

/-- The **integer-valued local order** of `f : X → ℂ` at `x : X`, computed
via the chart-pullback `mmeromorphicOrderAt`. -/
def localOrder
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (I : ModelWithCorners ℂ ℂ ℂ) (f : X → ℂ) (x : X) : ℤ :=
  MMeromorphicOn.orderFun I f x

/-- `localOrder` is exactly the underlying `orderFun` — structural identity. -/
@[simp] lemma localOrder_eq_orderFun
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (I : ModelWithCorners ℂ ℂ ℂ) (f : X → ℂ) (x : X) :
    localOrder I f x = MMeromorphicOn.orderFun I f x := rfl

/-- Unfolded form: `localOrder` is the `WithTop.untop₀` of the meromorphic
order at `x`. -/
lemma localOrder_eq_untop₀
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (I : ModelWithCorners ℂ ℂ ℂ) (f : X → ℂ) (x : X) :
    localOrder I f x = (mmeromorphicOrderAt I f x).untop₀ := rfl

/-- Under the no-germ-zero hypothesis, `localOrder I f x = 0` iff
`mmeromorphicOrderAt I f x = 0` (no spurious `⊤ ↦ 0` collapse).

Inlined (rather than delegated to `MMeromorphicOn.orderFun_eq_zero_iff`)
because the latter carries a spurious `[IsManifold ...]` dependency from
its enclosing `variable` block; the statement here is purely about
`WithTop ℤ.untop₀` and needs no manifold structure. -/
lemma localOrder_eq_zero_iff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}
    (hf0 : mmeromorphicOrderAt I f x ≠ ⊤) :
    localOrder I f x = 0 ↔ mmeromorphicOrderAt I f x = 0 := by
  change (mmeromorphicOrderAt I f x).untop₀ = 0 ↔ _
  constructor
  · intro h
    rcases WithTop.untop₀_eq_zero.mp h with h0 | htop
    · exact h0
    · exact (hf0 htop).elim
  · intro h
    rw [h]; rfl

/-! ## The chart-coordinate local normal form

The honest content. We invoke the mathlib lemma `meromorphicOrderAt_eq_int_iff`
to extract the local form `f(z) = (z - x₀) ^ k • g(z)` on a punctured
neighborhood, with `g` analytic and `g(x₀) ≠ 0`. -/

namespace MMeromorphicAt

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}

/-- **Local normal form for a meromorphic function in chart coordinates.**

For `f : X → ℂ` meromorphic at `x : X` on a complex chart, with finite
chart-pullback order `k = (mmeromorphicOrderAt I f x).untop₀`, the chart
representative `f ∘ (chartAt ℂ x).symm` admits the local form

  `(f ∘ chart⁻¹)(z) = (z - (chartAt ℂ x) x) ^ k • g(z)`

for some analytic `g` with `g ((chartAt ℂ x) x) ≠ 0`, on a punctured
neighborhood of `(chartAt ℂ x) x`.

This is the **chart-coordinate** version of R3. The R3 statement in
`ResidueTheorem.lean` further requires extracting the *topological*
multiplicity (cardinality of preimages); that step is deferred from a
mathlib-side Rouché argument and is captured as
`localMultiplicity_eq_localOrder_statement` below.

Proof: direct application of `meromorphicOrderAt_eq_int_iff`. -/
theorem exists_local_normal_form
    (hf : MMeromorphicAt I f x)
    (hf0 : mmeromorphicOrderAt I f x ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ((chartAt ℂ x) x) ∧
      g ((chartAt ℂ x) x) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x) x),
        (f ∘ (chartAt ℂ x).symm) z = (z - (chartAt ℂ x) x) ^ localOrder I f x • g z := by
  -- Unfold `MMeromorphicAt` to the underlying flat-domain `MeromorphicAt`.
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  -- The flat-domain order equals our `localOrder` definitionally
  -- (`localOrder = (mmeromorphicOrderAt I f x).untop₀ = meromorphicOrderAt _ _.untop₀`).
  set k : ℤ := localOrder I f x with hk
  have h_order_ne_top :
      meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ ⊤ := hf0
  -- Express `meromorphicOrderAt _ _ = (k : ℤ)` so we can apply
  -- `meromorphicOrderAt_eq_int_iff`.
  have h_order_eq :
      meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = (k : WithTop ℤ) := by
    -- `k = (mmeromorphicOrderAt I f x).untop₀ = meromorphicOrderAt _ _.untop₀`,
    -- and a `WithTop ℤ` value `≠ ⊤` equals the cast of its `untop₀`.
    change meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) =
      ((meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)).untop₀ : WithTop ℤ)
    exact (WithTop.coe_untop₀_of_ne_top h_order_ne_top).symm
  -- Apply the mathlib characterization.
  exact (meromorphicOrderAt_eq_int_iff hf').mp h_order_eq

/-- **Local normal form for an analytic function in chart coordinates.**

Strengthening of `exists_local_normal_form` to a *full* neighborhood (not
just punctured) when `f` is analytic at the chart image, i.e. when the
order is `≥ 0`. This is the case relevant to `R3` for *zeros* (rather
than poles) of `f`.

Proof: combine the punctured-neighborhood form with continuity of the
right-hand side at `(chartAt ℂ x) x` (where `(z - x₀)^k` is continuous
for `k ≥ 0` and the value at `x₀` is `0` for `k > 0`, matching `f x`). -/
theorem exists_local_normal_form_of_nonneg
    (_hf : MMeromorphicAt I f x)
    (hf0 : mmeromorphicOrderAt I f x ≠ ⊤)
    (hk : 0 ≤ localOrder I f x)
    (hf_an : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ((chartAt ℂ x) x) ∧
      g ((chartAt ℂ x) x) ≠ 0 ∧
      ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        (f ∘ (chartAt ℂ x).symm) z =
          (z - (chartAt ℂ x) x) ^ (localOrder I f x).toNat • g z := by
  -- Step 1: The analytic order equals `(localOrder I f x).toNat`.
  -- Use the analytic-order/meromorphic-order compatibility lemma.
  set k : ℤ := localOrder I f x with hk_def
  set n : ℕ := k.toNat with hn_def
  have h_kn : (k : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by
    simp [hn_def, Int.toNat_of_nonneg hk]
  -- The analytic order (`ℕ∞`-valued) equals `n`.
  have h_an_order : analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = (n : ℕ∞) := by
    -- From `AnalyticAt.meromorphicOrderAt_eq` we have
    -- `meromorphicOrderAt = (analyticOrderAt).map (↑)`. Combine with `h_order_eq` from the
    -- meromorphic side.
    have h_mero_eq : meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)).map (↑· : ℕ → ℤ) :=
      hf_an.meromorphicOrderAt_eq
    have h_mero_int : meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (k : WithTop ℤ) := by
      show meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = (k : WithTop ℤ)
      have h_ne_top :
          meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ ⊤ := hf0
      exact (WithTop.coe_untop₀_of_ne_top h_ne_top).symm
    -- Combine: `(analyticOrderAt _).map (↑) = (n : ℤ)` ⟹ `analyticOrderAt _ = n`.
    have h_combined :
        (analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)).map (↑· : ℕ → ℤ)
          = ((n : ℤ) : WithTop ℤ) := by
      rw [← h_mero_eq, h_mero_int, h_kn]
    -- The map `Nat.cast : ℕ → ℤ` is injective on `WithTop`; extract `analyticOrderAt _ = n`.
    -- We do this by case analysis on `analyticOrderAt _`.
    cases h_top : analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) with
    | top =>
      -- Then `(⊤).map _ = ⊤ ≠ ((n : ℤ) : WithTop ℤ)` — contradiction.
      rw [h_top] at h_combined
      exact absurd h_combined (by simp)
    | coe m =>
      rw [h_top] at h_combined
      -- `(m : ℕ).map _ = (m : ℤ)` and `((n : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)`.
      simp only [ENat.map_coe] at h_combined
      -- `((m : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)` ⟹ `m = n`.
      have h_eq : (m : ℤ) = (n : ℤ) := by exact_mod_cast h_combined
      have h_mn : m = n := by exact_mod_cast h_eq
      rw [h_mn]
  -- Step 2: Apply `analyticOrderAt_eq_natCast` to extract the local form.
  exact (hf_an.analyticOrderAt_eq_natCast).mp h_an_order

/-! ### Topological-multiplicity content for the analytic case

The `R3` Rouché-style topological-multiplicity statement asks for an exact
preimage count `Set.ncard {z ∈ V \ {0} | g z = w} = k` near a zero of order
`k`. The full Rouché theorem (with `k > 1`) is **not** available at the pin —
mathlib has neither a general "preimage count = winding number" theorem nor an
"argument principle" giving exact-equality counts in the form needed.

The `k = 1` slice however **is** available: it is precisely the inverse
function theorem for one-variable analytic maps (i.e. local injectivity from
nonvanishing derivative). We discharge that slice honestly here. The general
`k ≥ 2` content remains the named gap — captured in
`localMultiplicity_eq_order_punctured_statement` below as a `Prop`-valued
`def` (not an `axiom`). -/

/-- **The order-1 case of the topological-multiplicity bridge.**

For an analytic function `g : ℂ → ℂ` with `g 0 = 0` and `deriv g 0 ≠ 0`, the
function `g` is locally injective on some neighborhood of `0`. (No use is
made of `g 0 = 0` in the proof — local injectivity follows from the
nonvanishing-derivative hypothesis alone via the inverse function theorem —
but the hypothesis is kept to match the calling shape from
`exists_local_normal_form_of_nonneg` with `k = 1`.)

This is the order-`k = 1` slice of the Rouché-style statement
`localMultiplicity_eq_order_punctured_statement`: when `k = 1`, the equation
`g z = w` has a *unique* solution near `0` for every `w` close enough to `0`,
so in particular the cardinality is `1`.

Proof: `AnalyticAt.hasStrictDerivAt` (from `Mathlib.Analysis.Calculus.FDeriv
.Analytic`) lifts `AnalyticAt` to `HasStrictDerivAt`. Since the strict
derivative `deriv g 0` is nonzero, `HasStrictDerivAt.hasStrictFDerivAt_equiv`
(from `Mathlib.Analysis.Calculus.Deriv.Inverse`) repackages the strict
derivative as a `ContinuousLinearEquiv`, and the inverse function theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph` in
`Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`) gives an
`OpenPartialHomeomorph` whose source is an open neighborhood of `0` on which
`g` is injective. -/
lemma localMultiplicity_one_locally_injective
    {g : ℂ → ℂ} (h : AnalyticAt ℂ g 0) (_h0 : g 0 = 0) (hd : deriv g 0 ≠ 0) :
    ∃ U ∈ nhds (0 : ℂ), Set.InjOn g U := by
  -- 1. Lift `AnalyticAt` to `HasStrictDerivAt` via the analytic-derivative bridge.
  have hsd : HasStrictDerivAt g (deriv g 0) 0 := h.hasStrictDerivAt
  -- 2. Repackage `HasStrictDerivAt` with nonvanishing derivative as
  --    `HasStrictFDerivAt` with a continuous-linear-equiv `f'`.
  have hsfd :
      HasStrictFDerivAt g
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv g 0) hd) :
          ℂ →L[ℂ] ℂ) 0 :=
    hsd.hasStrictFDerivAt_equiv hd
  -- 3. The inverse function theorem yields an `OpenPartialHomeomorph` whose
  --    `toFun` is `g`, with `0 ∈ source` and `source` open.
  let φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph g
  have h0_src : (0 : ℂ) ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  -- The source of an `OpenPartialHomeomorph` is open, so it is a neighborhood
  -- of any point it contains.
  have h_src_nhds : φ.source ∈ nhds (0 : ℂ) :=
    φ.open_source.mem_nhds h0_src
  -- And `φ` is injective on its source (the partial-equiv left-inverse property).
  have h_inj_φ : Set.InjOn (φ : ℂ → ℂ) φ.source := φ.injOn
  -- The coercion `(φ : ℂ → ℂ)` is definitionally `g` (`toOpenPartialHomeomorph_coe`).
  have h_coe : (φ : ℂ → ℂ) = g := hsfd.toOpenPartialHomeomorph_coe
  refine ⟨φ.source, h_src_nhds, ?_⟩
  -- Transport injectivity along the definitional equality.
  rw [← h_coe]
  exact h_inj_φ

end MMeromorphicAt

/-! ## The headline R3 statement (Prop-valued, not axiom)

`localMultiplicity_eq_localOrder_statement` packages the bridge between the
chart-coordinate local form (proven above) and the topological local
multiplicity (cardinality of `f⁻¹{w}` near `x` for `w` near `f x`).

We state it as a `Prop`-valued `def` (per the brief): the statement is
*meaningful* and unambiguous, but the discharge requires Rouché-style
counting that is not in mathlib at the pin. -/

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-- **Local multiplicity = local order.** For every meromorphic `f` and
every `x : X`, the chart-coordinate local form gives a unique `k = localOrder
I f x` with `f ∘ chart⁻¹ = (z - chart x)^k · g(z)` on a punctured neighborhood.
The classical assertion (R3) is that, when `k > 0`, the topological
multiplicity of `f` at `x` (cardinality of `f⁻¹ {w} ∩ U` for any sufficiently
small neighborhood `U` of `x` and any sufficiently close-to-`f x` value `w`)
equals `k.natAbs`.

We package this as the conjunction of:

* the chart-coordinate local form (proven above as
  `MMeromorphicAt.exists_local_normal_form`);
* the topological-multiplicity bridge (the actual count statement).

For the **bridge** we use the equivalent formulation: there exists an open
neighborhood `U` of `x` and a deleted neighborhood `V` of `f x` such that for
every `w ∈ V`, the set `{y ∈ U | f y = w}` has exactly `(localOrder I f x).natAbs`
elements (when the order is positive; the pole case is symmetric via
`f⁻¹`).

**Status.** Stated, not proven (the Rouché count). ⚠ The `f x = 0` hypothesis is
REQUIRED (added 2026-06-04): without it the statement is FALSE — `f x` is a junk value
on the punctured germ (e.g. `f z = z` for `z ≠ 0`, `f 0 = 5`: `localOrder = 1` yet
`f 0 ≠ 0`), while the count is centered at `f x`. Under `f x = 0` the honest content is
PROVEN in `RoucheBridge.lean` (`localMultiplicity_eq_localOrder_count_of_apply_eq_zero`). -/
def localMultiplicity_eq_localOrder_statement : Prop :=
  ∀ (f : X → ℂ) (_ : MMeromorphicOn (modelWithCornersSelf ℂ ℂ) f Set.univ)
    (_ : ∀ x, mmeromorphicOrderAt (modelWithCornersSelf ℂ ℂ) f x ≠ ⊤)
    (x : X),
    -- Positive-order (zero) case: the topological multiplicity at `x` over
    -- nearby values `w` is the natural-number absolute value of the local order.
    -- We use `Set.ncard` (cardinality of a `Set`, `0` for infinite sets) so
    -- the statement does not need a separate finiteness hypothesis embedded in
    -- the type. The implicit content of "for sufficiently nearby `w`, the count
    -- equals `k`" includes the assertion that the preimage set is finite (and
    -- so `ncard` is the honest cardinality).
    0 < localOrder (modelWithCornersSelf ℂ ℂ) f x → f x = 0 →
      ∃ (U : Set X) (V : Set ℂ),
        IsOpen U ∧ x ∈ U ∧
        IsOpen V ∧ f x ∈ V ∧
        ∀ w ∈ V, w ≠ f x →
          ({y ∈ U | f y = w} : Set X).ncard =
            (localOrder (modelWithCornersSelf ℂ ℂ) f x).natAbs

/-! ## Compatibility statement bridging `localOrder` to the existing
`R3_localMultiplicity_statement` in `ResidueTheorem.lean`

The R3 statement in `ResidueTheorem.lean` is the coarse "multiplicity ≥ 1"
form. We discharge it directly here, since it follows from the no-germ-zero
hypothesis and the fact that `Int.natAbs` of a nonzero integer is `≥ 1`. -/

/-- The coarse R3 statement (`R3_localMultiplicity_statement` in
`ResidueTheorem.lean`) is **unconditionally true** under the standing
hypothesis: if the integer order is nonzero, its absolute value is `≥ 1`.

This is the only piece of R3 that does not require classical analytic input;
it is purely arithmetic on `ℤ`. We prove it here so that `ResidueTheorem.lean`
can route through `localOrder` rather than hand-rolling the same statement. -/
theorem r3_natAbs_ge_one_of_ne_zero
    (k : ℤ) (hk : k ≠ 0) : k.natAbs ≥ 1 := by
  rcases Int.natAbs_pos.mpr hk with h
  exact h

/-! ## The general-`k` Rouché-style statement (Prop-only)

The general `k ≥ 1` case asserts that an analytic `g : ℂ → ℂ` with order
`k` at `0` has *exactly* `k` preimages of every nonzero value `w` close to
`0`, in some punctured neighborhood of `0`. This is the Rouché theorem
applied to `f(z) - w = (z - z₀)^k u(z) - w`.

At the mathlib pin (`8e3c989`, 15 April 2026) the precise gating input is
**not present**. The relevant pieces that *are* present:

* `Mathlib.Analysis.Analytic.IsolatedZeros.exists_eventuallyEq_pow_smul_nonzero_iff`
  — the local form `g z = (z - z₀)^n • h z` with `h(z₀) ≠ 0` (analytic case).
* `Mathlib.Analysis.Analytic.Order.AnalyticAt.analyticOrderAt_eq_natCast`
  — the same local form expressed via the order.
* `Mathlib.Analysis.Calculus.FDeriv.Analytic.AnalyticAt.hasStrictDerivAt`
  — analytic ⟹ strict derivative at the point.
* `Mathlib.Analysis.Calculus.Deriv.Inverse.HasStrictDerivAt.hasStrictFDerivAt_equiv`
  — strict derivative + nonzero ⟹ strict Fréchet derivative as an equiv.
* `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv.HasStrictFDerivAt.toOpenPartialHomeomorph`
  — the inverse function theorem packaged as an `OpenPartialHomeomorph`.

What is **deferred** for the general `k ≥ 2` case:

> A theorem of the form: for `g` analytic at `z₀` with `analyticOrderAt g z₀ = (k : ℕ∞)`
> and `k ≥ 1`, there exist neighborhoods `V` of `z₀` and `W` of `0` such that
> for every `w ∈ W \ {0}`,
> `Set.ncard {z ∈ V \ {z₀} | g z = w} = k`.

Mathlib does not name this. Candidate name in a future PR:
`AnalyticAt.exists_count_preimage_of_analyticOrderAt`. Existence in some form
would route via Rouché's theorem applied to `g - w` versus `(z - z₀)^k`,
combined with the open-mapping / strict-derivative-of-the-inverse argument.
The `k = 1` special case is `localMultiplicity_one_locally_injective` above
(the inverse function theorem suffices); `k ≥ 2` requires winding-number /
argument-principle content not in mathlib at the pin.

We therefore state the general case as a `Prop`-valued `def` (NOT an
`axiom`) so future filling does not contaminate the kernel. -/

/-- **The general-`k` Rouché-style statement, in `Prop`-only form.**

For `g : ℂ → ℂ` analytic at `0` with `analyticOrderAt g 0 = k` and `k ≥ 1`,
there exists `ε > 0` and a neighborhood `V` of `0` such that for every
non-zero `w` in the open ball of radius `ε`, the equation `g z = w` has
exactly `k` solutions in `V \ {0}`.

The hypotheses are packaged as the `→` body so the type-shape of the
statement is `Prop`-valued (not a function-type), matching the structural
convention used elsewhere in this repo for stated-but-unproven content
(`R3_localMultiplicity_statement` in `ResidueTheorem.lean`,
`R5_principal_degree_zero_statement`, etc.).

**Status:** stated, not proven. The `k = 1` slice is honest content in
`MMeromorphicAt.localMultiplicity_one_locally_injective`. The `k ≥ 2` slice
requires Rouché / argument-principle content not in mathlib at the pin
`8e3c989` (15 April 2026). -/
def localMultiplicity_eq_order_punctured_statement
    (k : ℕ) (g : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ g 0 → analyticOrderAt g 0 = (k : ℕ∞) → 1 ≤ k →
    ∃ ε > (0 : ℝ), ∃ V ∈ nhds (0 : ℂ),
      ∀ w ∈ Metric.ball (0 : ℂ) ε \ {0},
        ({z ∈ V \ {0} | g z = w} : Set ℂ).ncard = k

/-! ## The argument-principle chip (P3, 2026-05-05)

The discharge of `localMultiplicity_eq_order_punctured_statement` for `k ≥ 2`
classically routes through the **argument principle**: for `g` analytic at `0`
with `g(0) = 0` of order `k`, the contour integral

  `(1 / (2πi)) · ∮_{|z|=ε} g'(z) / (g(z) - w) dz = k`

for every `w` close to but not equal to `0`. This is the Rouché-style winding-
number count: the integrand is the logarithmic derivative of `g - w`, which has
`k` simple zeros (by the open-mapping / Rouché shift) in the disk and no poles,
so the integral counts those zeros.

At the mathlib pin `8e3c989` the argument principle in the form needed is not
named. The nearest mathlib content is `Complex.integral_circle_div_eq` and the
Cauchy integral formula for analytic functions, but the statement
"`(1 / 2πi) ∫ g'/g = (zero count − pole count)`" is not packaged generally.

We therefore name the precise gap as two `Prop`-valued statements:

1. `argumentPrinciple_disk_statement k g` — the disk-centred argument-principle
   integral identity itself. This is the mathlib gap.
2. `argumentPrinciple_implies_rouche_statement k g` — once (1) is available,
   it implies the Rouché-style preimage count
   `localMultiplicity_eq_order_punctured_statement`.

Both are stated as `def : Prop`, not `axiom`, so they are inert until
discharged. -/

namespace MMeromorphicAt

/-- **Argument-principle integral identity on a disk centred at `0`.**

For `g : ℂ → ℂ` analytic at `0` with `analyticOrderAt g 0 = k`, there exists
`ε₀ > 0` such that for every `ε ∈ (0, ε₀)` the contour integral

  `(1 / (2πi)) · ∮_{|z|=ε} (g'(z) / (g(z) - w)) dz = k`  (here `w := 0`)

equivalently (parametrising the circle by `θ ↦ ε e^{iθ}`),

  `(2πi)⁻¹ · ∫_{0}^{2π} (g'(εe^{iθ}) / g(εe^{iθ})) · (iε e^{iθ}) dθ = k`.

This is the classical argument principle specialised to `w = 0`. The general
"`w` close to `0`, `w ≠ 0`" version is the Rouché count, which follows by
applying this to `g - w` and using the open-mapping theorem.

**Status:** `Prop`-valued statement, not proven. The mathlib pin does not
package this identity at the level of generality required (although the
ingredients — `Complex.integral_circle_div_eq`, `MeromorphicAt.exists_eq_pow_smul`,
and Cauchy's theorem on a disk for analytic functions — are present in
adjacent files). The statement is named here so that the dependency surface
between the (R3) Rouché count and the mathlib gap is explicit.

The hypotheses are packaged as the `→` body so the type-shape is `Prop`-valued
(matching `R3_localMultiplicity_statement` and
`localMultiplicity_eq_order_punctured_statement` above). -/
def argumentPrinciple_disk_statement (k : ℕ) (g : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ g 0 ∧ analyticOrderAt g 0 = k →
    ∃ ε₀ > (0 : ℝ),
      ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
        (2 * Real.pi * Complex.I)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (deriv g (ε * Complex.exp (Complex.I * θ)) /
             g (ε * Complex.exp (Complex.I * θ))) *
            (ε * Complex.I * Complex.exp (Complex.I * θ))
          = k

/-- **The argument-principle integral on a disk implies the Rouché count.**

If the argument-principle identity (`argumentPrinciple_disk_statement`) holds
for `g`, then so does the Rouché-style preimage count statement
(`localMultiplicity_eq_order_punctured_statement`).

The bridge is classical: applying the argument principle to `g - w` for `w`
close to but not equal to `0`, the integral
`(1/2πi) ∮ (g - w)'/(g - w) dz` equals the number of zeros of `g - w` in the
disk, counted with multiplicity. By the open-mapping theorem (and continuity
of the integrand in `w`), this equals `k` for all sufficiently small nonzero
`w`. The simple-zero structure (each zero has multiplicity `1` for nonzero
`w`, since `(g - w)'(z₀) = g'(z₀) ≠ 0` away from the order-`k` zero of `g`)
turns the multiplicity-counted count into a set-cardinality count.

**Status:** `Prop`-valued statement, not proven. Discharging requires both
the argument-principle integral (above) and the Hurwitz / open-mapping
content for the simple-zero passage. Stated here to make the chain explicit:
once `argumentPrinciple_disk_statement` is filled, this implication closes
`localMultiplicity_eq_order_punctured_statement` for `k ≥ 2`, completing R3. -/
def argumentPrinciple_implies_rouche_statement (k : ℕ) (g : ℂ → ℂ) : Prop :=
  argumentPrinciple_disk_statement k g →
    localMultiplicity_eq_order_punctured_statement k g

/-! ### k = 0 trivial case of the argument principle (zero-free disk)

When `f : ℂ → ℂ` is holomorphic and **nonzero** everywhere on a closed disk
`closedBall z₀ r` with `0 < r`, the logarithmic derivative `deriv f / f` is
holomorphic on a neighborhood of the closed disk (no poles, since `f ≠ 0`).
Cauchy's theorem (Cauchy–Goursat) applied to `deriv f / f` then gives

  `∮_{|z - z₀| = r} (deriv f) z / f z dz = 0`.

This is the `k = 0` (no-zero, no-pole) leg of the argument principle, and it
is honestly proven below from `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`.
The general (k ≥ 1) case is deferred; see `argumentPrinciple_disk_statement`. -/

/-- **Argument principle, trivial (k = 0) case.**

If `f : ℂ → ℂ` is holomorphic on a neighborhood of the closed disk
`closedBall z₀ r` (with `0 ≤ r`) and is nonzero everywhere on that closed
disk, then the contour integral of the logarithmic derivative `f' / f`
around the boundary circle is zero:

  `∮_{|z - z₀| = r} (deriv f z) / f z  dz = 0`.

**Proof.** Where `f ≠ 0`, the function `deriv f / f` is differentiable
(`deriv f` is analytic by `AnalyticOnNhd.deriv`, and division by a nonvanishing
analytic function is analytic). Hence `deriv f / f` is differentiable on the
open ball and continuous on the closed ball, so Cauchy–Goursat
(`circleIntegral_eq_zero_of_differentiable_on_off_countable` with empty
exceptional set) gives the integral is zero. -/
theorem argumentPrinciple_disk_zero_case
    {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ r))
    (hne : ∀ z ∈ Metric.closedBall z₀ r, f z ≠ 0) :
    (∮ z in C(z₀, r), deriv f z / f z) = 0 := by
  -- `deriv f` is analytic on a neighborhood of the closed ball.
  have hf' : AnalyticOnNhd ℂ (deriv f) (Metric.closedBall z₀ r) := hf.deriv
  -- `deriv f / f` is analytic on a neighborhood of the closed ball, since `f ≠ 0` there.
  have hquot : AnalyticOnNhd ℂ (deriv f / f) (Metric.closedBall z₀ r) := by
    intro z hz
    exact (hf' z hz).div (hf z hz) (hne z hz)
  -- Continuous on the closed ball.
  have hcont : ContinuousOn (deriv f / f) (Metric.closedBall z₀ r) :=
    hquot.continuousOn
  -- Differentiable at every point of the open ball.
  have hdiff : ∀ z ∈ Metric.ball z₀ r,
      DifferentiableAt ℂ (deriv f / f) z := fun z hz =>
    (hquot z (Metric.ball_subset_closedBall hz)).differentiableAt
  -- Apply Cauchy–Goursat with empty exceptional set.
  have hzero : (∮ z in C(z₀, r), (deriv f / f) z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      (E := ℂ) (R := r) (c := z₀) (f := deriv f / f)
      (s := (∅ : Set ℂ)) hr Set.countable_empty hcont
      (fun z hz => hdiff z hz.1)
  -- `(deriv f / f) z = deriv f z / f z` definitionally (Pi division).
  simpa [Pi.div_apply] using hzero

end MMeromorphicAt

end Jacobians.Discharge

end
