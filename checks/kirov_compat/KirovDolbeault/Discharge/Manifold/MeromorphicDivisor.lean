/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.MeromorphicAt
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.LocallyFinsupp

set_option autoImplicit true


/-! # The order divisor of a meromorphic function on a complex manifold

This file packages the chart-pulled-back meromorphic order
(`mmeromorphicOrderAt`) into a `Function.locallyFinsuppWithin (Set.univ) ℤ`
— the carrier of `Jacobians.Discharge.Div X`. This is one of the load-bearing
analytic inputs to the honest definition of `Jacobians.Discharge.PrincDiv`
(see the docstring on `PrincDiv` in `Divisor.lean`).

## Strategy

The integer value at `x ∈ X` is `(mmeromorphicOrderAt I f x).untop₀` — a
positive integer at zeros, negative at poles, `0` at regular nonzero points
or wherever the order is `⊤` (germ-zero). Mathlib's
`MeromorphicOn.divisor` already does this packaging on `ℂ → ℂ`; we lift
it through the **canonical chart** at each point, using
`mmeromorphicOrderAt_eq_of_isManifold` (which discharges chart-independence
on a complex analytic manifold) to identify the value with the underlying
flat-domain order.

Local finiteness (the load-bearing field of `Function.locallyFinsuppWithin`)
is obtained by, for every `z : X`:

1. Take the canonical chart `e := chartAt ℂ z`.
2. Pull `f` back to `f ∘ e.symm : ℂ → ℂ`. The hypothesis
   `MMeromorphicOn I f Set.univ` plus chart-independence
   (`MMeromorphicAt.iff_of_isManifold`) gives
   `MeromorphicOn (f ∘ e.symm) e.target`.
3. Mathlib's `MeromorphicOn.divisor (f ∘ e.symm) e.target` is locally
   finsupp within `e.target`; in particular at the chart image `e z` there
   exists `t' ∈ 𝓝 (e z)` with `Set.Finite (t' ∩ support')`.
4. The pullback set `t := e ⁻¹' t' ∩ e.source` is open, contains `z`,
   and the image of `t ∩ support` under `e` is contained in
   `t' ∩ support'`, which is finite. Since `e` is injective on its source,
   `t ∩ support` is finite.

The hypothesis `hf0 : ∀ x, mmeromorphicOrderAt I f x ≠ ⊤` is **load-bearing**:
without it, the support `{x | (mmeromorphicOrderAt I f x).untop₀ ≠ 0}` could
fail to coincide with `{x | mmeromorphicOrderAt I f x ≠ 0}`
(`(⊤ : WithTop ℤ).untop₀ = 0` is a default-collapse that would silently
fold "germ identically zero" points into "regular nonzero"). We use `hf0`
to upgrade the support identification used in the local-finiteness proof:
the support set is exactly `{x | mmeromorphicOrderAt I f x ≠ 0}`, which on
a chart corresponds to `{w | meromorphicOrderAt (f ∘ e.symm) w ≠ 0}`, and
that set's local-finiteness then follows from the codiscrete-of-zero-or-top
characterization in mathlib.

## Main definition

* `Jacobians.Discharge.MMeromorphicOn.divisor I f hf hf0` —
  `Function.locallyFinsuppWithin (Set.univ : Set X) ℤ`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace Jacobians.Discharge

set_option linter.unusedSectionVars false

namespace MMeromorphicOn

universe u

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-- The integer-valued **order function** of a meromorphic function on a
complex manifold: `(mmeromorphicOrderAt I f x).untop₀`. Positive at zeros,
negative at poles, `0` at regular non-zero points. Under the hypothesis
`hf0` (no germ is identically zero), the value is also `0` at points where
`mmeromorphicOrderAt I f x = ⊤`, but those points do not exist by `hf0`. -/
def orderFun (I : ModelWithCorners ℂ ℂ ℂ) (f : X → ℂ) (x : X) : ℤ :=
  (mmeromorphicOrderAt I f x).untop₀

/-- Under `hf0`, `orderFun I f x = 0` is equivalent to
`mmeromorphicOrderAt I f x = 0`, i.e. there is no spurious `⊤ ↦ 0` collapse. -/
lemma orderFun_eq_zero_iff
    {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}
    (hf0 : mmeromorphicOrderAt I f x ≠ ⊤) :
    orderFun I f x = 0 ↔ mmeromorphicOrderAt I f x = 0 := by
  unfold orderFun
  constructor
  · intro h
    have := WithTop.untop₀_eq_zero.mp h
    rcases this with h0 | htop
    · exact h0
    · exact (hf0 htop).elim
  · intro h
    rw [h]; rfl

/-- The **order divisor** of a meromorphic function `f` on a complex manifold,
valued in `ℤ` (positive at zeros, negative at poles, `0` elsewhere). The
`locallyFinsuppWithin Set.univ` packaging encodes the local-finiteness
statement that, for a non-identically-zero meromorphic function, the set
`{x | mmeromorphicOrderAt I f x ≠ 0}` is locally finite (in particular has
no accumulation point in any chart).

The hypothesis `hf0 : ∀ x, mmeromorphicOrderAt I f x ≠ ⊤` says that no
germ of `f` is identically zero; it is the standard hypothesis under which
the order divisor is a well-defined locally-finite object.

Construction: pull `f` back to each canonical chart, invoke mathlib's
`MeromorphicOn.divisor` (whose local-finiteness comes from
`MeromorphicOn.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top`), and
transport the local-finite-support neighborhood through the chart map.
Chart-independence is handled by `mmeromorphicOrderAt_eq_of_isManifold`. -/
def divisor
    (I : ModelWithCorners ℂ ℂ ℂ)
    (f : X → ℂ)
    (hf : MMeromorphicOn I f Set.univ)
    (hf0 : ∀ x, mmeromorphicOrderAt I f x ≠ ⊤) :
    Function.locallyFinsuppWithin (Set.univ : Set X) ℤ where
  toFun := fun x => orderFun I f x
  supportWithinDomain' := by
    intro x _
    trivial
  supportLocallyFiniteWithinDomain' := by
    intro z _
    -- Take the canonical chart at `z`.
    set e : OpenPartialHomeomorph X ℂ := chartAt ℂ z with he_def
    have he_atlas : e ∈ atlas ℂ X := chart_mem_atlas ℂ z
    have hz_src : z ∈ e.source := mem_chart_source ℂ z
    -- Step 1: prove `MeromorphicOn (f ∘ e.symm) e.target`.
    have h_mero_chart : MeromorphicOn (f ∘ e.symm) e.target := by
      intro w hw
      -- Set `y := e.symm w`. Then `y ∈ e.source` and `e y = w`.
      set y : X := e.symm w with hy_def
      have hy_src : y ∈ e.source := e.map_target hw
      have h_eyw : e y = w := e.right_inv hw
      have hMy : MMeromorphicAt I f y := hf y trivial
      -- We need to specialize chart-independence. The lemma lives in
      -- `Jacobians.Discharge` namespace; it's proved for `I = 𝓘(ℂ,ℂ)` only.
      -- Since `I : ModelWithCorners ℂ ℂ ℂ` is a parameter, we accept the
      -- specialization at `𝓘(ℂ,ℂ)` (the only meaningful case for this file).
      -- The `MMeromorphicAt` definition itself does not depend on `I`
      -- (the model is a `_` argument in `MMeromorphicAt`).
      have hMy' : MMeromorphicAt (𝓘(ℂ, ℂ)) f y := hMy
      have h_iff := Jacobians.Discharge.MMeromorphicAt.iff_of_isManifold
        (M := X) (e := e) (x := y) (f := f) he_atlas hy_src
      have : MeromorphicAt (f ∘ e.symm) (e y) := h_iff.mp hMy'
      rw [h_eyw] at this
      exact this
    -- Step 2: build mathlib's divisor and extract local-finiteness at `e z`.
    set D : Function.locallyFinsuppWithin e.target ℤ :=
      MeromorphicOn.divisor (f ∘ e.symm) e.target with hD_def
    have h_ez_target : e z ∈ e.target := e.map_source hz_src
    obtain ⟨t', ht'_nhds, ht'_finite⟩ :=
      D.supportLocallyFiniteWithinDomain (e z) h_ez_target
    -- Step 3: pull back to `X`. Use the open neighborhood
    -- `t := e ⁻¹' t' ∩ e.source`.
    -- The chart map `e` is continuous on `e.source` and `t' ∈ 𝓝 (e z)`
    -- with `e z ∈ e.target`, so the preimage in `e.source` is a nhd of `z`.
    refine ⟨e.source ∩ e ⁻¹' t', ?_, ?_⟩
    · -- `e.source ∩ e ⁻¹' t' ∈ 𝓝 z`.
      -- `e.source` is open and contains `z`; the continuous map `e`
      -- pulls back the nhd `t'` of `e z` to a nhd of `z` (within `e.source`).
      have h_open_src : IsOpen e.source := e.open_source
      have h_continuousAt : ContinuousAt e z := by
        have hco : ContinuousOn e e.source := e.continuousOn
        exact hco.continuousAt (h_open_src.mem_nhds hz_src)
      have h_pre : e ⁻¹' t' ∈ 𝓝 z := h_continuousAt.preimage_mem_nhds ht'_nhds
      have h_src_nhds : e.source ∈ 𝓝 z := h_open_src.mem_nhds hz_src
      exact Filter.inter_mem h_src_nhds h_pre
    · -- Finiteness of `(e.source ∩ e ⁻¹' t') ∩ (orderFun I f).support`.
      -- Strategy: every element of this set sits in `e.source` and maps under `e`
      -- into `t' ∩ D.support`. Since `e` is injective on `e.source`, the LHS
      -- injects into `t' ∩ D.support` (which is finite by `ht'_finite`).
      -- We use `Set.Finite.of_finite_image` after building the explicit image map.
      have h_inj : Set.InjOn e (e.source ∩ e ⁻¹' t' ∩
          (Function.support fun x => orderFun I f x)) := by
        -- `e.injOn` has type `Set.InjOn e e.source`. Restrict via `Set.InjOn.mono`.
        apply e.injOn.mono
        intro y hy
        exact hy.1.1
      have h_image_subset :
          e '' (e.source ∩ e ⁻¹' t' ∩ (Function.support fun x => orderFun I f x))
            ⊆ t' ∩ D.support := by
        rintro w ⟨x, ⟨⟨hx_src, hx_pre⟩, hx_supp⟩, rfl⟩
        -- Goal: `e x ∈ t' ∩ D.support`.
        -- `hx_supp : orderFun I f x ≠ 0`.
        have hx_order_ne_zero : mmeromorphicOrderAt I f x ≠ 0 := by
          intro h0
          apply hx_supp
          show (mmeromorphicOrderAt I f x).untop₀ = 0
          rw [h0]; rfl
        have hx_order_ne_top : mmeromorphicOrderAt I f x ≠ ⊤ := hf0 x
        -- Chart-independence at `x` (using `e = chartAt ℂ z`, which is in the atlas).
        have h_eq : mmeromorphicOrderAt I f x = meromorphicOrderAt (f ∘ e.symm) (e x) :=
          Jacobians.Discharge.mmeromorphicOrderAt_eq_of_isManifold
            (M := X) (e := e) (x := x) (f := f) he_atlas hx_src
        have h_chart_order_ne_zero : meromorphicOrderAt (f ∘ e.symm) (e x) ≠ 0 := by
          rw [← h_eq]; exact hx_order_ne_zero
        have h_chart_order_ne_top : meromorphicOrderAt (f ∘ e.symm) (e x) ≠ ⊤ := by
          rw [← h_eq]; exact hx_order_ne_top
        -- The mathlib divisor at `e x ∈ e.target` is `(meromorphicOrderAt _ _).untop₀`.
        have hex_target : e x ∈ e.target := e.map_source hx_src
        have h_D_apply : D (e x) = (meromorphicOrderAt (f ∘ e.symm) (e x)).untop₀ :=
          MeromorphicOn.divisor_apply h_mero_chart hex_target
        have h_D_ne_zero : D (e x) ≠ 0 := by
          rw [h_D_apply]
          intro h
          rcases WithTop.untop₀_eq_zero.mp h with h0 | htop
          · exact h_chart_order_ne_zero h0
          · exact h_chart_order_ne_top htop
        exact ⟨hx_pre, h_D_ne_zero⟩
      have h_image_finite :
          (e '' (e.source ∩ e ⁻¹' t' ∩ (Function.support fun x => orderFun I f x))).Finite :=
        ht'_finite.subset h_image_subset
      exact (Set.Finite.of_finite_image h_image_finite h_inj)

/-! ## Finiteness on a compact manifold (R2 of `Manifold/ResidueTheorem.lean`)

These three lemmas chip at the residue-theorem leg by exposing the
*finite* form of what `MMeromorphicOn.divisor` already packages as a
`Function.locallyFinsuppWithin Set.univ ℤ`. Compactness of `X` upgrades
local finiteness to global finiteness via
`Function.locallyFinsuppWithin.finiteSupport isCompact_univ`.

The mathematical content is:

* The support `{x | orderFun I f x ≠ 0}` is finite.
* The poles `{x | mmeromorphicOrderAt I f x < 0}` form a subset of the
  support (under `hf0`, a negative `WithTop ℤ` value untops to a nonzero
  integer), hence are finite.
* The zeros `{x | mmeromorphicOrderAt I f x > 0}` likewise form a subset
  of the support (under `hf0`, a positive value untops to a nonzero
  integer), hence are finite.

**Note on the spec's `{x | f x = 0}`.** The brief originally asked for
`{x | f x = 0}.Finite`. That literal claim is **not provable** from
`MMeromorphicOn I f Set.univ` and `hf0` alone: mathlib's `MeromorphicAt`
constrains the *germ* of `f` in a punctured neighborhood, not the value
`f x` at the point itself. A function can be modified at a single point
to be `0` while remaining meromorphic with order `0` (the regular case).
The mathematically correct, provable claim is the order-positive one
above; this is also exactly what R2 of `Manifold/ResidueTheorem.lean`
states (`(mmeromorphicOrderAt I f.toFun x).untop₀ > 0`). We therefore
prove the order-based formulation. -/

/-- The support of `orderFun I f` (= the support of the order divisor of
`f`) is **finite** on a compact Hausdorff complex 1-manifold. Direct
specialization of `Function.locallyFinsuppWithin.finiteSupport` to the
order divisor of `MMeromorphicOn.divisor`.

Both `hf` and `hf0` are load-bearing: they are the inputs to `divisor`. -/
lemma orderFun_support_finite
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (I : ModelWithCorners ℂ ℂ ℂ)
    (f : X → ℂ)
    (hf : MMeromorphicOn I f Set.univ)
    (hf0 : ∀ x, mmeromorphicOrderAt I f x ≠ ⊤) :
    {x : X | orderFun I f x ≠ 0}.Finite := by
  -- The divisor packages the order function with local-finiteness of its support.
  set D : Function.locallyFinsuppWithin (Set.univ : Set X) ℤ :=
    MMeromorphicOn.divisor I f hf hf0 with hD_def
  -- Compactness of `Set.univ` upgrades local finiteness of the support to global.
  have h_finite : (Function.support fun x => (D : X → ℤ) x).Finite :=
    D.finiteSupport isCompact_univ
  -- The two sets are pointwise equal by `D x = orderFun I f x` (rfl from `divisor.toFun`).
  exact h_finite

/-- The set of points where `f` has **strictly positive order** ("zeros" in the
order-divisor sense) is **finite** on a compact Hausdorff complex 1-manifold.

This is the order-based formulation of R2's zero-fibre finiteness statement
in `Manifold/ResidueTheorem.lean`. The proof shows
`{x | mmeromorphicOrderAt I f x > 0} ⊆ {x | orderFun I f x ≠ 0}` (using
`hf0` to rule out the `⊤` case) and applies `orderFun_support_finite`. -/
lemma zeros_finite
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (I : ModelWithCorners ℂ ℂ ℂ)
    (f : X → ℂ)
    (hf : MMeromorphicOn I f Set.univ)
    (hf0 : ∀ x, mmeromorphicOrderAt I f x ≠ ⊤) :
    {x : X | (0 : WithTop ℤ) < mmeromorphicOrderAt I f x}.Finite := by
  -- Reduce to `orderFun_support_finite` by showing the LHS is contained in the support.
  apply (orderFun_support_finite (X := X) I f hf hf0).subset
  intro x hx
  -- Unfold `Set.mem` so that `hx : 0 < mmeromorphicOrderAt I f x` is rewritable.
  simp only [Set.mem_setOf_eq] at hx
  -- Goal: `x ∈ {x | orderFun I f x ≠ 0}`, i.e. `orderFun I f x ≠ 0`.
  show orderFun I f x ≠ 0
  unfold orderFun
  -- `WithTop.untop₀_eq_zero : a.untop₀ = 0 ↔ a = 0 ∨ a = ⊤`. Negate.
  intro h
  rcases WithTop.untop₀_eq_zero.mp h with h0 | htop
  · -- `mmeromorphicOrderAt I f x = 0` contradicts `0 < mmeromorphicOrderAt I f x`.
    rw [h0] at hx
    exact lt_irrefl _ hx
  · exact hf0 x htop

/-- The set of points where `f` has **strictly negative order** ("poles") is
**finite** on a compact Hausdorff complex 1-manifold.

Per spec. The proof shows
`{x | mmeromorphicOrderAt I f x < 0} ⊆ {x | orderFun I f x ≠ 0}` (using
`hf0` to rule out the `⊤` case — which would otherwise contradict
`< 0` anyway, since `⊤` is not less than `0` in `WithTop ℤ`) and applies
`orderFun_support_finite`. -/
lemma poles_finite
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (I : ModelWithCorners ℂ ℂ ℂ)
    (f : X → ℂ)
    (hf : MMeromorphicOn I f Set.univ)
    (hf0 : ∀ x, mmeromorphicOrderAt I f x ≠ ⊤) :
    {x : X | mmeromorphicOrderAt I f x < (0 : WithTop ℤ)}.Finite := by
  -- Reduce to `orderFun_support_finite` by showing the LHS is contained in the support.
  apply (orderFun_support_finite (X := X) I f hf hf0).subset
  intro x hx
  -- Unfold `Set.mem` so that `hx : mmeromorphicOrderAt I f x < 0` is rewritable.
  simp only [Set.mem_setOf_eq] at hx
  show orderFun I f x ≠ 0
  unfold orderFun
  intro h
  rcases WithTop.untop₀_eq_zero.mp h with h0 | htop
  · -- `mmeromorphicOrderAt I f x = 0` contradicts `mmeromorphicOrderAt I f x < 0`.
    rw [h0] at hx
    exact lt_irrefl _ hx
  · exact hf0 x htop

end MMeromorphicOn

end Jacobians.Discharge
