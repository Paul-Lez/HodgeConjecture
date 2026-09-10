/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Complex

set_option autoImplicit true


/-! # Meromorphic functions on a complex manifold

This file lifts mathlib's `MeromorphicAt` / `MeromorphicOn` / `meromorphicOrderAt`
machinery (defined for functions `𝕜 → E` with `𝕜` a nontrivially normed field)
onto a complex manifold modelled on `ℂ`.

The construction is a *chart pullback*: for `f : M → ℂ`, `x : M`, we declare `f`
to be meromorphic at `x` iff its chart representative
`f ∘ (chartAt ℂ x).symm : ℂ → ℂ` is meromorphic at `(chartAt ℂ x) x` in the
ordinary sense.

## Main definitions

* `MMeromorphicAt I f x` — `f : M → ℂ` is meromorphic at `x : M`.
* `MMeromorphicOn I f s` — `f` is meromorphic on `s : Set M`.
* `mmeromorphicOrderAt I f x : WithTop ℤ` — chart-pulled-back order.

## Why parametrize by `I` even though we hard-code the model `𝓘(ℂ, ℂ)`?

The Jacobian-Conjecture-relevant case is `I = 𝓘(ℂ, ℂ)`, the trivial model of
`ℂ` over itself. The chart-pullback construction makes sense for any
model with corners `I : ModelWithCorners ℂ ℂ ℂ`, and several intermediate
lemmas hold without analyticity of the model. We therefore keep `I` as a
parameter, but require `[ChartedSpace ℂ M]` so that chart codomains are
literally `ℂ` (not a generic model space `H`). This avoids having to write
`I.symm ∘ (chartAt H x) ∘ ...` everywhere.

## Notes

**Chart-independence of `MMeromorphicAt`** is proved in this file
(`MMeromorphicAt.iff_of_isManifold` / `mmeromorphicOrderAt_eq_of_isManifold`,
via `analyticAt_chart_transition_of_isManifold` and
`deriv_chart_transition_of_isManifold_ne_zero`): the chart-pullback
definition uses the canonical chart `chartAt ℂ x`, and the order is shown
independent of the chart via `compatible_of_mem_maximalAtlas` plus the
omega-pregroupoid characterization (`ContDiffOn ω` ↔ `AnalyticOn` for
`𝓘(ℂ, ℂ)`). Not provided here: `MMeromorphicOn.iUnion` and a `@[simp]`
`mMeromorphicOn_empty`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace Jacobians.Discharge

universe u

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace ℂ M]

/-! ## Definitions: chart-pullback meromorphic predicate -/

/-- `f : M → ℂ` is **meromorphic at `x : M`** iff its representative in the
canonical chart at `x`, namely `f ∘ (chartAt ℂ x).symm : ℂ → ℂ`, is
meromorphic at the chart image `(chartAt ℂ x) x` in the standard sense.

This is a chart-pullback definition. It is conditionally chart-independent
on a complex analytic manifold; the unconditional discharge is deferred (see
the file header). -/
def MMeromorphicAt (_I : ModelWithCorners ℂ ℂ ℂ) (f : M → ℂ) (x : M) : Prop :=
  MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)

/-- `f : M → ℂ` is **meromorphic on `s : Set M`** iff it is meromorphic at
each point of `s`. -/
def MMeromorphicOn (I : ModelWithCorners ℂ ℂ ℂ) (f : M → ℂ) (s : Set M) : Prop :=
  ∀ x ∈ s, MMeromorphicAt I f x

/-- The **order** of a meromorphic function `f : M → ℂ` at `x : M`, computed
by chart pullback. Returns `⊤` if `f` is identically zero in a punctured
neighborhood, a finite negative integer for poles, zero for regular nonzero
points, and a positive integer for zeros (matching `meromorphicOrderAt`'s
convention).

Chart-independence is deferred; see file header. -/
def mmeromorphicOrderAt (_I : ModelWithCorners ℂ ℂ ℂ) (f : M → ℂ) (x : M) :
    WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)

/-! ## Membership and pointwise lemmas -/

variable {I : ModelWithCorners ℂ ℂ ℂ}

lemma mMeromorphicOn_empty (f : M → ℂ) : MMeromorphicOn I f ∅ := by
  intro x hx; exact absurd hx hx.elim

lemma MMeromorphicOn.mono {f : M → ℂ} {s t : Set M}
    (h : MMeromorphicOn I f t) (hst : s ⊆ t) : MMeromorphicOn I f s :=
  fun x hx => h x (hst hx)

lemma MMeromorphicOn.union {f : M → ℂ} {s t : Set M}
    (hs : MMeromorphicOn I f s) (ht : MMeromorphicOn I f t) :
    MMeromorphicOn I f (s ∪ t) := by
  intro x hx
  rcases hx with hx | hx
  · exact hs x hx
  · exact ht x hx

/-! ## Algebraic operations: lifted from `MeromorphicAt` via chart pullback

These are immediate consequences of the underlying mathlib lemmas, since the
chart pullback `f ∘ (chartAt ℂ x).symm` is a ring/module homomorphism in `f`. -/

namespace MMeromorphicAt

variable {f g : M → ℂ} {x : M}

/-- The zero function is meromorphic at every point. -/
lemma zero : MMeromorphicAt I (0 : M → ℂ) x := by
  show MeromorphicAt ((0 : M → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (0 : M → ℂ) ∘ (chartAt ℂ x).symm = (fun _ => (0 : ℂ)) := rfl
  rw [h]
  exact analyticAt_const.meromorphicAt

/-- Constant functions are meromorphic. -/
lemma const (c : ℂ) : MMeromorphicAt I (fun _ : M => c) x := by
  show MeromorphicAt ((fun _ : M => c) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (fun _ : M => c) ∘ (chartAt ℂ x).symm = (fun _ => c) := rfl
  rw [h]
  exact analyticAt_const.meromorphicAt

lemma add (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f + g) x := by
  -- Unfold via `show`: `MMeromorphicAt I f x` reduces to `MeromorphicAt (f ∘ ...) (...)`.
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  show MeromorphicAt ((f + g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (f + g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) + (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact hf'.add hg'

lemma mul (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f * g) x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  show MeromorphicAt ((f * g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (f * g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) * (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact hf'.mul hg'

lemma neg (hf : MMeromorphicAt I f x) : MMeromorphicAt I (-f) x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  show MeromorphicAt ((-f) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (-f) ∘ (chartAt ℂ x).symm = -(f ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact hf'.neg

lemma sub (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f - g) x := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- Pointwise inverse of a meromorphic function is meromorphic. Mathlib's
`MeromorphicAt.inv` is unconditional (poles are absorbed into the meromorphic
class); the chart pullback transports this directly. -/
lemma inv (hf : MMeromorphicAt I f x) : MMeromorphicAt I f⁻¹ x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  show MeromorphicAt (f⁻¹ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : f⁻¹ ∘ (chartAt ℂ x).symm = (f ∘ (chartAt ℂ x).symm)⁻¹ := rfl
  rw [h]
  exact hf'.inv

/-- Pointwise quotient of two meromorphic functions is meromorphic. -/
lemma div (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f / g) x := by
  rw [div_eq_mul_inv]
  exact hf.mul hg.inv

/-- A natural-number power of a meromorphic function is meromorphic. -/
lemma pow (hf : MMeromorphicAt I f x) (n : ℕ) : MMeromorphicAt I (f ^ n) x := by
  induction n with
  | zero =>
    have h : (f ^ 0 : M → ℂ) = (fun _ : M => (1 : ℂ)) := by funext y; simp
    rw [h]
    exact MMeromorphicAt.const 1
  | succ m hm => simpa only [pow_succ] using hm.mul hf

/-- An integer power of a meromorphic function is meromorphic. -/
lemma zpow (hf : MMeromorphicAt I f x) (n : ℤ) : MMeromorphicAt I (f ^ n) x := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow m
  | negSucc m =>
    have h := (hf.pow (m + 1)).inv
    simpa only [zpow_negSucc] using h

/-- Finite products of `MMeromorphicAt` functions are `MMeromorphicAt`. -/
lemma prod {ι : Type*} {s : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ s, MMeromorphicAt I (F i) x) :
    MMeromorphicAt I (∏ i ∈ s, F i) x := by
  show MeromorphicAt ((∏ i ∈ s, F i) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (∏ i ∈ s, F i) ∘ (chartAt ℂ x).symm
      = (fun z => ∏ i ∈ s, F i ((chartAt ℂ x).symm z)) := by
    funext z
    simp [Finset.prod_apply]
  rw [h_comp]
  exact MeromorphicAt.fun_prod (fun i hi => hF i hi)

/-- Finite-prod variant: a function-valued `∏ i, F i z` is `MMeromorphicAt`. -/
lemma fun_prod {ι : Type*} {s : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ s, MMeromorphicAt I (F i) x) :
    MMeromorphicAt I (fun y => ∏ i ∈ s, F i y) x := by
  have h_eq : (fun y => ∏ i ∈ s, F i y) = ∏ i ∈ s, F i := by
    funext y; simp [Finset.prod_apply]
  rw [h_eq]
  exact prod hF

/-- Finite sums of `MMeromorphicAt` functions are `MMeromorphicAt`. -/
lemma sum {ι : Type*} {s : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ s, MMeromorphicAt I (F i) x) :
    MMeromorphicAt I (∑ i ∈ s, F i) x := by
  show MeromorphicAt ((∑ i ∈ s, F i) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (∑ i ∈ s, F i) ∘ (chartAt ℂ x).symm
      = (fun z => ∑ i ∈ s, F i ((chartAt ℂ x).symm z)) := by
    funext z
    simp [Finset.sum_apply]
  rw [h_comp]
  exact MeromorphicAt.fun_sum (fun i hi => hF i hi)

/-- Finite-sum variant: a function-valued `∑ i, F i z` is `MMeromorphicAt`. -/
lemma fun_sum {ι : Type*} {s : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ s, MMeromorphicAt I (F i) x) :
    MMeromorphicAt I (fun y => ∑ i ∈ s, F i y) x := by
  have h_eq : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
    funext y; simp [Finset.sum_apply]
  rw [h_eq]
  exact sum hF

/-- Multiplication of a meromorphic function by a complex scalar is
meromorphic. -/
lemma const_smul (c : ℂ) (hf : MMeromorphicAt I f x) :
    MMeromorphicAt I (c • f) x := by
  -- `c • f = (fun _ => c) * f` pointwise on `M → ℂ`.
  have h_eq : (c • f) = (fun _ : M => c) * f := by
    funext y; simp [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [h_eq]
  exact (MMeromorphicAt.const c).mul hf

end MMeromorphicAt

/-! ## Set-level closure under operations -/

namespace MMeromorphicOn

variable {f g : M → ℂ} {s : Set M}

lemma zero : MMeromorphicOn I (0 : M → ℂ) s :=
  fun _ _ => MMeromorphicAt.zero

lemma const (c : ℂ) : MMeromorphicOn I (fun _ : M => c) s :=
  fun _ _ => MMeromorphicAt.const c

lemma add (hf : MMeromorphicOn I f s) (hg : MMeromorphicOn I g s) :
    MMeromorphicOn I (f + g) s :=
  fun x hx => (hf x hx).add (hg x hx)

lemma mul (hf : MMeromorphicOn I f s) (hg : MMeromorphicOn I g s) :
    MMeromorphicOn I (f * g) s :=
  fun x hx => (hf x hx).mul (hg x hx)

lemma neg (hf : MMeromorphicOn I f s) : MMeromorphicOn I (-f) s :=
  fun x hx => (hf x hx).neg

lemma sub (hf : MMeromorphicOn I f s) (hg : MMeromorphicOn I g s) :
    MMeromorphicOn I (f - g) s :=
  fun x hx => (hf x hx).sub (hg x hx)

lemma inv (hf : MMeromorphicOn I f s) : MMeromorphicOn I f⁻¹ s :=
  fun x hx => (hf x hx).inv

lemma div (hf : MMeromorphicOn I f s) (hg : MMeromorphicOn I g s) :
    MMeromorphicOn I (f / g) s :=
  fun x hx => (hf x hx).div (hg x hx)

lemma pow (hf : MMeromorphicOn I f s) (n : ℕ) : MMeromorphicOn I (f ^ n) s :=
  fun x hx => (hf x hx).pow n

lemma zpow (hf : MMeromorphicOn I f s) (n : ℤ) : MMeromorphicOn I (f ^ n) s :=
  fun x hx => (hf x hx).zpow n

lemma const_smul (c : ℂ) (hf : MMeromorphicOn I f s) :
    MMeromorphicOn I (c • f) s :=
  fun x hx => (hf x hx).const_smul c

lemma prod {ι : Type*} {t : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ t, MMeromorphicOn I (F i) s) :
    MMeromorphicOn I (∏ i ∈ t, F i) s :=
  fun x hx => MMeromorphicAt.prod (fun i hi => hF i hi x hx)

lemma fun_prod {ι : Type*} {t : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ t, MMeromorphicOn I (F i) s) :
    MMeromorphicOn I (fun y => ∏ i ∈ t, F i y) s :=
  fun x hx => MMeromorphicAt.fun_prod (fun i hi => hF i hi x hx)

lemma sum {ι : Type*} {t : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ t, MMeromorphicOn I (F i) s) :
    MMeromorphicOn I (∑ i ∈ t, F i) s :=
  fun x hx => MMeromorphicAt.sum (fun i hi => hF i hi x hx)

lemma fun_sum {ι : Type*} {t : Finset ι} {F : ι → M → ℂ}
    (hF : ∀ i ∈ t, MMeromorphicOn I (F i) s) :
    MMeromorphicOn I (fun y => ∑ i ∈ t, F i y) s :=
  fun x hx => MMeromorphicAt.fun_sum (fun i hi => hF i hi x hx)

end MMeromorphicOn

/-! ## Chart independence

The chart-pullback definition `MMeromorphicAt I f x` uses the *canonical* chart
`chartAt ℂ x`. This section shows that any other chart `e` from the atlas with
`x ∈ e.source` gives the same answer, **conditional on** the chart-transition
map being analytic with non-vanishing derivative at `e x`. On a complex
analytic manifold (`[IsManifold I ω M]` with `I = 𝓘(ℂ, ℂ)`), those hypotheses
hold automatically; the discharge is documented at the bottom of this section
and is the only piece *still* deferred (see `OPEN.md`).

The mathematical content reduces to the mathlib lemmas
`meromorphicAt_comp_iff_of_deriv_ne_zero` and
`meromorphicOrderAt_comp_of_deriv_ne_zero`, both in
`Mathlib/Analysis/Meromorphic/Order.lean`. The non-trivial bookkeeping is the
local rewrite of
`(f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm) = f ∘ e.symm`
on a neighborhood of `e x`, which we discharge via continuity of `e.symm` and
`(chartAt ℂ x).left_inv` together with `MeromorphicAt.meromorphicAt_congr`. -/

section ChartIndependence

variable {f : M → ℂ} {x : M} {e : OpenPartialHomeomorph M ℂ}

/-- A neighborhood-of-`e x` rewrite for the doubly-pulled-back representative.
On every `y ∈ e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source`, the function
`(f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)` agrees with
`f ∘ e.symm`. -/
lemma comp_chart_transition_eqOn (_hxe : x ∈ e.source) :
    Set.EqOn ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm))
      (f ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source) := by
  intro y hy
  have hy_chart_src : e.symm y ∈ (chartAt ℂ x).source := hy.2
  -- Apply `(chartAt ℂ x).left_inv` to collapse the inner pair.
  show f ((chartAt ℂ x).symm ((chartAt ℂ x) (e.symm y))) = f (e.symm y)
  rw [(chartAt ℂ x).left_inv hy_chart_src]

/-- The set on which the doubly-pulled-back representative agrees with the
single-chart representative is a neighborhood of `e x`. -/
lemma comp_chart_transition_mem_nhds (hxe : x ∈ e.source) :
    e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source ∈ nhds (e x) := by
  refine Filter.inter_mem ?_ ?_
  · exact e.open_target.mem_nhds (e.map_source hxe)
  · -- `(chartAt ℂ x).source` is open and contains `e.symm (e x) = x`.
    have h_continuousAt : ContinuousAt e.symm (e x) := by
      have : ContinuousOn e.symm e.target := e.continuousOn_invFun
      exact (this.continuousAt (e.open_target.mem_nhds (e.map_source hxe)))
    apply h_continuousAt.preimage_mem_nhds
    rw [e.left_inv hxe]
    exact (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)

/-- **Chart independence of `MMeromorphicAt`.** If `e` is any chart with
`x ∈ e.source`, and the transition `(chartAt ℂ x) ∘ e.symm` is analytic at
`e x` with nonzero derivative, then `MMeromorphicAt I f x` is equivalent to
the standard meromorphy of `f ∘ e.symm` at `e x`.

Both hypotheses are automatic on a complex analytic manifold (chart
transitions are analytic biholomorphisms); see
`analyticAt_chart_transition_of_atlas` (still open) for the discharge. -/
lemma MMeromorphicAt.iff_of_chart
    (hxe : x ∈ e.source)
    (h_an : AnalyticAt ℂ ((chartAt ℂ x) ∘ e.symm) (e x))
    (h_deriv : deriv ((chartAt ℂ x) ∘ e.symm) (e x) ≠ 0) :
    MMeromorphicAt I f x ↔ MeromorphicAt (f ∘ e.symm) (e x) := by
  -- Step 1: unfold the LHS.
  show MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ↔ _
  -- Step 2: rewrite `(chartAt ℂ x) x` as `((chartAt ℂ x) ∘ e.symm) (e x)`.
  have h_pt : ((chartAt ℂ x) ∘ e.symm) (e x) = (chartAt ℂ x) x := by
    show (chartAt ℂ x) (e.symm (e x)) = (chartAt ℂ x) x
    rw [e.left_inv hxe]
  rw [← h_pt]
  -- Step 3: `meromorphicAt_comp_iff_of_deriv_ne_zero` gives the comparison
  -- between `f ∘ (chartAt ℂ x).symm` at the transition image and the
  -- composition `(f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)` at `e x`.
  rw [← meromorphicAt_comp_iff_of_deriv_ne_zero h_an h_deriv]
  -- Step 4: replace the doubly-pulled-back representative by `f ∘ e.symm`
  -- using eventual equality on the neighborhood from `comp_chart_transition_*`.
  apply MeromorphicAt.meromorphicAt_congr
  -- Build an `EventuallyEq` at `𝓝 (e x)`, then drop to the punctured filter.
  have h_nhds :
      ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)) =ᶠ[nhds (e x)]
        (f ∘ e.symm) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source,
       comp_chart_transition_mem_nhds hxe,
       comp_chart_transition_eqOn hxe⟩
  exact h_nhds.filter_mono nhdsWithin_le_nhds

/-- **Chart independence of `mmeromorphicOrderAt`.** Under the same hypotheses
as `iff_of_chart`, the order computed by chart pullback at the canonical chart
agrees with the standard `meromorphicOrderAt` of `f ∘ e.symm` at `e x`. -/
lemma mmeromorphicOrderAt_eq_of_chart
    (hxe : x ∈ e.source)
    (h_an : AnalyticAt ℂ ((chartAt ℂ x) ∘ e.symm) (e x))
    (h_deriv : deriv ((chartAt ℂ x) ∘ e.symm) (e x) ≠ 0) :
    mmeromorphicOrderAt I f x = meromorphicOrderAt (f ∘ e.symm) (e x) := by
  -- Step 1: unfold the LHS.
  show meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = _
  -- Step 2: rewrite the basepoint via `e.left_inv`.
  have h_pt : ((chartAt ℂ x) ∘ e.symm) (e x) = (chartAt ℂ x) x := by
    show (chartAt ℂ x) (e.symm (e x)) = (chartAt ℂ x) x
    rw [e.left_inv hxe]
  rw [← h_pt]
  -- Step 3: invoke the deriv-ne-zero composition order formula. This rewrites
  -- `meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (((chartAt ℂ x) ∘ e.symm) (e x))`
  -- into `meromorphicOrderAt ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)) (e x)`.
  rw [← meromorphicOrderAt_comp_of_deriv_ne_zero h_an h_deriv]
  -- Step 4: rewrite the composed function pointwise on a neighborhood.
  apply meromorphicOrderAt_congr
  have h_nhds :
      ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)) =ᶠ[nhds (e x)]
        (f ∘ e.symm) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source,
       comp_chart_transition_mem_nhds hxe,
       comp_chart_transition_eqOn hxe⟩
  exact h_nhds.filter_mono nhdsWithin_le_nhds

/-! ### Discharge of the analyticity hypothesis on a complex analytic manifold

On a complex analytic manifold `[ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]`,
the hypotheses `AnalyticAt ℂ ((chartAt ℂ x) ∘ e.symm) (e x)` and the
`deriv ≠ 0` condition are automatic for any chart `e ∈ atlas ℂ M` with
`x ∈ e.source`. We discharge them via the structure-groupoid API:

* `compatible_of_mem_maximalAtlas` gives `e.symm ≫ₕ e' ∈ contDiffGroupoid ω 𝓘(ℂ,ℂ)`,
* `mem_groupoid_of_pregroupoid` unfolds membership to the pregroupoid property,
* for `𝓘(ℂ, ℂ)` the model and its inverse are the identity (`modelWithCornersSelf_coe`
  / `_coe_symm` are `id`) and `range 𝓘(ℂ,ℂ) = univ` (Boundaryless),
* `ContDiffOn.analyticOn` upgrades `ContDiffOn ℂ ω` to `AnalyticOn ℂ`,
* `AnalyticOn.analyticAt` extracts pointwise analyticity using that the
  source is open (hence a neighborhood of any of its points).

For the derivative non-vanishing condition, applying the analyticity result
in both directions yields `(e ∘ e'.symm) ∘ (e' ∘ e.symm) =ᶠ[𝓝 (e x)] id`,
and the chain-rule product equals `deriv id (e x) = 1 ≠ 0`. -/

/-- The chart transition between two charts in the atlas of a complex analytic
manifold is analytic at every interior point of its source. This is the
unconditional discharge of the analyticity hypothesis used by
`MMeromorphicAt.iff_of_chart` and `mmeromorphicOrderAt_eq_of_chart`. -/
lemma analyticAt_chart_transition_of_isManifold
    [IsManifold 𝓘(ℂ, ℂ) ω M]
    {e e' : OpenPartialHomeomorph M ℂ}
    (he : e ∈ atlas ℂ M) (he' : e' ∈ atlas ℂ M)
    {x : M} (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ e.symm) (e x) := by
  -- Membership of the transition map in `contDiffGroupoid ω 𝓘(ℂ, ℂ)`.
  have h_compat : e.symm ≫ₕ e' ∈ contDiffGroupoid ω (𝓘(ℂ, ℂ)) :=
    StructureGroupoid.compatible_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas _ he)
      (StructureGroupoid.subset_maximalAtlas _ he')
  -- Unfold to pregroupoid membership.
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h_compat
  obtain ⟨h_fwd, _⟩ := h_compat
  -- `h_fwd : ContDiffOn ℂ ω (𝓘(ℂ,ℂ) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℂ,ℂ).symm)
  --                          (𝓘(ℂ,ℂ).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range 𝓘(ℂ,ℂ))`.
  -- Simplify the model: `𝓘(ℂ,ℂ)` and `𝓘(ℂ,ℂ).symm` reduce to `id`; `range id = univ`.
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, preimage_id_eq, id_eq,
    Set.range_id, inter_univ] at h_fwd
  -- `h_fwd : ContDiffOn ℂ ω (e.symm ≫ₕ e') (e.symm ≫ₕ e').source`.
  have h_an_on : AnalyticOn ℂ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source :=
    h_fwd.analyticOn
  -- `(e.symm ≫ₕ e' : ℂ → ℂ) = e' ∘ e.symm` definitionally (via `coe_trans`).
  have h_coe : ((e.symm ≫ₕ e') : ℂ → ℂ) = e' ∘ e.symm :=
    OpenPartialHomeomorph.coe_trans _ _
  rw [h_coe] at h_an_on
  -- The source is open and contains `e x`: it equals `e.target ∩ e.symm ⁻¹' e'.source`.
  have h_src_open : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  have h_ex_mem : e x ∈ (e.symm ≫ₕ e').source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · -- `e x ∈ e.symm.source = e.target`.
      simpa [OpenPartialHomeomorph.symm_source] using e.map_source hxe
    · -- `e.symm (e x) = x ∈ e'.source`.
      show e.symm (e x) ∈ e'.source
      rw [e.left_inv hxe]; exact hxe'
  exact h_an_on.analyticAt (h_src_open.mem_nhds h_ex_mem)

/-- The derivative of the chart transition between two atlas charts is nonzero
at every interior point of its source on a complex analytic manifold. -/
lemma deriv_chart_transition_of_isManifold_ne_zero
    [IsManifold 𝓘(ℂ, ℂ) ω M]
    {e e' : OpenPartialHomeomorph M ℂ}
    (he : e ∈ atlas ℂ M) (he' : e' ∈ atlas ℂ M)
    {x : M} (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    deriv (e' ∘ e.symm) (e x) ≠ 0 := by
  -- Forward analyticity at `e x`.
  have h_an_fwd : AnalyticAt ℂ (e' ∘ e.symm) (e x) :=
    analyticAt_chart_transition_of_isManifold he he' hxe hxe'
  -- Backward analyticity at `e' x`.
  have h_an_bwd : AnalyticAt ℂ (e ∘ e'.symm) (e' x) :=
    analyticAt_chart_transition_of_isManifold he' he hxe' hxe
  -- The composition `(e ∘ e'.symm) ∘ (e' ∘ e.symm)` equals `id` on a neighborhood of `e x`.
  -- Build the witness set: `e.target ∩ e.symm ⁻¹' e'.source`.
  set U : Set ℂ := e.target ∩ e.symm ⁻¹' e'.source with hU
  have hU_open : IsOpen U := e.isOpen_inter_preimage_symm e'.open_source
  have hex_mem : e x ∈ U := by
    refine ⟨e.map_source hxe, ?_⟩
    show e.symm (e x) ∈ e'.source
    rw [e.left_inv hxe]; exact hxe'
  have h_eqOn : Set.EqOn ((e ∘ e'.symm) ∘ (e' ∘ e.symm)) id U := by
    intro y hy
    have hy_target : y ∈ e.target := hy.1
    have hy_pre : e.symm y ∈ e'.source := hy.2
    show e (e'.symm (e' (e.symm y))) = id y
    rw [e'.left_inv hy_pre, e.right_inv hy_target]
    rfl
  have h_evEq : ((e ∘ e'.symm) ∘ (e' ∘ e.symm)) =ᶠ[nhds (e x)] id :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU_open.mem_nhds hex_mem, h_eqOn⟩
  -- Differentiability at the relevant points.
  have h_diff_fwd : DifferentiableAt ℂ (e' ∘ e.symm) (e x) := h_an_fwd.differentiableAt
  -- We need backward differentiability at `(e' ∘ e.symm) (e x) = e' x`.
  have h_pt : (e' ∘ e.symm) (e x) = e' x := by
    show e' (e.symm (e x)) = e' x
    rw [e.left_inv hxe]
  have h_diff_bwd : DifferentiableAt ℂ (e ∘ e'.symm) ((e' ∘ e.symm) (e x)) := by
    rw [h_pt]; exact h_an_bwd.differentiableAt
  -- Chain rule: `deriv ((e ∘ e'.symm) ∘ (e' ∘ e.symm)) (e x)
  --             = deriv (e ∘ e'.symm) ((e' ∘ e.symm) (e x)) * deriv (e' ∘ e.symm) (e x)`.
  have h_chain : deriv ((e ∘ e'.symm) ∘ (e' ∘ e.symm)) (e x)
      = deriv (e ∘ e'.symm) ((e' ∘ e.symm) (e x)) * deriv (e' ∘ e.symm) (e x) :=
    deriv_comp (e x) h_diff_bwd h_diff_fwd
  -- LHS via `EventuallyEq.deriv_eq` equals `deriv id (e x) = 1`.
  have h_lhs : deriv ((e ∘ e'.symm) ∘ (e' ∘ e.symm)) (e x) = 1 := by
    rw [h_evEq.deriv_eq, deriv_id]
  -- Combine: product equals 1, so neither factor is zero.
  intro h_zero
  rw [h_chain, h_zero, mul_zero] at h_lhs
  exact one_ne_zero h_lhs.symm

/-- **Unconditional chart independence of `MMeromorphicAt`.** For any chart
`e ∈ atlas ℂ M` of a complex analytic manifold containing `x` in its source,
`MMeromorphicAt I f x` is equivalent to ordinary meromorphy of `f ∘ e.symm`
at `e x`. Specializes `MMeromorphicAt.iff_of_chart` by discharging the
analyticity and derivative-non-vanishing hypotheses on
`[IsManifold 𝓘(ℂ, ℂ) ω M]`. -/
lemma MMeromorphicAt.iff_of_isManifold
    [IsManifold 𝓘(ℂ, ℂ) ω M]
    (he : e ∈ atlas ℂ M)
    (hxe : x ∈ e.source) :
    MMeromorphicAt 𝓘(ℂ, ℂ) f x ↔ MeromorphicAt (f ∘ e.symm) (e x) := by
  -- Apply `iff_of_chart` with the now-discharged hypotheses, using the canonical chart for `x`.
  have h_can : chartAt ℂ x ∈ atlas ℂ M := chart_mem_atlas ℂ x
  have h_xcan : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  exact MMeromorphicAt.iff_of_chart hxe
    (analyticAt_chart_transition_of_isManifold he h_can hxe h_xcan)
    (deriv_chart_transition_of_isManifold_ne_zero he h_can hxe h_xcan)

/-- **Unconditional chart independence of `mmeromorphicOrderAt`.** For any chart
`e ∈ atlas ℂ M` of a complex analytic manifold containing `x` in its source,
the chart-pullback order equals the ordinary `meromorphicOrderAt` of `f ∘ e.symm`
at `e x`. -/
lemma mmeromorphicOrderAt_eq_of_isManifold
    [IsManifold 𝓘(ℂ, ℂ) ω M]
    (he : e ∈ atlas ℂ M)
    (hxe : x ∈ e.source) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) f x = meromorphicOrderAt (f ∘ e.symm) (e x) := by
  have h_can : chartAt ℂ x ∈ atlas ℂ M := chart_mem_atlas ℂ x
  have h_xcan : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  exact mmeromorphicOrderAt_eq_of_chart hxe
    (analyticAt_chart_transition_of_isManifold he h_can hxe h_xcan)
    (deriv_chart_transition_of_isManifold_ne_zero he h_can hxe h_xcan)

end ChartIndependence

end Jacobians.Discharge
