/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.MultiplicityPatching

/-!
# Constructing the multiplicity-patching supply: the `deg_div` endgame

This file performs the manifold-assembly endgame for `deg_div`.  It banks — fully
complete and axiom-clean — every layer of the conservation-of-number assembly
*except* the irreducible per-sheet analytic content, which it isolates into the
structure `LocalMultiplicitySheets f w₀`.  A pointwise supply
`∀ w₀, LocalMultiplicitySheets f w₀` is fed through the proven wire
(`exists_properMapDegree_of_pointwiseMultiplicityPatching`) to the Riemann–Roch
keystone

> `∃ d : ℕ, zerosCount f = d ∧ polesCount f = d`   (`exists_properMapDegree_of_localSheets`).

## The banked pieces (complete, axiom-clean)

* **Special-fibre identities** (`fibreMult_zero_eq_zerosCount`,
  `fibreMult_infty_eq_polesCount`): the genuine local-degree sums over the two
  special fibres equal the with-multiplicity counts.  These are *pure
  reindexing* — `localDeg f (coe 0) x = orderAtPoint f x`,
  `localDeg f ∞ x = −orderAtPoint f x`, and the fibre over `coe 0` (resp. `∞`)
  contains the zeros (resp. is exactly the poles), with the order-`0` points
  contributing nothing.  No analytic input.  *(This is the highest-value piece;
  it frees the `N_eq_fibreMult` field of `MultiplicityPatchingData` of all
  special-value bookkeeping.)*
* **`N f = fibreMult f` everywhere** (`N_eq_fibreMult_everywhere`): the two
  special-value plugs of `N` *equal* the genuine multiplicity sums there, so
  `N f` is literally the fibre-multiplicity function.
* **The `localDeg` ↔ chart-pullback-order bridge** (`localDeg_coe_eq_chartPullback_order`):
  via the shift meromorphic function `shiftMero f c` and the *proven*
  chart-invariance `orderAtPoint_chart_invariant`, the local degree of `F` over a
  finite value `coe c` at a preimage `y` is read through *any* atlas chart — the
  summand half of the per-sheet conservation `sheetMult_eq`.
* **The no-escape / disjointness / finiteness-shrinking skeleton**
  (`MultiplicityPatchingData.ofDisjointSheets`): from pairwise-disjoint sheets
  with per-sheet conservation and a fibre-finiteness value-neighbourhood, the
  proper-map compactness argument builds the common neighbourhood `W` with
  no-escape and persistent conservation/finiteness.  This reduces the per-`w₀`
  obligation to the *purely local* `LocalMultiplicitySheets`.

## The isolated wall (`LocalMultiplicitySheets`)

The single remaining input is `∀ w₀, LocalMultiplicitySheets f w₀`: per fibre
point, a chart-ball sheet with the per-sheet multiplicity conservation
`∑_{y ∈ U x ∩ F⁻¹(w)} localDeg f w y = m x` for `w` near `w₀`, pairwise-disjoint
sheets, and fibre finiteness over a value-neighbourhood.  This is the genuine
§17.9 analytic content, to be built from the per-chart normal-form split
`Planar.orderSum_eq_of_analyticOrder` (the `m`-fold simple-root multiplicity sum,
already proven), the `localDeg` chart-pullback bridge above, the proper-map fibre
finiteness, and T2 separation of the finite fibre.  It is a *true, non-vacuous*
obligation — at a value off `range F` the empty datum satisfies it
(`LocalMultiplicitySheets.ofNotMemRange`), so it is never a disguised `False`.

## References

* Forster, *Lectures on Riemann Surfaces*, §4 (the degree), Cor. 4.24–4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, §II.4 (conservation of number).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset OnePoint Filter

namespace Jacobians.MultiplicityPatchingConstruct

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.MultiplicityPatching

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The constant meromorphic function and the `localDeg` ↔ `orderAtPoint` bridge

`localDeg f (coe c) y` is the chart-pullback order of `z ↦ f(z) − c` at `y`.
Realising the shift `f − c` as the meromorphic function `f − constMero c` lets us
identify `localDeg f (coe c) y = orderAtPoint (f − constMero c) y` — and hence,
via the *proven* chart-invariance `orderAtPoint_chart_invariant`, read off
`localDeg` through *any* chart, not just the one at `y`.  This is the summand
half of the per-sheet conservation `sheetMult_eq`: the chart-at-`x` order sum of
`Planar.orderSum_eq_of_analyticOrder` matches the per-preimage `localDeg`
(computed in the chart at the preimage). -/

/-- The shift `f − c` as a meromorphic function (built directly, independent of
the `Sub (MeromorphicFunction X)` instance). -/
noncomputable def shiftMero (f : MeromorphicFunction X) (c : ℂ) : MeromorphicFunction X :=
  ⟨fun x => f.toFun x - c, fun x => by
    have h := f.meromorphic x
    have hc : MeromorphicAt (fun _ : ℂ => c) ((chartAt (H := ℂ) x) x) := MeromorphicAt.const c _
    -- `(fun x => f x − c) ∘ chart.symm = f ∘ chart.symm − (fun _ => c)`.
    have : (fun x => f.toFun x - c) ∘ (chartAt (H := ℂ) x).symm
        = (f.toFun ∘ (chartAt (H := ℂ) x).symm) - (fun _ => c) := by
      ext z; simp [Function.comp]
    rw [this]
    exact h.sub hc⟩

@[simp] lemma shiftMero_toFun (f : MeromorphicFunction X) (c : ℂ) :
    (shiftMero f c).toFun = fun x => f.toFun x - c := rfl

/-- **`localDeg` at a finite value as an `orderAtPoint` of the shift `f − c`.**

`localDeg f (coe c) y = orderAtPoint (shiftMero f c) y`.  Both are
`(meromorphicOrderAt (z ↦ f(chart_y.symm z) − c) (chart_y y)).untop₀` — the order
of vanishing of `f − c` at `y`, read in the chart at `y`.  This is *definitional*
(`shiftMero` plugs the constant `c` into the subtraction). -/
lemma localDeg_coe_eq_orderAtPoint_sub (f : MeromorphicFunction X) (c : ℂ) (y : X) :
    localDeg f ((c : ℂ) : RiemannSphere) y
      = MeromorphicFunction.orderAtPoint (shiftMero f c) y := by
  rw [MeromorphicFunction.orderAtPoint]
  show (meromorphicOrderAt (fun z => f.toFun ((chartAt (H := ℂ) y).symm z) - c)
      ((chartAt (H := ℂ) y) y)).untop₀
    = (meromorphicOrderAt ((shiftMero f c).toFun ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y)).untop₀
  rfl

/-- **Chart-invariant reading of `localDeg` at a finite value.**

For `y` in the source of *any* atlas chart `e`, the local degree of `F` over
`coe c` at `y` is the order of `z ↦ f(e.symm z) − c` at `e y`.  This is the
proven chart-invariance `orderAtPoint_chart_invariant` applied to the shift
`shiftMero f c`; it is what lets the chart-at-`x` order sum of the planar
normal form be matched, preimage by preimage, against the intrinsic `localDeg`. -/
lemma localDeg_coe_eq_chartPullback_order (f : MeromorphicFunction X) (c : ℂ) {y : X}
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (hy : y ∈ e.source) :
    localDeg f ((c : ℂ) : RiemannSphere) y
      = (meromorphicOrderAt (fun z => f.toFun (e.symm z) - c) (e y)).untop₀ := by
  rw [localDeg_coe_eq_orderAtPoint_sub,
    ← MeromorphicFunction.orderAtPoint_chart_invariant (shiftMero f c) e he hy]
  rfl

/-! ### The special-fibre identities (fallback step 1)

The fibre-multiplicity sums over the two special values `coe 0` and `∞` equal the
with-multiplicity counts `zerosCount f` and `polesCount f`.  These are the
highest-value banked pieces; they require *no* analytic content — only the
re-indexing of the order-sum from the (finite) fibre to the divisor support. -/

/-- The fibre over `∞` is finite (it is exactly the poles `{x | order x < 0}`,
finite on a compact `X`). -/
lemma fibre_infty_finite (f : MeromorphicFunction X) :
    (f.toRiemannSphere ⁻¹' {OnePoint.infty}).Finite := by
  rw [f.toRiemannSphere_preimage_infty]
  exact f.finite_poles

/-- **Special-fibre identity at `∞`:** the genuine local-degree sum over the
pole fibre `F⁻¹(∞)` equals `polesCount f`.

`F⁻¹(∞) = {x | order x < 0}` (the poles) and `localDeg f ∞ x = −order x`, so the
sum is `∑_{x : order x < 0} (−order x)`.  Reindexing this finite-set sum onto the
divisor support (where the extra points all have `order = 0`, hence are excluded
by the `order < 0` filter) gives `polesCount f` verbatim. -/
lemma fibreMult_infty_eq_polesCount (f : MeromorphicFunction X) :
    fibreMult f OnePoint.infty = polesCount f := by
  classical
  -- Unfold `fibreMult` and rewrite the fibre as the pole set.
  rw [fibreMult]
  have hfib : f.toRiemannSphere ⁻¹' {OnePoint.infty} = {x | f.orderAtPoint x < 0} :=
    f.toRiemannSphere_preimage_infty
  rw [hfib]
  -- The pole set is finite; turn the finsum into a Finset sum over its `toFinset`.
  have hpoles_fin : ({x | f.orderAtPoint x < 0} : Set X).Finite := f.finite_poles
  rw [finsum_mem_eq_finite_toFinset_sum _ hpoles_fin]
  -- `localDeg f ∞ x = −order x` on each summand.
  simp only [localDeg_infty]
  -- Now: `∑ x ∈ poles.toFinset, −order x = polesCount f`.
  -- `polesCount f = ∑ x ∈ div.support with order < 0, −order x`.
  rw [polesCount]
  -- Both index sets agree as Finsets: `poles.toFinset = div.support.filter (order < 0)`.
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter,
    Finsupp.mem_support_iff, div_apply]
  constructor
  · intro hx; exact ⟨ne_of_lt hx, hx⟩
  · rintro ⟨_, hx⟩; exact hx

/-- **Special-fibre identity at `coe 0`:** the genuine local-degree sum over the
zero fibre `F⁻¹(coe 0)` equals `zerosCount f`.

`localDeg f (coe 0) x = orderAtPoint f x` (`localDeg_zero_eq_order`), and the
order function vanishes off `{x | order x ≠ 0}`.  A point of the fibre `F⁻¹(coe
0)` is a non-pole (it maps to `coe 0 ≠ ∞`, so `order ≥ 0`), so on the support
`{order ≠ 0}` membership in the fibre is equivalent to being a genuine zero
`{0 < order}` (forward: `order ≥ 0` and `order ≠ 0`; backward:
`zeros_subset_toRiemannSphere_preimage_zero`).  The finsum therefore collapses
onto the zeros, reindexing to `zerosCount f`.

Note this needs *no* fibre-finiteness hypothesis: the summand's support is
finite (`⊆ {order ≠ 0}`, finite on compact `X`), which is all `finsum` needs. -/
lemma fibreMult_zero_eq_zerosCount (f : MeromorphicFunction X) :
    fibreMult f ((0 : ℂ) : RiemannSphere) = zerosCount f := by
  classical
  rw [fibreMult]
  -- Rewrite the summand to `orderAtPoint`.
  have hsummand : ∀ x, localDeg f ((0 : ℂ) : RiemannSphere) x = f.orderAtPoint x :=
    fun x => localDeg_zero_eq_order f x
  simp_rw [hsummand]
  -- Replace the fibre by the genuine zero set, using support-restriction.
  -- `support orderAtPoint = {x | order x ≠ 0}`.
  have hrestrict :
      (∑ᶠ x ∈ f.toRiemannSphere ⁻¹' {((0 : ℂ) : RiemannSphere)}, f.orderAtPoint x)
        = ∑ᶠ x ∈ {x | 0 < f.orderAtPoint x}, f.orderAtPoint x := by
    apply finsum_mem_inter_support_eq'
    intro x hx
    -- `hx : x ∈ support orderAtPoint`, i.e. `order x ≠ 0`.
    rw [Function.mem_support] at hx
    constructor
    · -- `x ∈ F⁻¹(coe 0)` ⇒ non-pole ⇒ `order ≥ 0`; with `order ≠ 0` get `order > 0`.
      intro hxfib
      simp only [Set.mem_setOf_eq]
      by_contra hnpos
      have hle : f.orderAtPoint x < 0 := lt_of_le_of_ne (not_lt.mp hnpos) hx
      -- but then `x` is a pole, so `F x = ∞ ≠ coe 0`.
      have : f.toRiemannSphere x = OnePoint.infty := f.toRiemannSphere_of_pole hle
      rw [Set.mem_preimage, Set.mem_singleton_iff, this] at hxfib
      exact (OnePoint.infty_ne_coe _) hxfib
    · -- `0 < order x` ⇒ `x` is a genuine zero ⇒ `x ∈ F⁻¹(coe 0)`.
      intro hxpos
      simp only [Set.mem_setOf_eq] at hxpos
      exact f.zeros_subset_toRiemannSphere_preimage_zero hxpos
  rw [hrestrict]
  -- Now: `∑ᶠ x ∈ {0 < order}, order x = zerosCount f`.
  -- The zero set is finite (⊆ support of the locally-finite order).
  have hzeros_fin : ({x | 0 < f.orderAtPoint x} : Set X).Finite := by
    have hsupp : (Function.support f.orderAtPoint).Finite :=
      f.orderLocallyFinsupp.finiteSupport isCompact_univ
    refine hsupp.subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    exact ne_of_gt hx
  rw [finsum_mem_eq_finite_toFinset_sum _ hzeros_fin, zerosCount]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter,
    Finsupp.mem_support_iff, div_apply]
  constructor
  · intro hx; exact ⟨ne_of_gt hx, hx⟩
  · rintro ⟨_, hx⟩; exact hx

/-- **`N f` is the genuine fibre-multiplicity function everywhere.**

`N f` differs from `fibreMult f` only at the two special values `coe 0`, `∞`,
where it plugs in `zerosCount f`, `polesCount f` respectively; the special-fibre
identities (`fibreMult_zero_eq_zerosCount`, `fibreMult_infty_eq_polesCount`)
prove those plugs *equal* the genuine multiplicity sums there.  Hence `N f w =
fibreMult f w` for every `w`.

Consequence: any `MultiplicityPatchingData f w₀` whose `N_eq_fibreMult` field is
required only on its neighbourhood `W` is freed of *all* its special-value
content by this global identity. -/
lemma N_eq_fibreMult_everywhere (f : MeromorphicFunction X) (w : RiemannSphere) :
    N f w = fibreMult f w := by
  unfold N
  split_ifs with h_infty h_zero
  · rw [h_infty, fibreMult_infty_eq_polesCount]
  · rw [h_zero, fibreMult_zero_eq_zerosCount]
  · rfl

/-! ### Streamlined per-`w₀` constructor (the special-value field discharged)

The special-fibre identities let us drop the `N_eq_fibreMult` field entirely from
the per-`w₀` obligation: it is now `N_eq_fibreMult_everywhere`, true for *all*
`w` with no hypothesis.  So a `MultiplicityPatchingData f w₀` is assembled from
*purely geometric* data — the sheets, weights, per-sheet multiplicity
conservation, fibre finiteness over `W`, and no-escape — with the special-value
bookkeeping already banked.  This is the reusable reduction of the §17.9 wall to
its genuine geometric core. -/

/-- **Streamlined builder for `MultiplicityPatchingData`.**  Identical to the raw
structure *except* the `N_eq_fibreMult` field is supplied automatically by the
proven global identity `N f = fibreMult f`.  The caller provides only the
geometric conservation-of-number data (sheets, weights, per-sheet conservation,
finite fibres, no-escape). -/
def MultiplicityPatchingData.ofGeometricData (f : MeromorphicFunction X)
    (w₀ : RiemannSphere)
    (xs : Finset X)
    (xs_coe : (xs : Set X) = f.toRiemannSphere ⁻¹' {w₀})
    (U : X → Set X)
    (U_open : ∀ x ∈ xs, IsOpen (U x))
    (mem_U_self : ∀ x ∈ xs, x ∈ U x)
    (U_pairwiseDisjoint : ∀ x ∈ xs, ∀ x' ∈ xs, x ≠ x' → Disjoint (U x) (U x'))
    (m : X → ℤ)
    (W : Set RiemannSphere)
    (W_open : IsOpen W)
    (w₀_mem_W : w₀ ∈ W)
    (sheetMult_eq : ∀ x ∈ xs, ∀ w ∈ W,
      (∑ᶠ y ∈ U x ∩ f.toRiemannSphere ⁻¹' {w}, localDeg f w y) = m x)
    (fibre_finite : ∀ w ∈ W, (f.toRiemannSphere ⁻¹' {w}).Finite)
    (preimage_W_subset : f.toRiemannSphere ⁻¹' W ⊆ ⋃ x ∈ xs, U x) :
    MultiplicityPatchingData f w₀ where
  xs := xs
  xs_coe := xs_coe
  U := U
  U_open := U_open
  mem_U_self := mem_U_self
  U_pairwiseDisjoint := U_pairwiseDisjoint
  m := m
  W := W
  W_open := W_open
  w₀_mem_W := w₀_mem_W
  sheetMult_eq := sheetMult_eq
  fibre_finite := fibre_finite
  preimage_W_subset := preimage_W_subset
  N_eq_fibreMult := fun w _ => N_eq_fibreMult_everywhere f w

/-! ### The no-escape skeleton (the properness/compactness assembly, banked)

The genuine §17.9 geometric content is the *local* per-sheet conservation; the
*global* "no preimage escapes the finitely many sheets" is a soft
properness/compactness argument, identical to the one in
`HurwitzPatchingData.ofLocalSheets`.  We bank it here: given the (already
pairwise-disjoint) sheets `U x` with per-point value-neighbourhoods `Wsheet x` on
which conservation holds, the common neighbourhood

> `W := (f '' K)ᶜ ∩ ⋂ₓ Wsheet x`,   `K := (⋃ₓ U x)ᶜ`

is open, contains `w₀`, sits inside every `Wsheet x` (so conservation persists),
and enjoys no-escape: a preimage of `w ∈ W` cannot lie in `K` (else `w ∈ f '' K`),
so it lies in some sheet `U x`.  Fibre finiteness over `W` follows from
properness (every fibre is compact; the supplied per-`w₀` finiteness suffices for
the value reading but we additionally require finiteness over `W`).

This reduces the per-`w₀` construction to: pairwise-disjoint sheets, per-point
conservation, and finite fibres over a value-neighbourhood — the irreducible
local content. -/

/-- **No-escape skeleton for `MultiplicityPatchingData`.**

From pairwise-disjoint open sheets `U x` (one per fibre point `x ∈ xs`, where
`↑xs = F⁻¹{w₀}`), each carrying an open value-neighbourhood `Wsheet x ∋ w₀` on
which the per-sheet multiplicity conservation holds, together with an open
value-neighbourhood `Wfin ∋ w₀` over which every fibre is finite, this builds a
`MultiplicityPatchingData f w₀`.

The no-escape (`preimage_W_subset`) and the shrinking of the value-neighbourhood
to a common `W := (f '' K)ᶜ ∩ ⋂ Wsheet x ∩ Wfin` are discharged via the
proper-map compactness argument; the `N_eq_fibreMult` field is the global
identity `N = fibreMult`.  Conservation persists from `Wsheet x` to the smaller
`W` by monotonicity (the sheets `U x` are *not* shrunk, so no preimage is lost);
fibre finiteness persists from `Wfin`.  Supplying `Wfin` *separately* (rather than
deriving it as `⋂ Wsheet x`) keeps the empty-fibre case sound (`xs = ∅` makes
`⋂ Wsheet x = univ`, but `Wfin` can be a genuine finiteness neighbourhood). -/
def MultiplicityPatchingData.ofDisjointSheets (f : MeromorphicFunction X)
    (w₀ : RiemannSphere)
    (xs : Finset X)
    (xs_coe : (xs : Set X) = f.toRiemannSphere ⁻¹' {w₀})
    (U : X → Set X)
    (U_open : ∀ x ∈ xs, IsOpen (U x))
    (mem_U_self : ∀ x ∈ xs, x ∈ U x)
    (U_pairwiseDisjoint : ∀ x ∈ xs, ∀ x' ∈ xs, x ≠ x' → Disjoint (U x) (U x'))
    (m : X → ℤ)
    (Wsheet : X → Set RiemannSphere)
    (Wsheet_open : ∀ x ∈ xs, IsOpen (Wsheet x))
    (w₀_mem_Wsheet : ∀ x ∈ xs, w₀ ∈ Wsheet x)
    (sheetMult_eq : ∀ x ∈ xs, ∀ w ∈ Wsheet x,
      (∑ᶠ y ∈ U x ∩ f.toRiemannSphere ⁻¹' {w}, localDeg f w y) = m x)
    (Wfin : Set RiemannSphere) (Wfin_open : IsOpen Wfin) (w₀_mem_Wfin : w₀ ∈ Wfin)
    (fibre_finite_Wfin : ∀ w ∈ Wfin, (f.toRiemannSphere ⁻¹' {w}).Finite) :
    MultiplicityPatchingData f w₀ := by
  classical
  -- The finite union of sheets, via `attach` to handle dependent membership cleanly.
  set UnionU : Set X := ⋃ (p : {a // a ∈ xs}), U p.1 with hUnionU
  have UnionU_open : IsOpen UnionU := isOpen_iUnion (fun p => U_open p.1 p.2)
  have fibre_subset_UnionU : f.toRiemannSphere ⁻¹' {w₀} ⊆ UnionU := by
    rw [← xs_coe]
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_U_self x hx⟩
  -- `K := UnionUᶜ` is compact (closed in compact `X`); `F '' K` is closed and avoids `w₀`.
  set K : Set X := UnionUᶜ with hK
  have K_compact : IsCompact K := UnionU_open.isClosed_compl.isCompact
  have FK_closed : IsClosed (f.toRiemannSphere '' K) :=
    (K_compact.image f.continuous_toRiemannSphere).isClosed
  have w₀_notin_FK : w₀ ∉ f.toRiemannSphere '' K := by
    rintro ⟨z, hzK, hzfw⟩
    have hz_fib : z ∈ f.toRiemannSphere ⁻¹' {w₀} := by simpa using hzfw
    exact hzK (fibre_subset_UnionU hz_fib)
  -- The common intersection of value-neighbourhoods (finite, over `↑xs`).
  set InterW : Set RiemannSphere := ⋂ (p : {a // a ∈ xs}), Wsheet p.1 with hInterW
  have InterW_open : IsOpen InterW :=
    isOpen_iInter_of_finite (fun p => Wsheet_open p.1 p.2)
  have w₀_mem_InterW : w₀ ∈ InterW := by
    rw [mem_iInter]; intro p; exact w₀_mem_Wsheet p.1 p.2
  -- `W := (F '' K)ᶜ ∩ InterW ∩ Wfin`.
  set W : Set RiemannSphere := (f.toRiemannSphere '' K)ᶜ ∩ InterW ∩ Wfin with hWdef
  have W_open : IsOpen W := (FK_closed.isOpen_compl.inter InterW_open).inter Wfin_open
  have w₀_mem_W : w₀ ∈ W := ⟨⟨w₀_notin_FK, w₀_mem_InterW⟩, w₀_mem_Wfin⟩
  -- `W ⊆ Wsheet x` for each `x ∈ xs` (via the `InterW` factor).
  have W_subset_Wsheet : ∀ x ∈ xs, W ⊆ Wsheet x := by
    intro x hx w hw
    have : w ∈ InterW := hw.1.2
    exact mem_iInter.mp this ⟨x, hx⟩
  refine MultiplicityPatchingData.ofGeometricData f w₀ xs xs_coe U U_open mem_U_self
    U_pairwiseDisjoint m W W_open w₀_mem_W ?_ ?_ ?_
  · -- sheetMult_eq on `W`: persists from `Wsheet x ⊇ W`.
    intro x hx w hw
    exact sheetMult_eq x hx w (W_subset_Wsheet x hx hw)
  · -- fibre finiteness over `W ⊆ Wfin`.
    intro w hw
    exact fibre_finite_Wfin w hw.2
  · -- no escape: a preimage of `w ∈ W` is not in `K`, hence in `UnionU`, hence in some sheet.
    intro z hz
    have hzfW : f.toRiemannSphere z ∈ W := hz
    have hz_notin_K : z ∉ K := fun hzK => hzfW.1.1 ⟨z, hzK, rfl⟩
    have hz_unionU : z ∈ UnionU := by
      by_contra h; exact hz_notin_K h
    rw [hUnionU, mem_iUnion] at hz_unionU
    obtain ⟨p, hzp⟩ := hz_unionU
    exact mem_iUnion₂.mpr ⟨p.1, p.2, hzp⟩

/-! ### The isolated local content: `LocalMultiplicitySheets`

`ofDisjointSheets` reduces the per-`w₀` patching obligation to *purely local*
geometric data: pairwise-disjoint sheets around the (finite) fibre, each with a
value-neighbourhood on which the per-sheet multiplicity sum is constant, and
fibre-finiteness over the common value-neighbourhood.  We bundle exactly this
into a structure `LocalMultiplicitySheets f w₀`, the irreducible §17.9 content.

This is the genuine analytic wall — built per fibre point from the chart normal
form (`Planar.orderSum_eq_of_analyticOrder`), the chart-invariance of the order
(`MeromorphicFunction.orderAtPoint_chart_invariant`), and T2 separation of the
finite fibre.  It is a *true, non-vacuous* obligation: at a value off the range
of `F` the fibre is empty and the *empty* sheet datum satisfies every field
(`LocalMultiplicitySheets.ofEmptyFibre`), so the structure is satisfiable, never
a disguised `False`. -/

/-- **The irreducible local conservation data** at a value `w₀ : ℂℙ¹`: the
geometric inputs to `MultiplicityPatchingData.ofDisjointSheets`.  Bundles the
finite fibre enumeration, the pairwise-disjoint sheets, the per-sheet weights and
value-neighbourhoods, the per-sheet multiplicity conservation, and fibre
finiteness over the common value-neighbourhood. -/
structure LocalMultiplicitySheets (f : MeromorphicFunction X) (w₀ : RiemannSphere) where
  /-- Finite enumeration of the fibre `F⁻¹(w₀)`. -/
  xs : Finset X
  /-- `↑xs` is the fibre. -/
  xs_coe : (xs : Set X) = f.toRiemannSphere ⁻¹' {w₀}
  /-- A sheet around each fibre point. -/
  U : X → Set X
  /-- Each sheet is open. -/
  U_open : ∀ x ∈ xs, IsOpen (U x)
  /-- Each sheet contains its fibre point. -/
  mem_U_self : ∀ x ∈ xs, x ∈ U x
  /-- Sheets are pairwise disjoint. -/
  U_pairwiseDisjoint : ∀ x ∈ xs, ∀ x' ∈ xs, x ≠ x' → Disjoint (U x) (U x')
  /-- The per-sheet weight (local degree). -/
  m : X → ℤ
  /-- A per-sheet value-neighbourhood of `w₀`. -/
  Wsheet : X → Set RiemannSphere
  /-- Each value-neighbourhood is open. -/
  Wsheet_open : ∀ x ∈ xs, IsOpen (Wsheet x)
  /-- Each value-neighbourhood contains `w₀`. -/
  w₀_mem_Wsheet : ∀ x ∈ xs, w₀ ∈ Wsheet x
  /-- **Per-sheet multiplicity conservation** on the value-neighbourhood. -/
  sheetMult_eq : ∀ x ∈ xs, ∀ w ∈ Wsheet x,
    (∑ᶠ y ∈ U x ∩ f.toRiemannSphere ⁻¹' {w}, localDeg f w y) = m x
  /-- An open value-neighbourhood of `w₀` over which every fibre is finite. -/
  Wfin : Set RiemannSphere
  /-- `Wfin` is open. -/
  Wfin_open : IsOpen Wfin
  /-- `w₀ ∈ Wfin`. -/
  w₀_mem_Wfin : w₀ ∈ Wfin
  /-- Fibre finiteness over `Wfin`. -/
  fibre_finite_Wfin : ∀ w ∈ Wfin, (f.toRiemannSphere ⁻¹' {w}).Finite

/-- **From the local data to the patching datum.** -/
def LocalMultiplicitySheets.toPatchingData {f : MeromorphicFunction X}
    {w₀ : RiemannSphere} (s : LocalMultiplicitySheets f w₀) :
    MultiplicityPatchingData f w₀ :=
  MultiplicityPatchingData.ofDisjointSheets f w₀ s.xs s.xs_coe s.U s.U_open
    s.mem_U_self s.U_pairwiseDisjoint s.m s.Wsheet s.Wsheet_open s.w₀_mem_Wsheet
    s.sheetMult_eq s.Wfin s.Wfin_open s.w₀_mem_Wfin s.fibre_finite_Wfin

/-! ### Non-vacuity: the empty-fibre witness

At a value `w₀ ∉ range F`, the fibre is empty, so the *empty* local-sheet datum
(`xs = ∅`) satisfies every field on the whole-space neighbourhood `(range F)ᶜ`
(open, since `F` is proper hence closed-range).  This certifies
`LocalMultiplicitySheets` is *satisfiable* — a genuine, true obligation. -/

/-- **Empty-fibre witness.**  At `w₀ ∉ range F`, the empty local-sheet datum
satisfies `LocalMultiplicitySheets f w₀`: the fibre over `w₀` is empty, and on the
open neighbourhood `Wfin := (range F)ᶜ` every fibre is empty (hence finite).
Since `F` is proper its range is closed, so `(range F)ᶜ` is open and contains
`w₀`.  Hence the structure's obligations are satisfiable, not a disguised
`False`. -/
def LocalMultiplicitySheets.ofNotMemRange (f : MeromorphicFunction X)
    {w₀ : RiemannSphere} (h_notmem : w₀ ∉ Set.range f.toRiemannSphere) :
    LocalMultiplicitySheets f w₀ where
  xs := ∅
  xs_coe := by
    -- `↑(∅ : Finset X) = F⁻¹{w₀}`: both empty (`w₀ ∉ range F`).
    rw [Finset.coe_empty]
    symm
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact h_notmem ⟨y, hy⟩
  U := fun _ => ∅
  U_open := by intro x hx; simp at hx
  mem_U_self := by intro x hx; simp at hx
  U_pairwiseDisjoint := by intro x hx; simp at hx
  m := fun _ => 0
  Wsheet := fun _ => Set.univ
  Wsheet_open := by intro x hx; simp at hx
  w₀_mem_Wsheet := by intro x hx; simp at hx
  sheetMult_eq := by intro x hx; simp at hx
  Wfin := (Set.range f.toRiemannSphere)ᶜ
  Wfin_open := f.isProperMap_toRiemannSphere.isClosedMap.isClosed_range.isOpen_compl
  w₀_mem_Wfin := h_notmem
  fibre_finite_Wfin := by
    -- On `(range F)ᶜ` every fibre is empty (`w ∉ range F`), hence finite.
    intro w hw
    have : f.toRiemannSphere ⁻¹' {w} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact hw ⟨y, hy⟩
    rw [this]; exact Set.finite_empty

/-! ### The headline: `IsLocallyConstant (N f)` and `exists_properMapDegree`

A *pointwise* supply of the local conservation data `∀ w₀, LocalMultiplicitySheets
f w₀` yields, through `toPatchingData` and the proven structure ⇒ local-constancy
bridge `isLocallyConstant_N_of_pointwiseMultiplicityPatching`, the global local
constancy `IsLocallyConstant (N f)` — and thence, via the proven connectedness
globalization, the proper-map-degree existential `exists_properMapDegree`.

This is the exact wiring the parent (`DegDivResidue.exists_properMapDegree`)
invokes; the only remaining input is the *local* conservation supply (the
irreducible §17.9 content isolated in `LocalMultiplicitySheets`, banked here down
to its genuine per-sheet core, with the no-escape/disjointness skeleton, the
special-fibre identities, and the finiteness-shrinking all discharged
complete). -/

/-- **Local constancy of `N f` from a pointwise local-conservation supply.** -/
theorem isLocallyConstant_N_of_localSheets (f : MeromorphicFunction X)
    (h : ∀ w₀ : RiemannSphere, LocalMultiplicitySheets f w₀) :
    IsLocallyConstant (N f) :=
  isLocallyConstant_N_of_pointwiseMultiplicityPatching f
    (fun w₀ => (h w₀).toPatchingData)

/-- **`zerosCount = polesCount`** (the argument-principle equality) from a
pointwise local-conservation supply. -/
theorem zerosCount_eq_polesCount_of_localSheets (f : MeromorphicFunction X)
    (h : ∀ w₀ : RiemannSphere, LocalMultiplicitySheets f w₀) :
    zerosCount f = polesCount f :=
  zerosCount_eq_polesCount_of_pointwiseMultiplicityPatching f
    (fun w₀ => (h w₀).toPatchingData)

/-- **The proper-map-degree existential** (the exact shape of
`Jacobians.DegDivResidue.exists_properMapDegree`: a common `d : ℕ` with
`zerosCount f = d = polesCount f`) from a pointwise local-conservation supply.

Feeding this theorem `∀ w₀, LocalMultiplicitySheets f w₀` closes
`exists_properMapDegree`, hence `deg_div`, hence the Riemann–Roch keystone. -/
theorem exists_properMapDegree_of_localSheets (f : MeromorphicFunction X)
    (h : ∀ w₀ : RiemannSphere, LocalMultiplicitySheets f w₀) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) :=
  exists_properMapDegree_of_pointwiseMultiplicityPatching f
    (fun w₀ => (h w₀).toPatchingData)

end Jacobians.MultiplicityPatchingConstruct

end
