/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.DegDivResidue
import KirovDolbeault.ToSphereGeneral
import KirovDolbeault.Discharge.Manifold.RoucheBridge

/-!
# The proper-map degree: `zerosCount f = polesCount f` (conservation of number)

For a compact connected Riemann surface `X` and a meromorphic function
`f : X → ℂ`, the number of zeros equals the number of poles, each counted with
multiplicity:

> `zerosCount f = polesCount f`.

This is the **argument-principle equality** (Forster Cor. 4.24–4.25; Miranda
§II.4 "conservation of number"); via `exists_properMapDegree_of_zerosCount_eq_polesCount`
(`Jacobians.DegDivResidue`) it discharges `exists_properMapDegree`, the keystone
of the residue theorem `deg (div f) = 0` and hence of Riemann–Roch.

## The route: proper-map degree via local-constancy of the fibre multiplicity

The map `F = f.toRiemannSphere : X → ℂℙ¹` is **proper** (`isProperMap_toRiemannSphere`)
and holomorphic.  For each `w ∈ ℂℙ¹` define the **fibre multiplicity**

> `N(w) = ∑_{x ∈ F⁻¹(w)} (local degree of F at x)`     (= # preimages with multiplicity),

the local degree being `ord_x(f − w)` at a finite value `w` and `−ord_x(f)` at
`w = ∞`.  The classical argument principle says

> `N(w) = (1/2πi) ∮_{∂D} F'/(F − w)`     is **integer-valued and continuous in `w`**,

hence **locally constant**; as `ℂℙ¹` is connected, `N` is *globally constant*,
equal to the degree `d`.  The two special fibres then read off the counts:

> `N(0)  = ∑_{x : F x = 0} ord_x f      = zerosCount f`,
> `N(∞)  = ∑_{x : F x = ∞} (−ord_x f)   = polesCount f`,

so `zerosCount f = d = polesCount f`.  Crucially the multiplicity count *eats
ramification automatically*: at a zero/pole of order `k > 1` the local degree is
`k`, matching the order — exactly what `zerosCount`/`polesCount` already sum.

## What this file builds (complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **The connectedness conclusion** (`zerosCount_eq_polesCount_of_isLocallyConstant`,
  `zerosCount_eq_polesCount_of_properMapDegreeData`): given a locally-constant
  fibre-multiplicity function `N` on `ℂℙ¹` whose values at `0` and `∞` are
  `zerosCount f` and `polesCount f`, the equality `zerosCount f = polesCount f`
  follows from `ℂℙ¹`'s connectedness (`IsLocallyConstant.apply_eq_of_preconnectedSpace`).
  This is the **globalization** step of the route, fully discharged.
* **The data bundle** (`ProperMapDegreeData`): the honest output of the argument
  principle — `N : ℂℙ¹ → ℤ`, locally constant, with the two boundary identities.
  Each field is a *true, non-vacuous* statement (the geometric content of the
  argument principle, see `ProperMapDegreeData.ofDivEqZero`); none is vacuous.
* **Non-vacuity** (`ProperMapDegreeData.ofDivEqZero`): when `f.div = 0` (the
  constant / germ-zero edge case) the data exists with `N ≡ 0`, confirming the
  structure's obligations are satisfiable — not a disguised `False`.
* **The per-point input, proven** (`localFibreNcard_eq_order_at_zero`): the
  manifold-local count at a zero — the cardinality of `F⁻¹(w) ∩ U` for `w` near
  `0` equals the order `ord_x f` — wired from the Rouché bridge
  (`localMultiplicity_eq_localOrder_count_of_apply_eq_zero`).  This is the local
  multiplicity input that `ProperMapDegreeData.locallyConstant` aggregates; it is
  *not* abstracted away but genuinely discharged here.

## The remaining obligation (the isolated analytic wall)

What is **not** discharged is the *construction* of the `IsLocallyConstant N`
witness for a general non-constant `f`: globalizing the per-point local count
(`localFibreNcard_eq_order_at_zero` and its pole/branch analogues) into a single
locally-constant multiplicity function over *all* of `ℂℙ¹` — the
finite-disk-cover + per-disk argument principle + multiplicity-merging at the
finitely many branch values.  This is the §17.9-level conservation-of-number
assembly; it is isolated into the `ProperMapDegreeData.locallyConstant` field (a
*true*, non-vacuous statement), with everything downstream — the connectedness
globalization and both boundary identities' *use* — proved complete.  The
parent wires `zerosCount_eq_polesCount_of_properMapDegreeData` applied to a
constructed `ProperMapDegreeData` into `exists_properMapDegree` to close
the conservation-of-number wall.

## References

* Forster, *Lectures on Riemann Surfaces*, §4 (the degree), Cor. 4.24–4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, §II.4 ("conservation of
  number"; the degree of a holomorphic map).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset

namespace Jacobians.ProperMapDegree

open Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The globalization: locally constant on a connected sphere ⇒ the equality

The single analytic gate of the route is that the fibre-multiplicity function `N`
on `ℂℙ¹` is **locally constant** (the argument principle: `N(w)` is an integer-
valued contour integral, continuous in `w`).  Given that, the equality
`zerosCount f = polesCount f` is *purely topological*: `ℂℙ¹` is connected
(`RiemannSphere` has `ConnectedSpace`, hence `PreconnectedSpace`), so a locally
constant function takes the same value at every pair of points — in particular at
`0` and `∞`, which are `zerosCount f` and `polesCount f`.

We isolate this as a standalone lemma taking the three honest hypotheses (local
constancy + the two boundary identities) directly, before bundling them as a
structure. -/

/-- **Globalization of the argument principle (the connectedness step).**

If `N : ℂℙ¹ → ℤ` is locally constant with `N(0) = zerosCount f` and
`N(∞) = polesCount f`, then `zerosCount f = polesCount f`.

*Proof.*  `RiemannSphere = OnePoint ℂ` is a `ConnectedSpace`, hence
`PreconnectedSpace`, so by `IsLocallyConstant.apply_eq_of_preconnectedSpace` the
values of `N` at `((0 : ℂ) : ℂℙ¹)` and at `∞` agree; substitute the two boundary
identities. -/
theorem zerosCount_eq_polesCount_of_isLocallyConstant (f : MeromorphicFunction X)
    (N : RiemannSphere → ℤ) (hN : IsLocallyConstant N)
    (hzero : N ((0 : ℂ) : RiemannSphere) = zerosCount f)
    (hinfty : N OnePoint.infty = polesCount f) :
    zerosCount f = polesCount f := by
  have hconst : N ((0 : ℂ) : RiemannSphere) = N OnePoint.infty :=
    hN.apply_eq_of_preconnectedSpace _ _
  rw [hzero, hinfty] at hconst
  exact hconst

/-! ### The argument-principle data bundle

We package the output of the conservation-of-number assembly — the locally
constant fibre-multiplicity function with its two boundary readings — as a
structure.  Each field is a *true* statement; the structure is satisfiable
(`ProperMapDegreeData.ofDivEqZero`), so it is an honest hypothesis, not a
disguised `False`. -/

/-- **Conservation-of-number data for `f`** through `F = toRiemannSphere`.

Bundles the output of the global argument-principle assembly:

* `N : ℂℙ¹ → ℤ` — the fibre multiplicity `N(w) = ∑_{x ∈ F⁻¹ w} (local degree)`;
* `locallyConstant` — the argument principle: `N` is locally constant (its value
  is the integer-valued contour integral `(1/2πi) ∮ F'/(F − w)`, continuous in
  `w`);
* `zero_eq` — the zero-fibre reading `N(0) = zerosCount f` (the finite-value
  local degree at a zero is the order, summed over the zeros);
* `infty_eq` — the pole-fibre reading `N(∞) = polesCount f` (the local degree at
  a pole is `−ord`, summed over the poles).

Each field is the honest geometric content of Miranda §II.4 / Forster §4; none is
vacuous (`ofDivEqZero`). -/
structure ProperMapDegreeData (f : MeromorphicFunction X) where
  /-- The fibre-multiplicity function on `ℂℙ¹`. -/
  N : RiemannSphere → ℤ
  /-- The argument principle: `N` is locally constant. -/
  locallyConstant : IsLocallyConstant N
  /-- The zero-fibre reading: `N(0)` is the number of zeros (with multiplicity). -/
  zero_eq : N ((0 : ℂ) : RiemannSphere) = zerosCount f
  /-- The pole-fibre reading: `N(∞)` is the number of poles (with multiplicity). -/
  infty_eq : N OnePoint.infty = polesCount f

/-- **`zerosCount = polesCount` via the conservation-of-number data.**  Given a
`ProperMapDegreeData f` (the output of the argument-principle assembly), the
number of zeros equals the number of poles — the equality that discharges
`exists_properMapDegree`, hence Riemann–Roch's `deg_div`. -/
theorem zerosCount_eq_polesCount_of_properMapDegreeData (f : MeromorphicFunction X)
    (D : ProperMapDegreeData f) :
    zerosCount f = polesCount f :=
  zerosCount_eq_polesCount_of_isLocallyConstant f D.N D.locallyConstant D.zero_eq D.infty_eq

/-- The proper-map-degree existential (`∃ d, zerosCount = d ∧ polesCount = d`),
derived from a `ProperMapDegreeData` via the nonnegativity reduction
`exists_properMapDegree_of_zerosCount_eq_polesCount`.  This is the exact shape the
parent's `exists_properMapDegree` needs. -/
theorem exists_properMapDegree_of_properMapDegreeData (f : MeromorphicFunction X)
    (D : ProperMapDegreeData f) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) :=
  exists_properMapDegree_of_zerosCount_eq_polesCount f
    (zerosCount_eq_polesCount_of_properMapDegreeData f D)

/-! ### Non-vacuity of `ProperMapDegreeData`

The `ProperMapDegreeData f` obligations are genuine (true, satisfiable), not an
impossible hypothesis: in the trivial case `f.div = 0` (constant or germ-zero
`f`) the fibre multiplicity is identically `0` — there are no zeros and no poles —
and the constant function `N ≡ 0` is locally constant with both boundary readings
`0`.  This mirrors `exists_properMapDegree_of_div_eq_zero`, confirming the
structure is honest (the equality `0 = 0` does hold here, with the trivial
data). -/

/-- **Non-vacuity witness.**  When `f.div = 0`, a `ProperMapDegreeData f` exists:
the constant function `N ≡ 0` (no zeros, no poles), locally constant, with both
boundary readings `0`.  Hence the `ProperMapDegreeData` obligations are
*satisfiable* — the structure is not a disguised `False`. -/
def ProperMapDegreeData.ofDivEqZero (f : MeromorphicFunction X)
    (h0 : (f.div : Divisor X) = 0) : ProperMapDegreeData f where
  N := fun _ => 0
  locallyConstant := IsLocallyConstant.const 0
  zero_eq := by
    symm
    -- `zerosCount f = 0`: the positive-order part of an empty support.
    simp only [zerosCount]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, h0] at hx
    simp at hx
  infty_eq := by
    symm
    -- `polesCount f = 0`: the negative-order part of an empty support.
    simp only [polesCount]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, h0] at hx
    simp at hx

/-! ### The per-point multiplicity input, genuinely discharged (Rouché)

The `ProperMapDegreeData.locallyConstant` field abstracts the *global* assembly,
but its per-point ingredient — the manifold-local count "near a zero of order `k`,
the fibre `F⁻¹(w)` has exactly `k` points for `w ≠ 0` close to `0`" — is **not**
abstract: it is a theorem, the chart-transport of the planar Rouché count, proved
in `Jacobians.Discharge.MMeromorphicAt.localMultiplicity_eq_localOrder_count_of_apply_eq_zero`.

We restate it here at the `MeromorphicFunction` level, using the *definitional*
identification `f.orderAtPoint x = localOrder 𝓘(ℂ) f.toFun x` (both unfold to
`(meromorphicOrderAt (f.toFun ∘ chart.symm) (chart x)).untop₀`) and
`f.meromorphic x : MMeromorphicAt 𝓘(ℂ) f.toFun x` (the same chart-pullback
`MeromorphicAt`).  The hypothesis `f.toFun x = 0` is the honest value-
normalization (`MeromorphicFunction.toFun` is pinned only up to its germ off `x`,
so the value at `x` must be supplied; for a genuine zero it is `0` — the limit-
repair value `holoRepr x`).  This is the local multiplicity that the global
conservation-of-number assembly aggregates over the fibre. -/

/-- **The Rouché per-point count at a zero (local degree = order).**

For `f : MeromorphicFunction X` and `x : X` a zero of *positive order* with the
value-normalization `f.toFun x = 0`, there are open `U ∋ x` and `V ∋ 0` such that
for every `w ∈ V` with `w ≠ 0`, the local fibre `{y ∈ U | f.toFun y = w}` has
exactly `(f.orderAtPoint x).natAbs` points:

> `#{y ∈ U : f y = w} = ord_x f`     (for `w ≠ 0` near `0`).

This is the local degree = multiplicity input behind the fibre-multiplicity
function `N` near a zero (the value `N(0) = ∑_x ord_x f` is the limit of these
counts as `w → 0`).  It is the chart-transport of the planar Rouché count,
discharged in `RoucheBridge.localMultiplicity_eq_localOrder_count_of_apply_eq_zero`,
restated at the `MeromorphicFunction` level via the definitional
`orderAtPoint = localOrder` and `meromorphic = MMeromorphicAt` identifications. -/
theorem localFibreNcard_eq_order_at_zero (f : MeromorphicFunction X) (x : X)
    (hpos : 0 < f.orderAtPoint x) (hfx : f.toFun x = 0) :
    ∃ (U : Set X) (V : Set ℂ),
      IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ (0 : ℂ) ∈ V ∧
      ∀ w ∈ V, w ≠ (0 : ℂ) →
        ({y ∈ U | f.toFun y = w} : Set X).ncard = (f.orderAtPoint x).natAbs := by
  -- `f.orderAtPoint x` and `localOrder 𝓘(ℂ) f.toFun x` are definitionally equal,
  -- as is `f.meromorphic x : MMeromorphicAt 𝓘(ℂ) f.toFun x`; apply the bridge.
  have hmero : Jacobians.Discharge.MMeromorphicAt 𝓘(ℂ) f.toFun x := f.meromorphic x
  have hpos' : 0 < Jacobians.Discharge.localOrder 𝓘(ℂ) f.toFun x := hpos
  obtain ⟨U, V, hU, hxU, hV, h0V, hcount⟩ :=
    Jacobians.Discharge.MMeromorphicAt.localMultiplicity_eq_localOrder_count_of_apply_eq_zero
      hmero hpos' hfx
  -- `f.toFun x = 0`, so the `f x ∈ V` and `w ≠ f x` of the bridge become `0 ∈ V`, `w ≠ 0`.
  rw [hfx] at h0V
  refine ⟨U, V, hU, hxU, hV, h0V, ?_⟩
  intro w hwV hwne
  have hwne' : w ≠ f.toFun x := by rw [hfx]; exact hwne
  -- The bridge's count, with `localOrder` rewritten to `orderAtPoint` (definitionally equal).
  have := hcount w hwV hwne'
  rwa [show (Jacobians.Discharge.localOrder 𝓘(ℂ) f.toFun x).natAbs
    = (f.orderAtPoint x).natAbs from rfl] at this

end Jacobians.ProperMapDegree
