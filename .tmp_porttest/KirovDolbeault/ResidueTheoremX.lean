/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.MeromorphicTrace
import KirovDolbeault.ToSphereGeneral
import KirovDolbeault.DegDivResidue

/-!
# The residue theorem on a compact Riemann surface — the global assembly (`deg_div`)

For a compact connected Riemann surface `X` and a non-constant meromorphic function `f`, the
divisor `div f = ∑ₓ ord_x(f)·x` has degree `0`:

> `∑_{x ∈ X} ord_x(f) = 0`, equivalently `zerosCount f = polesCount f`.

This is Miranda §VIII.3 / Forster §17, the `df/f` (logarithmic-derivative) case of the residue
theorem, assembled from the one-variable pieces in `Jacobians.MeromorphicTrace` (the simple-pole
trace combine), `Jacobians.TraceResidue` (the `ℂℙ¹` residue theorem), and the cover
`F = toRiemannSphere` in `Jacobians.ToSphereGeneral`.

The route is

```
∑_{x∈X} ord_x(f)  =  ∑_{x∈X} Res_x(df/f)                         (chart bridge, step 1)
                  =  ∑_{y∈ℂℙ¹} ∑_{x∈F⁻¹y} Res_x(df/f)            (regroup by fibre, step 4)
                  =  ∑_{y} Res_y(Tr_F(df/f))                       (Lemma 3.2, simple poles)
                  =  0                                             (ℂℙ¹ residue theorem).
```

Because `df/f` has only **simple** poles (residue = the order), the residue change-of-variables
across each unramified sheet is unconditional (`resAt_simplePole_pushforward`), so no general
contour-substitution atom is needed.

## What this file builds (complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **Step 1 — the chart bridge** (`resLogDeriv`, `resLogDeriv_eq_order`): the intrinsic residue of
  `df/f` at `x`, read in any chart, equals `ord_x(f)`.  The per-point input of the route; a corollary
  of `resAt_logDeriv_eq_order`.

* **Step 4 — the fibrewise regrouping** (`orderSum_eq_fiberwise`, `orderSum_eq_infty_add_finite`):
  the total order `∑_{x∈supp} ord_x f` equals `∑_y ∑_{x∈F⁻¹y} ord_x f`, split into the `∞`-fibre
  (poles) and the finite-value fibres.  Pure `Finset` combinatorics.
* **Lemma 3.2 → orders** (`resAt_traceCoeff_eq_fibre_orderSum`): wires step 1 into Miranda's Lemma
  3.2 — a fibre carrying the `df/f` simple poles has trace residue = the fibre order sum.
* **The reduction** (`LogDerivTrace`, `orderSum_eq_zero_of_logDerivTrace`,
  `degDiv_eq_zero_of_logDerivTrace`, `zerosCount_eq_polesCount_of_logDerivTrace`): given the honest
  trace-representation structure `LogDerivTrace f` (the §VIII.3 assembly output), the residue theorem
  `∑_{x∈X} ord_x f = 0`, hence `zerosCount f = polesCount f`, follows from the simple-pole trace
  combine (`finiteResidueSum_trace_eq_zero_of_simplePole_fibres`) + the regrouping.
* **Non-vacuity** (`logDerivTrace_of_div_eq_zero`): a `LogDerivTrace f` exists when `f.div = 0`
  (the empty `LaurentForm`), confirming the structure's obligations are *true* and satisfiable — not
  a disguised `False`.

## The remaining obligation (the isolated analytic wall)

What is **not** discharged is the *construction* of a `LogDerivTrace f` for a general non-constant
`f`: the rational `LaurentForm L` representing `Tr_F(df/f)` (steps 2-3 — the cover's local
holomorphic sections, the trace's finiteness/rationality, partial fractions), Lemma 3.2's manifold
bookkeeping `hL32`, and the two aggregate fibre-residue↔order identifications `infty_eq`/`finite_eq`.
This is the §17.9-level trace assembly; it is isolated into the `LogDerivTrace` structure (whose
fields are each *true, non-vacuous* statements), with everything downstream fully proved.  The
parent wires `zerosCount_eq_polesCount_of_logDerivTrace` applied to a constructed `LogDerivTrace`
into `exists_properMapDegree` to close the conservation-of-number wall.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; partial
  fractions / residue theorem on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces*, §17 (the residue functional); Cor. 4.25.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.ResidueTheoremX

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step 1 — the chart bridge `Res_x(df/f) = ord_x(f)`

A meromorphic `1`-form on `X` is, in a chart `φ = chartAt x`, `(coeff)·dz` with the coefficient
meromorphic; its residue at `x` is `resAt (coeff) (φ x)`.  For `α = df/f` the coefficient is the
logarithmic derivative `logDeriv (f.toFun ∘ φ.symm)` of the chart pullback, and Miranda's local
argument principle (`resAt_logDeriv_eq_order`) gives its residue `= ord_x(f)` whenever the chart
pullback has finite order `n` at `φ x` (i.e. `f` is not identically `0` near `x`). -/

/-- The **intrinsic residue of the logarithmic differential** `df/f` at `x`, read in the chart
`φ = chartAt x`: `Res_x(df/f) := resAt (logDeriv (f.toFun ∘ φ.symm)) (φ x)`. -/
def resLogDeriv (f : MeromorphicFunction X) (x : X) : ℂ :=
  resAt (logDeriv (f.toFun ∘ (chartAt (H := ℂ) x).symm)) ((chartAt (H := ℂ) x) x)

/-- **The chart bridge (step 1), order form.**  If the chart pullback `f.toFun ∘ φ.symm`
(`φ = chartAt x`) has finite order `n` at `φ x` — i.e. `meromorphicOrderAt … = (n : ℤ)`, which
holds precisely when `f` is not identically `0` near `x` — then the residue of `df/f` at `x` is
`n`:

> `Res_x(df/f) = n`.

A direct corollary of `resAt_logDeriv_eq_order` (the one-variable local argument principle). -/
theorem resLogDeriv_eq_of_order (f : MeromorphicFunction X) (x : X) {n : ℤ}
    (hord : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
      = (n : ℤ)) :
    resLogDeriv f x = (n : ℂ) :=
  resAt_logDeriv_eq_order (f.meromorphic x) hord

/-- **The chart bridge (step 1).**  When the chart pullback of `f` is not identically `0` near
`φ x` (equivalently `meromorphicOrderAt … ≠ ⊤`), the intrinsic residue of `df/f` at `x` equals the
order of `f` there:

> `Res_x(df/f) = ord_x(f)`.

This is the per-point input of the residue-theorem route.  The hypothesis `hne` rules out the
degenerate `f ≡ 0` germ (where `orderAtPoint` is the junk value `0` and `df/f` is undefined); it
holds at every point for a non-constant `f`. -/
theorem resLogDeriv_eq_order (f : MeromorphicFunction X) (x : X)
    (hne : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) ≠ ⊤) :
    resLogDeriv f x = (f.orderAtPoint x : ℂ) := by
  -- The order is some finite `n`; `orderAtPoint = n.untop₀ = n`.
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  have hord : meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
      = (n : ℤ) := hn.symm
  have hoap : f.orderAtPoint x = n := by
    show (meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)).untop₀
      = n
    rw [hord]; rfl
  rw [resLogDeriv_eq_of_order f x hord, hoap]

/-! ### Step 4 — the fibrewise regrouping `∑_{x∈X} = ∑_y ∑_{F⁻¹y}`

The total order sum over the (finite) divisor support partitions, fibrewise, along the cover
`F = toRiemannSphere`: grouping the support points by their image under `F` and summing the order
within each fibre recovers the total.  This is pure `Finset` combinatorics
(`Finset.sum_fiberwise_of_maps_to`) and is independent of the analytic fibre packaging — the bridge
that turns `∑_{x∈X} Res_x` into a sum over `ℂℙ¹` of fibre sums. -/

/-- **The fibrewise regrouping of the order sum (step 4).**  Partition the divisor support by the
fibres of `F = f.toRiemannSphere`: the total order is the sum, over the image points `y` of the
support, of the per-fibre order sums.

> `∑_{x ∈ supp} ord_x f  =  ∑_{y ∈ F''supp} ∑_{x ∈ supp, F x = y} ord_x f`.

Pure combinatorics (`Finset.sum_fiberwise_of_maps_to`). -/
theorem orderSum_eq_fiberwise (f : MeromorphicFunction X) :
    ∑ x ∈ (f.div : Divisor X).support, f.orderAtPoint x
      = ∑ y ∈ (f.div : Divisor X).support.image f.toRiemannSphere,
          ∑ x ∈ (f.div : Divisor X).support with f.toRiemannSphere x = y, f.orderAtPoint x :=
  (Finset.sum_fiberwise_of_maps_to (fun _ hx => Finset.mem_image_of_mem _ hx) _).symm

/-- The fibrewise regrouping, split into the finite-value (`coe`) fibres and the `∞`-fibre.  The
support image under `F` decomposes into `∞` (the poles, all in the support) and the finite values;
within the support, the `∞`-fibre is exactly the poles and the `coe`-fibres are the zeros.  We keep
the decomposition at the level of the sphere image to feed it the trace combine. -/
theorem orderSum_eq_infty_add_finite (f : MeromorphicFunction X) :
    ∑ x ∈ (f.div : Divisor X).support, f.orderAtPoint x
      = (∑ x ∈ (f.div : Divisor X).support with f.toRiemannSphere x = OnePoint.infty,
            f.orderAtPoint x)
        + ∑ y ∈ ((f.div : Divisor X).support.image f.toRiemannSphere).erase OnePoint.infty,
            ∑ x ∈ (f.div : Divisor X).support with f.toRiemannSphere x = y, f.orderAtPoint x := by
  classical
  rw [orderSum_eq_fiberwise]
  by_cases hmem : OnePoint.infty ∈ (f.div : Divisor X).support.image f.toRiemannSphere
  · rw [← Finset.add_sum_erase _ _ hmem]
  · -- No pole in the support image: the `∞`-fibre sum is empty (`= 0`), erase is a no-op.
    rw [Finset.erase_eq_of_notMem hmem]
    have hempty : ((f.div : Divisor X).support.filter
        (fun x => f.toRiemannSphere x = OnePoint.infty)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hcontra
      exact hmem (hcontra ▸ Finset.mem_image_of_mem _ hx)
    rw [hempty, Finset.sum_empty, zero_add]

/-! ### The per-fibre Lemma 3.2 → orders bridge (step 1 ∘ Lemma 3.2)

The lemma that wires the chart bridge (step 1) into Miranda's Lemma 3.2 for the
`df/f` route: if a fibre `T : FibreTrace` carries the simple poles of `df/f` — each sheet `i`'s
coefficient being `cs i·(w − pre i)⁻¹` (`hsp`) with the simple-pole coefficient `cs i` equal to the
**order** of the corresponding preimage point `xs i` (`hcs`, which is `Res_{pre i}(df/f) = ord_{xs i}`
by step 1) — then the residue of the trace `Tr_F(df/f)` at the base equals the **fibre order sum**:

> `Res_b (Tr_F(df/f)) = ∑_{sheets i} ord_{xs i} f`.

This is Lemma 3.2 (`resAt_traceCoeff_of_simplePole`, residue = `∑ cs i`) composed with the chart
bridge (`cs i = ord_{xs i}`).  Any constructor of `LogDerivTrace` produces exactly this per fibre. -/
theorem resAt_traceCoeff_eq_fibre_orderSum (f : MeromorphicFunction X) (T : FibreTrace)
    (cs : T.ι → ℂ) (hsp : ∀ i, T.coeff i = fun w => cs i * (w - T.pre i)⁻¹)
    (xs : T.ι → X) (hcs : ∀ i, cs i = (f.orderAtPoint (xs i) : ℂ)) :
    resAt T.traceCoeff T.b = ((∑ i, f.orderAtPoint (xs i) : ℤ) : ℂ) := by
  rw [T.resAt_traceCoeff_of_simplePole cs hsp]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hsp i, resAt_const_mul_sub_inv, hcs i]

/-! ### Steps 2-3-5 — the trace representation and the reduction to the residue theorem

The remaining content is the **global manifold assembly** of the meromorphic trace `Tr_F(df/f)`
through the cover `F = toRiemannSphere`: packaging the (finite, off-branch) fibres as `FibreTrace`s
with simple-pole coefficients, exhibiting the rational trace as a `LaurentForm L` on `ℂℙ¹`, and
identifying — via Lemma 3.2 (`FibreTrace.resAt_traceCoeff_of_simplePole`) and the chart bridge
(`resLogDeriv_eq_order`) — each fibre's residue with the fibre's **order sum** `∑_{x∈F⁻¹y} ord_x f`.

We package this output as the structure `LogDerivTrace f` below; each field is a *true* statement
(it is exactly what the §VIII.3 trace assembly produces) and **not** vacuous.  Given a
`LogDerivTrace f`, the residue theorem `∑_{x∈X} ord_x f = 0` (hence `zerosCount = polesCount`)
follows from the simple-pole trace combine
(`finiteResidueSum_trace_eq_zero_of_simplePole_fibres`) and the fibrewise regrouping
(`orderSum_eq_infty_add_finite`), as proved in `degDiv_eq_zero_of_logDerivTrace` /
`zerosCount_eq_polesCount_of_logDerivTrace`.

This isolates the *entire* remaining analytic wall (the trace's finiteness/rationality + Lemma 3.2's
manifold bookkeeping `hL32` + the per-fibre order↔residue identifications) into the two geometric
identifications `infty_eq` and `finite_eq`, with everything downstream proved. -/

/-- **The logarithmic-derivative trace representation** of `f` through `F = toRiemannSphere`.

This bundles the output of the global manifold assembly of the meromorphic trace `Tr_F(df/f)` on
`ℂℙ¹` for the `df/f` route to the residue theorem:

* a `LaurentForm L` (partial-fraction `1`-form on `ℂℙ¹`) representing `Tr_F(df/f)`;
* a fibre datum `fibre p : FibreTrace` for each finite center `p`, with simple-pole coefficients
  `cs p` (`hsp`) — the `df/f` form, whose poles are all simple with residue the integer order;
* `hL32`: each center's fibre-residue sum equals `L`'s residue there (the manifold bookkeeping that
  `L` *is* the trace — Lemma 3.2 at the finite centers);
* `infty_eq`: the residue at infinity of the trace equals the **pole-fibre order sum**
  `∑_{x : F x = ∞} ord_x f` (Lemma 3.2 at `∞`, via the chart bridge `Res_x(df/f) = ord_x f`);
* `finite_eq`: the total over the finite centers of the per-fibre trace residue equals the
  **finite-fibre order sum** `∑_{y ≠ ∞} ∑_{x : F x = y} ord_x f` (Lemma 3.2 at the finite centers,
  via the chart bridge).

Each `*_eq` field is the honest geometric content of Miranda §VIII.3 (the trace residue = fibre sum
of residues = fibre sum of orders); none is vacuous. -/
structure LogDerivTrace (f : MeromorphicFunction X) where
  /-- The partial-fraction `1`-form on `ℂℙ¹` representing `Tr_F(df/f)`. -/
  L : LaurentForm
  /-- The fibre datum over each finite center. -/
  fibre : ℂ → FibreTrace
  /-- The simple-pole coefficients of the `df/f` form on each sheet. -/
  cs : (p : ℂ) → (fibre p).ι → ℂ
  /-- Each sheet's coefficient is a simple pole (`df/f` has only simple poles). -/
  hsp : ∀ p, ∀ i, (fibre p).coeff i = fun w => cs p i * (w - (fibre p).pre i)⁻¹
  /-- Lemma 3.2 at each finite center: the fibre-residue sum equals `L`'s residue. -/
  hL32 : ∀ p ∈ (Finset.univ.image L.a),
    (∑ i, resAt ((fibre p).coeff i) ((fibre p).pre i)) = resAt L.R p
  /-- The `∞`-residue of the trace is the pole-fibre order sum (Lemma 3.2 at `∞` + chart bridge). -/
  infty_eq : resAtInfty L.R L.ρ
    = ((∑ x ∈ (f.div : Divisor X).support with f.toRiemannSphere x = OnePoint.infty,
        f.orderAtPoint x : ℤ) : ℂ)
  /-- The finite-center trace-residue total is the finite-fibre order sum (Lemma 3.2 + chart bridge). -/
  finite_eq : (∑ p ∈ Finset.univ.image L.a, resAt (fibre p).traceCoeff (fibre p).b)
    = ((∑ y ∈ ((f.div : Divisor X).support.image f.toRiemannSphere).erase OnePoint.infty,
        ∑ x ∈ (f.div : Divisor X).support with f.toRiemannSphere x = y,
          f.orderAtPoint x : ℤ) : ℂ)

/-- **The residue theorem via the trace representation.**  Given a `LogDerivTrace f` (the output of
the §VIII.3 trace assembly), the total order of `f` over `X` vanishes:

> `∑_{x ∈ supp} ord_x f = 0`.

*Proof.*  The simple-pole trace combine
(`finiteResidueSum_trace_eq_zero_of_simplePole_fibres`) gives
`(∑_{centers} Res_b (Tr_F)) + Res_∞ (Tr_F) = 0`.  By `finite_eq` and `infty_eq` (cast to `ℂ`) the
two summands are the finite-fibre and `∞`-fibre order sums; by `orderSum_eq_infty_add_finite` their
integer sum is the total order, so its cast is `0`, whence (injectivity of `ℤ ↪ ℂ`) the integer sum
is `0`. -/
theorem orderSum_eq_zero_of_logDerivTrace (f : MeromorphicFunction X) (T : LogDerivTrace f) :
    ∑ x ∈ (f.div : Divisor X).support, f.orderAtPoint x = 0 := by
  -- The combine: the center-residue total plus the residue at infinity vanish.
  have hcombine := finiteResidueSum_trace_eq_zero_of_simplePole_fibres T.L T.fibre T.cs T.hsp T.hL32
  -- Rewrite both summands as casts of the fibre order sums.
  rw [T.finite_eq, T.infty_eq] at hcombine
  -- So the cast of the total integer order sum is `0`.
  have hcast : (((∑ y ∈ ((f.div : Divisor X).support.image f.toRiemannSphere).erase OnePoint.infty,
        ∑ x ∈ (f.div : Divisor X).support with f.toRiemannSphere x = y, f.orderAtPoint x)
      + (∑ x ∈ (f.div : Divisor X).support with f.toRiemannSphere x = OnePoint.infty,
        f.orderAtPoint x) : ℤ) : ℂ) = 0 := by
    rw [Int.cast_add]; exact hcombine
  rw [← Int.cast_zero] at hcast
  have hint := Int.cast_injective hcast
  -- The integer sum is the total order by the fibrewise regrouping.
  rw [orderSum_eq_infty_add_finite, add_comm]
  exact hint

/-- **The residue theorem (`deg_div`) via the trace representation.**  Given a `LogDerivTrace f`,
the principal divisor `div f` has degree `0`. -/
theorem degDiv_eq_zero_of_logDerivTrace (f : MeromorphicFunction X) (T : LogDerivTrace f) :
    Divisor.deg X f.div = 0 := by
  rw [deg_div_eq_support_sum]
  exact orderSum_eq_zero_of_logDerivTrace f T

/-- **`zerosCount = polesCount` via the trace representation.**  Given a `LogDerivTrace f`, the
number of zeros equals the number of poles (each with multiplicity) — the argument-principle
equality that discharges `exists_properMapDegree`, hence Riemann–Roch's `deg_div`. -/
theorem zerosCount_eq_polesCount_of_logDerivTrace (f : MeromorphicFunction X)
    (T : LogDerivTrace f) :
    zerosCount f = polesCount f := by
  have h := degDiv_eq_zero_of_logDerivTrace f T
  rw [deg_div_eq_zeros_sub_poles] at h
  linarith [h]

/-! ### Non-vacuity of `LogDerivTrace`

The `LogDerivTrace f` obligations are genuine (true, satisfiable), not an impossible hypothesis: in
the trivial case `f.div = 0` (constant or germ-zero `f`) we exhibit a `LogDerivTrace f` explicitly
— the empty `LaurentForm` (no poles, trace `≡ 0`), whose residue data and both order sums vanish.
This mirrors `exists_properMapDegree_of_div_eq_zero`, confirming the isolated structure is honest
(the residue theorem does hold in this case, with the trivial trace). -/

/-- The empty `LaurentForm` (no monomials): coefficient `R ≡ 0`, residue at infinity `0`, no
centers.  The trace of the zero `1`-form. -/
def emptyLaurentForm : LaurentForm where
  ι := Empty
  fintype_ι := inferInstance
  decEq_ι := inferInstance
  c := Empty.elim
  a := Empty.elim
  n := Empty.elim
  ρ := 0
  centers_mem := fun i => i.elim

/-- The empty `FibreTrace` (no sheets): trace coefficient `≡ 0`.  The fibre datum over a center with
no preimages. -/
def emptyFibreTrace : FibreTrace where
  ι := Empty
  fintype_ι := inferInstance
  b := 0
  sheet := fun i => i.elim
  pre := Empty.elim
  sheet_analytic := fun i => i.elim
  sheet_deriv_ne := fun i => i.elim
  sheet_base := fun i => i.elim
  coeff := fun i => i.elim
  coeff_mero := fun i => i.elim

@[simp] theorem emptyLaurentForm_R : emptyLaurentForm.R = fun _ => (0 : ℂ) := by
  funext z; simp [LaurentForm.R, emptyLaurentForm, Finset.univ_eq_empty]

@[simp] theorem emptyLaurentForm_image_a :
    (Finset.univ.image emptyLaurentForm.a) = (∅ : Finset ℂ) := by
  simp [emptyLaurentForm, Finset.image, Finset.univ_eq_empty]

/-- **Non-vacuity witness.**  When `f.div = 0`, a `LogDerivTrace f` exists: the empty `LaurentForm`
(no monomials, so `R ≡ 0` and `Res_∞ = 0`), with vacuous fibre data and both fibre order sums `0`
(the support is empty).  Hence the `LogDerivTrace` obligations are *satisfiable* — the structure is
not a disguised `False`. -/
def logDerivTrace_of_div_eq_zero (f : MeromorphicFunction X)
    (h0 : (f.div : Divisor X) = 0) : LogDerivTrace f where
  L := emptyLaurentForm
  fibre := fun _ => emptyFibreTrace
  cs := fun _ i => i.elim
  hsp := fun _ i => i.elim
  hL32 := by intro p hp; rw [emptyLaurentForm_image_a] at hp; exact absurd hp (Finset.notMem_empty p)
  infty_eq := by
    rw [resAtInfty, emptyLaurentForm_R]
    show -(2 * π * I : ℂ)⁻¹ • (∮ _z in C((0 : ℂ), emptyLaurentForm.ρ), (0 : ℂ)) = _
    rw [show emptyLaurentForm.ρ = 0 from rfl, circleIntegral.integral_radius_zero, smul_zero, h0]
    simp
  finite_eq := by rw [emptyLaurentForm_image_a, Finset.sum_empty, h0]; simp

end Jacobians.ResidueTheoremX
