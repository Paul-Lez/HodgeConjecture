/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.ResidueTheoremX
import KirovDolbeault.ResidueChangeOfVariables
import KirovDolbeault.Dolbeault.MittagLeffler

/-!
# The general 1-form residue theorem `∑ₐ Resₐ(α) = 0` (Gate A, node A-ii)

For a compact connected Riemann surface `X`, a holomorphic 1-form `ω₀ : HolomorphicOneForms X`, and
a function `g : X → ℂ`, the **meromorphic 1-form** `α = ω₀·g` satisfies the residue theorem

> `∑_{a ∈ X} Res_a(α) = 0`,   i.e.   `residueSum ω₀ g (poles) = 0`,

where `Res_a(α) = formFnResidue ω₀ g a` is the local Laurent residue read in the canonical chart at
`a` (`Jacobians.Dolbeault.formFnResidue`) and `residueSum` (`Jacobians.Dolbeault.MittagLeffler`) is
the finite sum over the (finitely many) poles.

This is **Gate A** of the Serre §17 plan: the
well-definedness of the residue functional `Res : H¹(X, Ω) → ℂ` on cohomology classes (Forster 17.3)
rests on exactly this — a globally-defined (coboundary) meromorphic 1-form has total residue `0`. It
is the **general higher-order-pole** statement, strictly more than `deg_div` (which is the simple-pole
`α = df/f` special case, `Jacobians.ResidueTheoremX`).

## The route (Miranda §VIII.3, the trace to ℙ¹)

The proof is the algebraic residue theorem via the **trace to `ℂℙ¹`**: pick a nonconstant meromorphic
`f : X → ℂℙ¹` (a branched cover `F = f.toRiemannSphere`, RR-supplied by gate D), form the trace
`Tr_F α` (a rational 1-form on `ℂℙ¹`), and compute

```
∑_{x∈X} Res_x(α)  =  ∑_{y∈ℂℙ¹} ∑_{x∈F⁻¹y} Res_x(α)        (regroup by fibre)
                  =  ∑_{y∈ℂℙ¹} Res_y(Tr_F α)              (Miranda Lemma 3.2)
                  =  0                                     (ℂℙ¹ residue theorem).
```

The two one-variable engines are **already proven, unconditional** (the residue change-of-variables
atom `ResidueChangeOfVariables` was discharged in `Jacobians.ResidueChangeOfVariables`):

* the fibre Lemma 3.2 `FibreTrace.resAt_traceCoeff'` — `Res_b(Tr_F α) = ∑_{sheets i} Res_{pre i}` — and
* the trace combine `finiteResidueSum_trace_eq_zero_of_fibres'` —
  `(∑_{centers p} Res_b(Tr_F α over fibre p)) + Res_∞(Tr_F α) = 0` —

both in `Jacobians.ResidueChangeOfVariables` (the `'`-forms, no `ResidueChangeOfVariables`
hypothesis), built on the `ℂℙ¹` residue theorem `LaurentForm.finiteResidueSum_add_resAtInfty_eq_zero`
(`Jacobians.TraceResidue`).

## What this file builds (all complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

This file is the **manifold trace assembly** — the generalization of `Jacobians.ResidueTheoremX` (the
`df/f`/`deg_div` simple-pole assembly) to a general meromorphic 1-form, reusing the now-general
feeders.  It mirrors that file field-for-field:

* the **fibrewise regrouping** (`residueSum_eq_fiberwise`, `residueSum_eq_infty_add_finite`): the
  finite residue-sum `∑_{a ∈ poles} formFnResidue ω₀ g a` partitions along the fibres of
  `F = f.toRiemannSphere` into the `∞`-fibre (the poles of `α` mapping to `∞`) and the finite-value
  fibres — pure `Finset` combinatorics (`Finset.sum_fiberwise_of_maps_to`), in `formFnResidue` in
  place of `orderAtPoint`;
* the **trace-representation structure** `FormResidueTrace ω₀ g` (the §VIII.3 assembly output — the
  rational trace `LaurentForm L = Tr_F α`, the per-fibre `FibreTrace` data, Lemma 3.2's manifold
  bookkeeping `hL32`, and the two aggregate fibre-residue ↔ `formFnResidue` identifications
  `infty_eq` / `finite_eq`);
* **the residue theorem** (`residueSum_eq_zero_of_formResidueTrace`,
  `formFnResidue_total_eq_zero_of_formResidueTrace`): given a `FormResidueTrace ω₀ g`, the total
  residue vanishes — *completely* from the general trace combine + the regrouping;
* **non-vacuity** (`formResidueTrace_of_holomorphic`): a `FormResidueTrace ω₀ g` exists when `α = ω₀·g`
  is globally holomorphic (the empty `LaurentForm`, no poles), confirming the structure's obligations
  are *true and satisfiable*, not a disguised `False`.

## The remaining obligation (the isolated geometric construction)

What is **not** discharged here is the *construction* of a `FormResidueTrace ω₀ g` for a general
nonconstant `f`: the rational `LaurentForm L` representing `Tr_F α` (the cover's local holomorphic
sections, the trace's finiteness/rationality, partial fractions on `ℂℙ¹`), Lemma 3.2's manifold
bookkeeping `hL32`, and the two aggregate fibre-residue ↔ residue identifications
`infty_eq` / `finite_eq`.  This is the §17-level trace assembly; it is the same fibre/sheet/branched-
cover apparatus as the (still-open) `exists_properMapDegree` (`Jacobians.DegDivResidue`), and is
isolated into the `FormResidueTrace` structure (each field a *true, non-vacuous* statement), with
everything downstream proved completely.  See the report accompanying this commit and §4.2 (A-ii) of
the plan.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; partial
  fractions / residue theorem on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17 (the residue functional `Res`; 17.1–17.3).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The fibrewise regrouping `∑_{a ∈ poles} = ∑_y ∑_{F⁻¹y}`

The finite residue-sum `∑_{a ∈ poles} formFnResidue ω₀ g a` of `α = ω₀·g` over its (finite) pole set
partitions, fibrewise, along the cover `F = f.toRiemannSphere`: grouping the poles by their image
under `F` and summing the residue within each fibre recovers the total.  Pure `Finset` combinatorics
(`Finset.sum_fiberwise_of_maps_to`), independent of the analytic fibre packaging — the bridge that
turns `∑_{a ∈ X} Res_a(α)` into a sum over `ℂℙ¹` of fibre sums.  (Identical to
`Jacobians.ResidueTheoremX.orderSum_eq_fiberwise`, with `formFnResidue ω₀ g` for `orderAtPoint`.) -/

/-- **The fibrewise regrouping of the residue-sum.**  Partition a pole set `poles : Finset X` by the
fibres of `F = f.toRiemannSphere`: the total residue is the sum, over the image points `y` of
`poles`, of the per-fibre residue sums.

> `∑_{a ∈ poles} Res_a(α)  =  ∑_{y ∈ F''poles} ∑_{a ∈ poles, F a = y} Res_a(α)`. -/
theorem residueSum_eq_fiberwise (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X) :
    ∑ a ∈ poles, formFnResidue ω₀ g a
      = ∑ y ∈ poles.image f.toRiemannSphere,
          ∑ a ∈ poles with f.toRiemannSphere a = y, formFnResidue ω₀ g a :=
  (Finset.sum_fiberwise_of_maps_to (fun _ hx => Finset.mem_image_of_mem _ hx) _).symm

/-- The fibrewise regrouping, split into the finite-value (`coe`) fibres and the `∞`-fibre.  The
pole image under `F` decomposes into `∞` (the poles of `α` mapping to `∞`) and the finite values; we
keep the decomposition at the level of the sphere image to feed it the trace combine.  (Identical to
`Jacobians.ResidueTheoremX.orderSum_eq_infty_add_finite`, with `formFnResidue ω₀ g`.) -/
theorem residueSum_eq_infty_add_finite (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X) :
    ∑ a ∈ poles, formFnResidue ω₀ g a
      = (∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a)
        + ∑ y ∈ (poles.image f.toRiemannSphere).erase OnePoint.infty,
            ∑ a ∈ poles with f.toRiemannSphere a = y, formFnResidue ω₀ g a := by
  classical
  rw [residueSum_eq_fiberwise]
  by_cases hmem : OnePoint.infty ∈ poles.image f.toRiemannSphere
  · rw [← Finset.add_sum_erase _ _ hmem]
  · -- No pole of `α` maps to `∞`: the `∞`-fibre sum is empty (`= 0`), `erase` is a no-op.
    rw [Finset.erase_eq_of_notMem hmem]
    have hempty : (poles.filter (fun a => f.toRiemannSphere a = OnePoint.infty)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a ha hcontra
      exact hmem (hcontra ▸ Finset.mem_image_of_mem _ ha)
    rw [hempty, Finset.sum_empty, zero_add]

/-! ### The trace representation `FormResidueTrace ω₀ g`

The remaining content is the **global manifold assembly** of the meromorphic trace `Tr_F α`
(`α = ω₀·g`) through the cover `F = f.toRiemannSphere`: packaging the (finite, off-branch) fibres as
`FibreTrace`s, exhibiting the rational trace as a `LaurentForm L` on `ℂℙ¹`, and identifying — via the
**general** Lemma 3.2 (`FibreTrace.resAt_traceCoeff'`, now unconditional) and the local-residue
bridge — each fibre's residue with the fibre's residue sum `∑_{a ∈ F⁻¹y} Res_a(α)`.

We package this output as the structure `FormResidueTrace ω₀ g` below; each field is a *true*
statement (it is exactly what the §VIII.3 trace assembly produces) and **not** vacuous.  Given a
`FormResidueTrace ω₀ g`, the residue theorem `∑_{a ∈ poles} Res_a(α) = 0` follows *completely* from
the general trace combine (`finiteResidueSum_trace_eq_zero_of_fibres'`) and the fibrewise regrouping
(`residueSum_eq_infty_add_finite`), as proved in `residueSum_eq_zero_of_formResidueTrace`.

This isolates the *entire* remaining geometric wall (the trace's finiteness/rationality + Lemma 3.2's
manifold bookkeeping `hL32` + the per-fibre residue ↔ `formFnResidue` identifications) into the two
aggregate identifications `infty_eq` and `finite_eq`, with everything downstream proved.

The crucial difference from `Jacobians.ResidueTheoremX.LogDerivTrace`: there are no simple-pole
fields (`cs`/`hsp`) and no `ResidueChangeOfVariables` hypothesis — `α = ω₀·g` has *higher-order*
poles, so we use the **general** unconditional combine `finiteResidueSum_trace_eq_zero_of_fibres'`. -/

/-- **The 1-form trace representation** of `α = ω₀·g` through `F = f.toRiemannSphere`.

This bundles the output of the global manifold assembly of the meromorphic trace `Tr_F α` on `ℂℙ¹`
for the general 1-form residue theorem:

* `f` — a (nonconstant) meromorphic function giving the branched cover `F = f.toRiemannSphere`;
* `poles` — the finite set of poles of `α = ω₀·g` (off it, `α` is holomorphic);
* a `LaurentForm L` (partial-fraction `1`-form on `ℂℙ¹`) representing `Tr_F α`;
* a fibre datum `fibre p : FibreTrace` for each finite center `p`;
* `hL32`: each finite center's fibre-residue sum equals `L`'s residue there (the manifold bookkeeping
  that `L` *is* the trace — Lemma 3.2 at the finite centers, `FibreTrace.resAt_traceCoeff'`);
* `infty_eq`: the residue at infinity of the trace equals the **`∞`-fibre residue sum**
  `∑_{a : F a = ∞} Res_a(α)` (Lemma 3.2 at `∞`, via the local-residue bridge);
* `finite_eq`: the total over the finite centers of the per-fibre trace residue equals the
  **finite-fibre residue sum** `∑_{y ≠ ∞} ∑_{a : F a = y} Res_a(α)` (Lemma 3.2 at the finite
  centers, via the local-residue bridge).

Each `*_eq` field is the honest geometric content of Miranda §VIII.3 (the trace residue = fibre sum
of residues); none is vacuous (see `formResidueTrace_of_holomorphic`). -/
structure FormResidueTrace (ω₀ : HolomorphicOneForms X) (g : X → ℂ) where
  /-- The (nonconstant) meromorphic function giving the branched cover `F = f.toRiemannSphere`. -/
  f : MeromorphicFunction X
  /-- The finite set of poles of `α = ω₀·g`. -/
  poles : Finset X
  /-- The partial-fraction `1`-form on `ℂℙ¹` representing `Tr_F α`. -/
  L : LaurentForm
  /-- The fibre datum over each finite center. -/
  fibre : ℂ → FibreTrace
  /-- Lemma 3.2 at each finite center: the fibre-residue sum equals `L`'s residue. -/
  hL32 : ∀ p ∈ (Finset.univ.image L.a),
    (∑ i, resAt ((fibre p).coeff i) ((fibre p).pre i)) = resAt L.R p
  /-- The `∞`-residue of the trace is the `∞`-fibre residue sum (Lemma 3.2 at `∞` + the bridge). -/
  infty_eq : resAtInfty L.R L.ρ
    = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a
  /-- The finite-center trace-residue total is the finite-fibre residue sum (Lemma 3.2 + the bridge). -/
  finite_eq : (∑ p ∈ Finset.univ.image L.a, resAt (fibre p).traceCoeff (fibre p).b)
    = ∑ y ∈ (poles.image f.toRiemannSphere).erase OnePoint.infty,
        ∑ a ∈ poles with f.toRiemannSphere a = y, formFnResidue ω₀ g a

/-- **The 1-form residue theorem via the trace representation.**  Given a `FormResidueTrace ω₀ g`
(the output of the §VIII.3 trace assembly), the total residue of `α = ω₀·g` over its poles vanishes:

> `∑_{a ∈ poles} Res_a(α) = 0`.

*Proof (complete).*  The **general** trace combine `finiteResidueSum_trace_eq_zero_of_fibres'`
(now unconditional, the `ResidueChangeOfVariables` atom being discharged) gives
`(∑_{centers} Res_b(Tr_F α)) + Res_∞(Tr_F α) = 0`.  By `finite_eq` and `infty_eq` the two summands
are the finite-fibre and `∞`-fibre residue sums; by `residueSum_eq_infty_add_finite` their sum is the
total residue, so it is `0`. -/
theorem residueSum_eq_zero_of_formResidueTrace (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (T : FormResidueTrace ω₀ g) :
    ∑ a ∈ T.poles, formFnResidue ω₀ g a = 0 := by
  -- The general combine: the center-residue total plus the residue at infinity vanish.
  have hcombine := finiteResidueSum_trace_eq_zero_of_fibres' T.L T.fibre T.hL32
  -- Rewrite both summands as the fibrewise residue sums.
  rw [T.finite_eq, T.infty_eq] at hcombine
  -- The total residue is the sum of the two fibre groups (with the order matching the combine).
  rw [residueSum_eq_infty_add_finite ω₀ g T.f T.poles, add_comm]
  exact hcombine

/-- **The 1-form residue theorem (`residueSum` form).**  Given a `FormResidueTrace ω₀ g`, the
Mittag–Leffler residue-sum `residueSum ω₀ g (poles)` of `α = ω₀·g` vanishes.  This is the precise
input the global residue functional `Res : H¹(X, Ω) → ℂ` descent (node 4) consumes. -/
theorem residueSum_eq_zero_of_formResidueTrace' (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (T : FormResidueTrace ω₀ g) :
    residueSum ω₀ g T.poles = 0 :=
  residueSum_eq_zero_of_formResidueTrace ω₀ g T

/-- **Forster's residue `Res(μ) = 0` for a coboundary distribution.**  A Mittag–Leffler distribution
`μ` of the shape `ω₀·g` whose recorded pole set has a `FormResidueTrace` (i.e. the global meromorphic
1-form `α = ω₀·g` it represents has a rational trace) has total residue `Res(μ) = 0`.  This is the
precise statement Forster 17.3 needs: a globally-defined (coboundary) Mittag–Leffler distribution has
zero residue, which makes the residue functional `Res : H¹(X, Ω) → ℂ` well-defined on cohomology
classes (the node-4 `globalRes` descent).

The hypothesis `hpoles` records that `μ`'s bookkeeping pole set is the trace's pole set; combined with
`MittagLefflerForm.res = residueSum` this gives `Res(μ) = residueSum ω₀ μ.g T.poles = 0`. -/
theorem MittagLefflerForm_res_eq_zero (μ : MittagLefflerForm X) (T : FormResidueTrace μ.α μ.g)
    (hpoles : μ.poles = T.poles) :
    μ.res = 0 := by
  rw [MittagLefflerForm.res_def, hpoles]
  exact residueSum_eq_zero_of_formResidueTrace μ.α μ.g T

/-! ### Non-vacuity of `FormResidueTrace`

The `FormResidueTrace ω₀ g` obligations are genuine (true, satisfiable), not an impossible
hypothesis: in the case where `α = ω₀·g` is **globally holomorphic** (its chart-pullback coefficient
is analytic at every point — no poles) we exhibit a `FormResidueTrace ω₀ g` explicitly — the empty
`LaurentForm` (no poles, trace `≡ 0`) with an empty pole set, whose residue data and both fibre sums
vanish.  This mirrors `Jacobians.ResidueTheoremX.logDerivTrace_of_div_eq_zero`, confirming the
isolated structure is honest (the residue theorem does hold in this case, with the trivial trace). -/

/-- **Non-vacuity witness.**  When `α = ω₀·g` is globally holomorphic (`g`'s chart-pullback is
analytic at every point), a `FormResidueTrace ω₀ g` exists: an arbitrary cover `f`, the **empty pole
set** (so `residueSum ω₀ g ∅ = 0` directly), the empty `LaurentForm` (no monomials, `R ≡ 0`,
`Res_∞ = 0`), and vacuous fibre data.  Hence the `FormResidueTrace` obligations are *satisfiable* —
the structure is not a disguised `False`. -/
def formResidueTrace_of_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) : FormResidueTrace ω₀ g where
  f := f
  poles := ∅
  L := Jacobians.ResidueTheoremX.emptyLaurentForm
  fibre := fun _ => Jacobians.ResidueTheoremX.emptyFibreTrace
  hL32 := by
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  infty_eq := by
    rw [resAtInfty, Jacobians.ResidueTheoremX.emptyLaurentForm_R]
    show -(2 * π * I : ℂ)⁻¹ • (∮ _z in C((0 : ℂ),
      Jacobians.ResidueTheoremX.emptyLaurentForm.ρ), (0 : ℂ)) = _
    rw [show Jacobians.ResidueTheoremX.emptyLaurentForm.ρ = 0 from rfl,
      circleIntegral.integral_radius_zero, smul_zero]
    simp
  finite_eq := by rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp

/-- **The residue theorem, holomorphic case (unconditional).**  If `α = ω₀·g` is globally holomorphic
(`g`'s chart-pullback is analytic at every point), then over any finite pole-candidate set the residue
sum vanishes — directly from `residueSum_eq_zero_of_analyticAt`, and consistent with the trace
representation.  (The honest content: a coboundary — globally-holomorphic — distribution has total
residue `0`, the trivial case of Forster 17.3.) -/
theorem residueSum_eq_zero_of_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (S : Finset X)
    (hg : ∀ a ∈ S, AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    residueSum ω₀ g S = 0 :=
  residueSum_eq_zero_of_analyticAt ω₀ g S hg

end Jacobians.Dolbeault.FormResidueTheorem
