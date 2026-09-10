/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedCenter
import KirovDolbeault.Dolbeault.FormTracePrincipalPart

/-!
# The ramified geometric-trace identification `hcoh` (Forster §5 `z = wᵐ` normal form, slit branch)

This file builds the genuine geometric content of `RamifiedCenterFacts.hcoh`
(`Jacobians/Dolbeault/SerreResidueRamifiedCenter.lean`): at a (possibly ramified) finite pole-value
centre `c` of `α = ω₀·g`, the **geometric** value-chart trace germ `valueChartTrace ω₀ f Φ` near `c`
*is* the **algebraic** `m`-sheet-sum trace of the per-preimage chart integrands.  It is the ramified
analogue of `exists_planar_section` (`FormTraceFibre.lean`, the unramified local biholomorphism that
identifies the geometric chart with the value chart), now for a ramification point of multiplicity
`m`, where the cover is the branched normal form `z = wᵐ` (Forster GTM 81, §5).

## ⚠ The monodromy obstruction — why the branch lives on a *slit*, not all of `𝓝[≠] c`

There is **no single-valued holomorphic `m`-th root of `z − c` on a punctured disk** when `m > 1`:
analytically continuing `(z − c)^{1/m}` once around `c` multiplies it by `ζ ≠ 1` (monodromy).  So the
two demands "`w₀` analytic on `𝓝[≠] c`" **and** "`w₀(z)ᵐ = z − c` on `𝓝[≠] c`" are *jointly
contradictory* for `m > 1`.  (An earlier version of `RamifiedSheetData` demanded exactly this — making
it a disguised `False` at every genuine ramification centre, satisfiable only at `m = 1`.  This file
fixes that.)

The resolution (the standard one): a holomorphic branch `w₀` of `(z − c)^{1/m}` **does** exist on a
*slit* `S` — a simply-connected open subset of the punctured neighbourhood, e.g. the punctured disk
minus a ray (concretely `{z | z − c ∈ slitPlane}`, on which `w₀ z = (z − c)^{1/m}` via `Complex.cpow`).
On the slit the geometry is exactly the unramified `m`-sheet picture, and the proven atom applies.  But
both the geometric trace `valueChartTrace` and the algebraic trace are **single-valued analytic on the
*full* punctured neighbourhood**: `valueChartTrace` because it is the *symmetric* sum over the `m`-point
fibre (a set — independent of the sheet labelling; Miranda (3.1) makes it meromorphic at `c`), and the
algebraic trace `ramifiedTraceTerm + Rem` by construction.  Two functions meromorphic at `c` that agree
on a slit accumulating at `c` agree on all of `𝓝[≠] c` by the **identity theorem**
(`MeromorphicAt.frequently_eq_iff_eventuallyEq`).  That is how `hcoh` is *derived* (never asserted).

## The geometry on the slit (Miranda §VIII.3, Forster §5)

On the slit, with the centered chart `w = chart_p` at `p`, the cover reads `z − c = (w − w_p)ᵐ` and the
fibre splits into the `m` sheets `w = w_p + ζʲ·w₀(z)` (`ζ` a primitive `m`-th root of unity).  The
value-chart trace over those sheets is the `m`-sheet sum

> `∑_{j<m} h(w_p + ζʲ w₀(z)) · (d/dz)[w_p + ζʲ w₀(z)]`,    `h := chartIntegrand ω₀ g p`,

with `(d/dz)[w_p + ζʲ w₀(z)] = ζʲ w₀'(z) = ζʲ·(1/m) w₀(z)^{1−m}` (from `m w₀^{m−1} w₀' = 1`).  By the
proven roots-of-unity collapse (`Jacobians.RamifiedTrace.laurentTraceCoeff_eq_sheetSum`) this `m`-sheet
sum, applied to the **Laurent principal part** of `h` at `w_p`, equals the closed-form
`laurentTraceCoeff (z − c)` — exactly the algebraic `ramifiedTraceTerm` whose residue is the upstairs
residue (`resAt_laurentTraceCoeff`).  The holomorphic remainder of `h` contributes a holomorphic trace
`Rem` (single-valued at `c` by the symmetric-function descent), which the residue does not see.

## What this file delivers

* **`RamifiedSheetData`** (the genuine geometric input): at one preimage `p`, the multiplicity `m`, a
  primitive `m`-th root `ζ`, a **slit** `S` accumulating at `c`, a holomorphic branch `w₀` of
  `(z − c)^{1/m}` **on `S`** (the Forster §5 analytic atom — the slit `m`-th root, which exists for any
  `m`), the per-preimage Laurent principal-part data + the **single-valued** analytic remainder trace
  `Rem`, the geometric identification `hgeom_slit` (on the slit), and — the genuine new content — the
  **single-valued meromorphy of the symmetric trace sum** `hvct_mero` at `c`.  All supplied as *data*,
  none asserted as a free lemma.

* **`eventuallyEq_of_meromorphic_eqOn_slit`** (the identity-theorem bridge, #3): two functions
  meromorphic at `c` agreeing on a slit accumulating at `c` agree on `𝓝[≠] c`
  (`MeromorphicAt.frequently_eq_iff_eventuallyEq`).

* **`RamifiedSheetData.traceFull` / `hcoh`** (the genuine new analytic content): the single-valued
  algebraic trace `T = ramifiedTraceTerm (principal part) + Rem`, equal on the slit to the geometric
  `m`-sheet sum (the atom, #1), hence equal to `valueChartTrace` on `𝓝[≠] c` by the identity theorem.

* **`RamifiedCenterFacts.ofSheetData`** (the sound capstone): assembles a `RamifiedCenterFacts` whose
  carried trace `T` is the single-valued `ramifiedTraceTerm + Rem`, with `hcoh` derived via the slit +
  identity theorem and `hmero`/`hres` via the proven atom.  Single-preimage form.

## ⚠ Soundness

* **No monodromy contradiction.**  `w₀` is required analytic only on the *slit* `S`; the structure is
  satisfiable for `m > 1` (`ramifiedSheetData_sqrt`, an explicit `m = 2` witness with the genuine slit
  branch `√(z − c)`), not just `m = 1`.
* `T = ramifiedTraceTerm + Rem` is single-valued meromorphic at `c`; `hcoh : valueChartTrace =ᶠ[𝓝[≠] c]
  T` is **derived** (identity theorem from agreement on the slit), never asserted.  `hmero`/`hres` come
  from the atom; `Rem` (analytic) contributes residue `0`.
* Every trace statement is the `m`-sheet **SUM** (the atom's roots-of-unity factor `∑(ζʲ)⁰ = m`
  cancels the chain-rule `1/m`); there is no single-sheet "`m·Res`" shortcut.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (local normal form `z = wᵐ`).
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, (3.1) (Tr single-valued meromorphic
  in `z`), Lemma 3.2 ramified case.
* `Jacobians/RamifiedResidueChangeOfVariables.lean` (`laurentTraceCoeff_eq_sheetSum`, the atom).
* `Mathlib.Analysis.Meromorphic.IsolatedZeros` (`MeromorphicAt.frequently_eq_iff_eventuallyEq`, the
  identity theorem).
* `Jacobians/Dolbeault/FormTraceFibre.lean` (`exists_planar_section`, the unramified template).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip
  Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.RamifiedTrace

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The identity-theorem bridge (slit → punctured neighbourhood)

The mechanism by which a *slit* identity globalises: two functions meromorphic at `c` that agree on a
set accumulating at `c` agree on the whole punctured neighbourhood (Mathlib's meromorphic identity
theorem `MeromorphicAt.frequently_eq_iff_eventuallyEq`).  A slit (e.g. punctured-disk-minus-a-ray)
accumulates at `c`, so a branch-built equality on the slit upgrades to a `𝓝[≠] c` germ-equality. -/

/-- **Identity theorem on a slit.**  If `f` and `g` are meromorphic at `c` and agree on a set `S` that
accumulates at `c` (`∃ᶠ z in 𝓝[≠] c, z ∈ S` — true for a slit), then `f =ᶠ[𝓝[≠] c] g`.  This is the
engine that turns the slit-only branch identity into a punctured-neighbourhood germ-equality (so the
multivalued `m`-th root is needed only on the slit, dodging the monodromy obstruction). -/
theorem eventuallyEq_of_meromorphic_eqOn_slit {f h : ℂ → ℂ} {c : ℂ} {S : Set ℂ}
    (hf : MeromorphicAt f c) (hh : MeromorphicAt h c)
    (hacc : ∃ᶠ z in 𝓝[≠] c, z ∈ S) (hfh : ∀ z ∈ S, f z = h z) :
    f =ᶠ[𝓝[≠] c] h :=
  (MeromorphicAt.frequently_eq_iff_eventuallyEq hf hh).mp (hacc.mono hfh)

/-! ### The Forster §5 slit sheet data (the genuine geometric input)

`RamifiedSheetData` packages, at one preimage `p` of multiplicity `m` over a centre `c`, the Forster
§5 local normal-form geometry as *data* (the ramified analogue of the `exists_planar_section` output),
**with the monodromy obstruction respected**: the `m`-th-root branch `w₀` lives on a *slit* `S`, not on
all of `𝓝[≠] c`.  The data also carries the single-valued algebraic trace ingredients (the Laurent
principal part of the chart integrand, and the single-valued analytic remainder trace `Rem`) plus the
genuine new content — the single-valued meromorphy of the symmetric trace sum `valueChartTrace` at `c`.
Everything downstream (`T`, `hcoh`, the residue/meromorphy) is *derived*. -/

/-- **Forster §5 slit sheet data at one preimage.**  At a preimage `p` of multiplicity `m ≥ 1` over the
centre `c`, with chart coordinate `wp := chart_p p`:

* `ζ` a primitive `m`-th root of unity;
* a **slit** `S ⊆ ℂ` accumulating at `c` (`hS_acc`), with a holomorphic branch `w₀` of `(z − c)^{1/m}`
  **on `S`** — nonvanishing (`hw₀_ne`), an `m`-th root (`hw₀_pow`), with the chain-rule derivative
  (`hw₀_deriv`).  This is the **Forster §5 analytic atom**, restricted to the slit where it exists for
  *any* `m` (no monodromy contradiction);
* per-preimage Laurent **principal-part data** of the chart integrand `h := chartIntegrand ω₀ g p`:
  degree `ppN`, coefficients `ppb`, analytic remainder `ppR` (`hppR_an`), with the split holding at the
  sheet points along the slit (`hpp_split_sheet`).  `hppN_res` records that the principal part carries
  the upstairs residue (a true fact about the Laurent expansion at `p`, *not* the downstairs residue);
* the **single-valued analytic remainder trace** `Rem` (`hRem_an : AnalyticAt ℂ Rem c`), the
  symmetric-function descent of the `m`-sheet sum of `ppR` (`hRem_slit`, on the slit) — the standard
  "trace of a holomorphic form is holomorphic", now stated as a single-valued function at `c`;
* the **geometric identification** `hgeom_slit`: on the slit, `valueChartTrace ω₀ f Φ` equals the
  `m`-sheet sum `∑_{j<m} h(wp + ζʲ w₀(z))·(d/dz)[wp + ζʲ w₀(z)]`;
* `hvct_mero` — the genuine new content (Miranda (3.1)): the symmetric trace sum `valueChartTrace ω₀ f Φ`
  (single-valued by construction — a *set* sum over the fibre) is **meromorphic at `c`**.

Supplied as *data* (as the unramified `MovingCoherenceDatum` is), never asserted as a free lemma; the
single-valued trace `T`, the punctured germ-equality `hcoh`, the residue and meromorphy are all
*derived* (`RamifiedCenterFacts.ofSheetData`). -/
structure RamifiedSheetData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (c : ℂ) where
  /-- The ramification preimage over `c`. -/
  p : X
  /-- The ramification multiplicity (`≥ 1`). -/
  m : ℕ
  /-- The multiplicity is positive. -/
  hm : 0 < m
  /-- A primitive `m`-th root of unity (the sheet rotation). -/
  ζ : ℂ
  /-- `ζ` is a primitive `m`-th root of unity. -/
  hζ : IsPrimitiveRoot ζ m
  /-- The **slit** on which the `m`-th-root branch is defined (e.g. a punctured-disk-minus-a-ray). -/
  S : Set ℂ
  /-- The slit accumulates at `c` (so the identity theorem applies). -/
  hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ S
  /-- The holomorphic branch of `(z − c)^{1/m}` on the slit. -/
  w₀ : ℂ → ℂ
  /-- The branch is nonzero on the slit. -/
  hw₀_ne : ∀ z ∈ S, w₀ z ≠ 0
  /-- The branch is an `m`-th root on the slit: `w₀(z)ᵐ = z − c`. -/
  hw₀_pow : ∀ z ∈ S, w₀ z ^ (m : ℤ) = z - c
  /-- The chain-rule derivative on the slit: `w₀'(z) = (1/m) w₀(z)^{1−m}` (from `m w₀^{m−1} w₀' = 1`). -/
  hw₀_deriv : ∀ z ∈ S, deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ))
  /-- `g`'s chart-pullback is meromorphic at `p`'s chart centre (so the chart integrand of `α = ω₀·g`
  has an isolated singularity — true since `p` is an isolated pole of `α`). -/
  hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)
  /-- Degree of the Laurent principal part of `chartIntegrand ω₀ g p` at `wp`. -/
  ppN : ℕ
  /-- Coefficients of the Laurent principal part. -/
  ppb : ℕ → ℂ
  /-- Analytic remainder of `chartIntegrand ω₀ g p` (the part holomorphic at `wp`). -/
  ppR : ℂ → ℂ
  /-- The remainder is analytic at `wp`. -/
  hppR_an : AnalyticAt ℂ ppR ((chartAt ℂ p) p)
  /-- **The principal-part split at the sheet points** (true by `exists_principalPart_meromorphicAt`):
  on the slit, the chart integrand decomposes as principal part `negTail` plus analytic remainder `ppR`
  at each of the `m` sheet arguments `wp + ζʲ w₀ z`. -/
  hpp_split_sheet : ∀ z ∈ S, ∀ j ∈ Finset.range m,
    chartIntegrand ω₀ g p ((chartAt ℂ p) p + ζ ^ j * w₀ z)
      = negTail ((chartAt ℂ p) p) ppb ppN ((chartAt ℂ p) p + ζ ^ j * w₀ z)
        + ppR ((chartAt ℂ p) p + ζ ^ j * w₀ z)
  /-- The principal part carries the upstairs residue (a true fact about the Laurent expansion of
  `chartIntegrand ω₀ g p` at `wp`; **not** the downstairs trace residue — no circularity). -/
  hppN_res : resAt (fun w => ∑ k ∈ Finset.Icc 1 ppN, ppb k * (w - 0) ^ (-(k : ℤ))) 0
    = formFnResidue ω₀ g p
  /-- The **single-valued analytic remainder trace** at `c` (the symmetric-function descent of the
  `m`-sheet sum of the holomorphic remainder `ppR`). -/
  Rem : ℂ → ℂ
  /-- The remainder trace is analytic at `c` (trace of a holomorphic form is holomorphic). -/
  hRem_an : AnalyticAt ℂ Rem c
  /-- The remainder trace agrees, on the slit, with the `m`-sheet sum of `ppR`. -/
  hRem_slit : ∀ z ∈ S, Rem z = ∑ j ∈ Finset.range m,
    ppR ((chartAt ℂ p) p + ζ ^ j * w₀ z)
      * deriv (fun ζz => (chartAt ℂ p) p + ζ ^ j * w₀ ζz) z
  /-- **The geometric trace identification on the slit** (Forster §5): on the slit, the value-chart
  trace is the `m`-sheet sum of the chart integrand of `α = ω₀·g` at `p`, read along `w = wp + ζʲ w₀`. -/
  hgeom_slit : ∀ z ∈ S, valueChartTrace ω₀ f Φ z = ∑ j ∈ Finset.range m,
    chartIntegrand ω₀ g p ((chartAt ℂ p) p + ζ ^ j * w₀ z)
      * deriv (fun ζz => (chartAt ℂ p) p + ζ ^ j * w₀ ζz) z
  /-- **Single-valued meromorphy of the symmetric trace sum** (the genuine new content, Miranda (3.1)):
  `valueChartTrace ω₀ f Φ` — single-valued by construction (a sum over the *fibre set*, independent of
  sheet labels) — is meromorphic at `c`. -/
  hvct_mero : MeromorphicAt (valueChartTrace ω₀ f Φ) c

/-! ### The sheet-`j` derivative `(d/dz)[wp + ζʲ w₀(z)] = ζʲ w₀'(z)`

The sheet `z ↦ wp + ζʲ w₀(z)` has derivative `ζʲ w₀'(z)` wherever `w₀` is differentiable: it is the
constant `wp` plus the scalar `ζʲ` times `w₀`. -/

/-- The sheet-`j` derivative.  `(d/dz)[wp + ζʲ w₀(z)] = ζʲ · w₀'(z)` (unconditional: constant `wp`
plus the field scalar `ζʲ` times `w₀`). -/
theorem deriv_sheet_eq (w₀ : ℂ → ℂ) (z wp ζj : ℂ) :
    deriv (fun ζz => wp + ζj * w₀ ζz) z = ζj * deriv w₀ z := by
  have h1 : deriv (fun ζz => wp + ζj * w₀ ζz) z = deriv (fun ζz => ζj * w₀ ζz) z :=
    deriv_const_add (f := fun ζz => ζj * w₀ ζz) wp
  rw [h1, deriv_const_mul_field]

/-! ### The planar `m`-sheet trace of a Laurent polynomial integrand (the atom, on the geometry)

The reusable algebraic core: when the chart integrand near `wp` is the Laurent polynomial
`W ↦ ∑_i cf_i (W − wp)^{n_i}`, its `m`-sheet sum along `w = wp + ζʲ w₀(z)` is exactly the closed-form
`laurentTraceCoeff (z − c) = ramifiedTraceTerm`, by the proven roots-of-unity collapse
`laurentTraceCoeff_eq_sheetSum`.  The branch `w₀` (`w₀ ≠ 0`, `w₀ᵐ = z − c`, `w₀' = (1/m) w₀^{1−m}`)
turns the geometric sheet sum into the atom's LHS verbatim. -/

/-- **The geometric `m`-sheet sum of a Laurent-polynomial integrand is `ramifiedTraceTerm`.**  For the
Laurent polynomial integrand `hpoly W := ∑_{i ∈ s} cf_i (W − wp)^{n_i}` and the branch `w₀` at `z`
(`w₀ z ≠ 0`, `w₀(z)ᵐ = z − c`, `w₀'(z) = (1/m) w₀(z)^{1−m}`, `ζ` a primitive `m`-th root), the
`m`-sheet sum `∑_{j<m} hpoly(wp + ζʲ w₀(z))·(d/dz)[wp + ζʲ w₀(z)]` equals
`ramifiedTraceTerm s cf n m c z`.  Pure algebra: substitute `W − wp = ζʲ w₀(z)` and the chain-rule
derivative, then apply the atom's soundness identity `laurentTraceCoeff_eq_sheetSum`. -/
theorem ramifiedSheetSum_laurentPoly {ι : Type*} (s : Finset ι) (cf : ι → ℂ) (n : ι → ℤ) {m : ℕ}
    (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {w₀ : ℂ → ℂ} {z wp c : ℂ}
    (hne : w₀ z ≠ 0) (hpow : w₀ z ^ (m : ℤ) = z - c)
    (hderiv : deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ))) :
    (∑ j ∈ Finset.range m, (∑ i ∈ s, cf i * (wp + ζ ^ j * w₀ z - wp) ^ n i)
        * deriv (fun ζz => wp + ζ ^ j * w₀ ζz) z)
      = ramifiedTraceTerm s cf n m c z := by
  -- Rewrite each summand: `(wp + ζʲ w₀ − wp) = ζʲ w₀`, and the derivative `= ζʲ·(1/m) w₀^{1−m}`.
  have hstep : ∀ j ∈ Finset.range m,
      (∑ i ∈ s, cf i * (wp + ζ ^ j * w₀ z - wp) ^ n i)
          * deriv (fun ζz => wp + ζ ^ j * w₀ ζz) z
        = (∑ i ∈ s, cf i * (ζ ^ j * w₀ z) ^ n i)
          * (ζ ^ j * ((m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ)))) := by
    intro j _
    rw [deriv_sheet_eq w₀ z wp (ζ ^ j), hderiv, add_sub_cancel_left]
  rw [Finset.sum_congr rfl hstep]
  -- The atom's soundness identity, evaluated at the branch `w₀ z` (`= (z − c)^{1/m}`).
  rw [laurentTraceCoeff_eq_sheetSum s cf n hm hζ (w₀ z) hne]
  -- `laurentTraceCoeff … (w₀ zᵐ) = laurentTraceCoeff … (z − c) = ramifiedTraceTerm … z`.
  rw [hpow]
  rfl

/-! ### The single-valued algebraic trace `T` and the slit identity

From the slit sheet data `S`, the **single-valued** algebraic trace is

> `T := ramifiedTraceTerm (Icc 1 ppN) ppb (k ↦ −k) m c  +  Rem`

(`ramifiedTraceTerm` the `m`-sheet-sum trace of the integrand's Laurent **principal part**, `Rem` the
single-valued analytic remainder trace).  `T` is single-valued and meromorphic at `c` *by
construction*.  On the slit `S`, `T` equals the geometric `m`-sheet sum `valueChartTrace` (the proven
atom `ramifiedSheetSum_laurentPoly` + the data fields).  Since both `T` and `valueChartTrace` are
meromorphic at `c` and the slit accumulates at `c`, the identity theorem upgrades the slit identity to
the punctured germ-equality `hcoh` — without ever needing the multivalued branch off the slit. -/

namespace RamifiedSheetData

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ}

/-- The **single-valued** algebraic trace carried as `T`: the `m`-sheet-sum trace of the integrand's
Laurent principal part (`ramifiedTraceTerm`, a single-valued meromorphic function of `z − c`) plus the
single-valued analytic remainder trace `Rem`.  This is single-valued and meromorphic at `c` by
construction — it does **not** reference the multivalued branch `w₀`. -/
noncomputable def traceFull (S : RamifiedSheetData ω₀ g f Φ c) : ℂ → ℂ :=
  fun z => ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c z + S.Rem z

/-- **The slit identity** (the genuine ramified Lemma 3.2 on the slit): on the slit, the geometric
trace `valueChartTrace` equals the single-valued algebraic trace `T = ramifiedTraceTerm + Rem`.  Proof:
`hgeom_slit` (geometric = `m`-sheet sum of the chart integrand), then the principal-part split at the
sheet points (`hpp_split_sheet`), the proven atom (`ramifiedSheetSum_laurentPoly`, turning the
principal-part sheet sum into `ramifiedTraceTerm`), and `hRem_slit` (the remainder sheet sum is `Rem`). -/
theorem eqOn_traceFull_slit (S : RamifiedSheetData ω₀ g f Φ c) :
    ∀ z ∈ S.S, valueChartTrace ω₀ f Φ z = S.traceFull z := by
  classical
  intro z hz
  set wp := (chartAt ℂ S.p) S.p with hwp
  -- Geometric: `valueChartTrace z = ∑ⱼ chartIntegrand(wp + ζʲ w₀ z)·deriv(sheet j)`.
  rw [S.hgeom_slit z hz]
  -- Split each `chartIntegrand(sheet)` into `negTail(sheet) + ppR(sheet)`, distribute the sum.
  have hsplit : (∑ j ∈ Finset.range S.m,
        chartIntegrand ω₀ g S.p (wp + S.ζ ^ j * S.w₀ z)
          * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
      = (∑ j ∈ Finset.range S.m,
          negTail wp S.ppb S.ppN (wp + S.ζ ^ j * S.w₀ z)
            * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
        + (∑ j ∈ Finset.range S.m,
            S.ppR (wp + S.ζ ^ j * S.w₀ z) * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [S.hpp_split_sheet z hz j hj]; ring
  rw [hsplit]
  -- The `negTail`-sheet-sum is `ramifiedTraceTerm` (the proven atom).
  have hatom : (∑ j ∈ Finset.range S.m,
        negTail wp S.ppb S.ppN (wp + S.ζ ^ j * S.w₀ z)
          * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
      = ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c z := by
    rw [show (∑ j ∈ Finset.range S.m,
          negTail wp S.ppb S.ppN (wp + S.ζ ^ j * S.w₀ z)
            * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
        = ∑ j ∈ Finset.range S.m,
          (∑ k ∈ Finset.Icc 1 S.ppN, S.ppb k * (wp + S.ζ ^ j * S.w₀ z - wp) ^ (-(k : ℤ)))
            * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z
      from Finset.sum_congr rfl (fun j _ => by rw [negTail])]
    exact ramifiedSheetSum_laurentPoly (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.hm S.hζ
      (S.hw₀_ne z hz) (S.hw₀_pow z hz) (S.hw₀_deriv z hz)
  -- The `ppR`-sheet-sum is `Rem z` (the symmetric-function descent, `hRem_slit`).
  rw [hatom, ← S.hRem_slit z hz]
  rfl

/-- The single-valued trace `T` is **meromorphic at `c`** by construction: `ramifiedTraceTerm` is the
atom's shifted Laurent term (`meromorphicAt_ramifiedTraceTerm`) and `Rem` is analytic at `c`. -/
theorem meromorphicAt_traceFull (S : RamifiedSheetData ω₀ g f Φ c) :
    MeromorphicAt S.traceFull c := by
  show MeromorphicAt
    (fun z => ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c z + S.Rem z) c
  have h : MeromorphicAt
      ((ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c) + S.Rem) c :=
    (meromorphicAt_ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c).add
      S.hRem_an.meromorphicAt
  exact h

/-- **`hcoh` (DERIVED via the identity theorem):** `valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] c] T`.  Both sides
are meromorphic at `c` (`hvct_mero` / `meromorphicAt_traceFull`) and agree on the slit
(`eqOn_traceFull_slit`), which accumulates at `c` (`hS_acc`); the identity theorem
(`eventuallyEq_of_meromorphic_eqOn_slit`) extends the slit agreement to the punctured neighbourhood.
This is where the monodromy obstruction is dodged — the branch was needed only on the slit. -/
theorem hcoh (S : RamifiedSheetData ω₀ g f Φ c) :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] c] S.traceFull :=
  eventuallyEq_of_meromorphic_eqOn_slit S.hvct_mero S.meromorphicAt_traceFull S.hS_acc
    S.eqOn_traceFull_slit

/-- **Fact (B): the residue of the single-valued trace `T` at `c` is the upstairs residue.**
`resAt T c = formFnResidue ω₀ g p`.  The residue of `ramifiedTraceTerm` is the principal part's residue
(`resAt_ramifiedTraceTerm` + the data field `hppN_res`), and `Rem` (analytic) adds `0`. -/
theorem resAt_traceFull (S : RamifiedSheetData ω₀ g f Φ c) :
    resAt S.traceFull c = formFnResidue ω₀ g S.p := by
  show resAt
    (fun z => ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c z + S.Rem z) c
    = formFnResidue ω₀ g S.p
  rw [show (fun z => ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c z
        + S.Rem z)
      = (ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c) + S.Rem from rfl,
    resAt_add
      (meromorphicAt_ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c).holoPunctured
      S.hRem_an.meromorphicAt.holoPunctured,
    resAt_eq_zero_of_analyticAt S.hRem_an, add_zero,
    resAt_ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.hm c, S.hppN_res]

end RamifiedSheetData

/-! ### The sound capstone: `RamifiedCenterFacts` from `RamifiedSheetData`

Assembling the full `RamifiedCenterFacts` at a single ramified preimage centre.  The carried trace
`T := traceFull` is the single-valued `ramifiedTraceTerm (principal part) + Rem` (NOT the multivalued
sheet sum), so `hcoh : valueChartTrace =ᶠ[𝓝[≠] c] T` is the genuine punctured germ-equality, *derived*
via the slit identity + the identity theorem; `hmero`/`hres` come from the proven atom. -/

/-- **`RamifiedCenterFacts` from a single-preimage `RamifiedSheetData`** (the SOUND ramified centre
provider).  Given the Forster §5 slit sheet data `S` at a ramification preimage `p` of multiplicity `m`
over `c`, and that `p` is the *unique* pole of `α = ω₀·g` in the fibre `F⁻¹(coe c)` (`hp_pole`,
`hp_fibre`, `hp_unique`), build the `RamifiedCenterFacts` whose carried trace `T = traceFull` is the
single-valued `ramifiedTraceTerm + Rem`.  `hcoh` is `S.hcoh` (derived via the slit + identity theorem —
TRUE, no monodromy contradiction); `hmero`/`hres` are `meromorphicAt_traceFull`/`resAt_traceFull` (the
proven atom).  **No `deriv ≠ 0`** (admits ramification); **no false/circular field**. -/
noncomputable def RamifiedCenterFacts.ofSheetData {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {poles : Finset X} {c : ℂ}
    (S : RamifiedSheetData ω₀ g f Φ c) (hp_pole : S.p ∈ poles)
    (hp_fibre : f.toRiemannSphere S.p = ((c : ℂ) : RiemannSphere))
    (hp_unique : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → a = S.p) :
    RamifiedCenterFacts ω₀ g f Φ poles c where
  D :=
    { ι := Unit
      fintype_ι := inferInstance
      xs := fun _ => S.p
      hmem := fun _ => hp_fibre
      mult := fun _ => S.m
      hmult_pos := fun _ => S.hm
      hg_mero := fun _ => S.hg_mero }
  hD_inj := fun _ _ _ => rfl
  hD_mem := fun _ => hp_pole
  hD_surj := fun a ha hfib => ⟨(), (hp_unique a ha hfib).symm⟩
  T := S.traceFull
  hcoh := S.hcoh
  hmero := S.meromorphicAt_traceFull
  hres := by
    show resAt S.traceFull c = ∑ _ : Unit, formFnResidue ω₀ g S.p
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, S.resAt_traceFull]

/-! ### Soundness sanity — the carried trace is single-valued; the slit identity recovers the geometry

The carried trace `T = traceFull` is, by construction, the **single-valued** function
`ramifiedTraceTerm (principal part) + Rem` (a meromorphic function of `z − c`), *not* the multivalued
sheet sum.  It coincides with the geometric `m`-sheet sum exactly on the slit `S`
(`eqOn_traceFull_slit`), and that slit agreement is what the identity theorem promotes to `hcoh`.  At an
*unramified* preimage (`m = 1`) the slit can be taken to be the full punctured neighbourhood and the
construction degenerates to the unramified single-section identification (witnessed at `m = 1` by
`ramifiedSheetData_zero`).  We record the single-valued definitional shape as a sanity check. -/
theorem traceFull_def {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
    {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} (S : RamifiedSheetData ω₀ g f Φ c) (z : ℂ) :
    S.traceFull z
      = ramifiedTraceTerm (Finset.Icc 1 S.ppN) S.ppb (fun k => -(k : ℤ)) S.m c z + S.Rem z := rfl

/-! ### Non-vacuity of `RamifiedSheetData` — inhabitable for **any** `m` (the monodromy fix verified)

`RamifiedSheetData`'s fields are *jointly satisfiable for every `m ≥ 1`*, so `RamifiedCenterFacts.
ofSheetData` is **not** vacuous, and — crucially — the structure is **not a disguised `False` at a
ramified centre** (the bug it replaces).  Witness: the zero numerator `g ≡ 0` (so `α = ω₀·g = 0`), the
empty fibre selection (`valueChartTrace ≡ 0`), with the genuine **slit `m`-th-root branch**
`w₀ z = (z − c)^{1/m}` (`Complex.cpow`) on the slit `S = {z | z − c ∈ slitPlane}` — which exists for
*any* `m` (the whole point of the slit).  At `m = 2` this is the genuine `√(z − c)` branch on the
slit-plane, demonstrating the structure is inhabited at a *ramified* multiplicity.  Every other field is
`0 = 0` by direct computation (`g ≡ 0`), and the branch fields are the standard `cpow` identities. -/

/-- **`RamifiedSheetData` is inhabitable for every `m ≥ 1`** (non-vacuity / soundness witness — the
monodromy fix).  For the zero numerator `g ≡ 0`, the empty fibre selection, any centre `c`, point `p`,
multiplicity `m ≥ 1`, and primitive `m`-th root `ζ`, the slit `S = {z | z − c ∈ slitPlane}` with the
`cpow` branch `w₀ z = (z − c)^{1/m}` is a valid `RamifiedSheetData`.  The branch exists on the slit for
**any** `m` (no monodromy contradiction), so the structure is inhabited at genuinely ramified
multiplicities — e.g. `m = 2`, the `√(z − c)` branch (`ramifiedSheetData_sqrt`). -/
noncomputable def ramifiedSheetData_slit (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (c : ℂ) (p : X) (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    RamifiedSheetData ω₀ (fun _ => (0 : ℂ)) f (fun b => emptyFibreRegularData (fun _ => 0) f b) c where
  p := p
  m := m
  hm := hm
  ζ := ζ
  hζ := hζ
  S := {z | z - c ∈ slitPlane}
  hS_acc := by
    -- The slit accumulates at `c`: approach along the positive imaginary axis `c + (1/(n+1))·I`.
    rw [show (fun z => z ∈ {z : ℂ | z - c ∈ slitPlane}) = (fun z => z ∈ {z : ℂ | z - c ∈ slitPlane})
      from rfl, ← accPt_iff_frequently_nhdsNE]
    have hcS : c ∉ {z : ℂ | z - c ∈ slitPlane} := by simp [mem_slitPlane_iff]
    have hcl : c ∈ closure {z : ℂ | z - c ∈ slitPlane} := by
      have htend : Tendsto (fun n : ℕ => c + ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I) atTop (𝓝 c) := by
        have h0 : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
          have hr : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have hc : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
            (Complex.continuous_ofReal.tendsto 0).comp hr
          rw [Complex.ofReal_zero] at hc
          simpa using hc.mul_const Complex.I
        simpa using (tendsto_const_nhds (x := c)).add h0
      refine mem_closure_of_tendsto htend (Filter.Eventually.of_forall (fun n => ?_))
      simp only [Set.mem_setOf_eq, add_sub_cancel_left, mem_slitPlane_iff]
      right
      have him : (((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I).im = (1 / (n + 1 : ℝ) : ℝ) := by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]; ring
      rw [him]; positivity
    rw [closure_eq_self_union_derivedSet] at hcl
    exact hcl.resolve_left hcS
  w₀ := fun z => (z - c) ^ ((m : ℂ)⁻¹)
  hw₀_ne := by
    intro z hz
    have hzc : z - c ≠ 0 := Complex.slitPlane_ne_zero hz
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hzc)
  hw₀_pow := by
    intro z _
    rw [zpow_natCast]; exact Complex.cpow_nat_inv_pow _ hm.ne'
  hw₀_deriv := by
    intro z hz
    have hmem : (z - c) ∈ slitPlane := hz
    have hzc : z - c ≠ 0 := Complex.slitPlane_ne_zero hz
    have hw0ne : (z - c) ^ ((m : ℂ)⁻¹) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hzc)
    have hpow : ((z - c) ^ ((m : ℂ)⁻¹)) ^ (m : ℤ) = z - c := by
      rw [zpow_natCast]; exact Complex.cpow_nat_inv_pow _ hm.ne'
    have hbase : HasDerivAt (fun z : ℂ => z - c) 1 z := by simpa using (hasDerivAt_id z).sub_const c
    have hD := hbase.cpow_const (c := (m : ℂ)⁻¹) hmem
    rw [mul_one] at hD
    have hderiv : deriv (fun z : ℂ => (z - c) ^ ((m : ℂ)⁻¹)) z
        = (m : ℂ)⁻¹ * (z - c) ^ ((m : ℂ)⁻¹ - 1) := hD.deriv
    rw [hderiv]; congr 1
    -- `(z−c)^(a−1) = w₀^(1−m)`: both equal `w₀·(z−c)⁻¹`.
    have hL : (z - c) ^ ((m : ℂ)⁻¹ - 1) = (z - c) ^ ((m : ℂ)⁻¹) * (z - c)⁻¹ := by
      rw [Complex.cpow_sub _ _ hzc, Complex.cpow_one, div_eq_mul_inv]
    have hR : ((z - c) ^ ((m : ℂ)⁻¹)) ^ (1 - (m : ℤ)) = (z - c) ^ ((m : ℂ)⁻¹) * (z - c)⁻¹ := by
      rw [zpow_sub₀ hw0ne, zpow_one, hpow, div_eq_mul_inv]
    rw [hL, hR]
  hg_mero := by
    show MeromorphicAt (fun z => (0 : ℂ)) ((chartAt ℂ p) p)
    exact analyticAt_const.meromorphicAt
  ppN := 0
  ppb := fun _ => 0
  ppR := fun _ => 0
  hppR_an := analyticAt_const
  hpp_split_sheet := by
    intro z _ j _
    rw [show chartIntegrand ω₀ (fun _ => (0 : ℂ)) p = (fun _ => (0 : ℂ)) by
      funext w; simp [chartIntegrand]]
    simp [negTail]
  hppN_res := by
    -- `resAt 0 0 = 0 = formFnResidue ω₀ 0 p` (`Icc 1 0 = ∅`, and chartIntegrand of `0` is `0`).
    have hrhs : formFnResidue ω₀ (fun _ => (0 : ℂ)) p = 0 := by
      rw [formFnResidue, show (fun z => coeffAt ω₀ p z * (fun _ => (0 : ℂ)) ((chartAt ℂ p).symm z))
          = (fun _ => (0 : ℂ)) by funext z; simp, resAt_zero]
    simp only [show (Finset.Icc 1 0 : Finset ℕ) = ∅ from rfl, Finset.sum_empty, resAt_zero, hrhs]
  Rem := fun _ => 0
  hRem_an := analyticAt_const
  hRem_slit := by
    intro z _
    simp
  hgeom_slit := by
    intro z _
    -- `valueChartTrace = 0` (empty selection), and the RHS is the `m`-sheet sum of `chartIntegrand 0 = 0`.
    rw [valueChartTrace_emptySelection ω₀ f,
      show chartIntegrand ω₀ (fun _ => (0 : ℂ)) p = (fun _ => (0 : ℂ)) by
        funext w; simp [chartIntegrand]]
    simp
  hvct_mero := by
    rw [valueChartTrace_emptySelection ω₀ f]
    exact analyticAt_const.meromorphicAt

/-- **`RamifiedSheetData` is inhabited at the ramified multiplicity `m = 2`** — the genuine `√(z − c)`
slit branch.  This is the decisive soundness witness: the corrected structure is satisfiable for
`m > 1` (the old `∀ᶠ in 𝓝[≠] c` branch demand was a disguised `False` here by monodromy).  Uses the
primitive square root `ζ = −1` and the `cpow` branch `√(z − c)` on the slit plane. -/
noncomputable def ramifiedSheetData_sqrt (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (c : ℂ) (p : X) :
    RamifiedSheetData ω₀ (fun _ => (0 : ℂ)) f (fun b => emptyFibreRegularData (fun _ => 0) f b) c :=
  ramifiedSheetData_slit ω₀ f c p 2 (by norm_num) (-1)
    (IsPrimitiveRoot.neg_one (R := ℂ) 0 (by norm_num))

/-- **`RamifiedSheetData` is inhabited at `m = 1`** (the unramified reduction — `ζ = 1`).  Confirms the
construction degenerates correctly; here the slit branch is `(z − c)^{1/1} = z − c`. -/
noncomputable def ramifiedSheetData_zero (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (c : ℂ) (p : X) :
    RamifiedSheetData ω₀ (fun _ => (0 : ℂ)) f (fun b => emptyFibreRegularData (fun _ => 0) f b) c :=
  ramifiedSheetData_slit ω₀ f c p 1 one_pos 1 IsPrimitiveRoot.one

/-! ### Wiring to `ExistsRamifiedCenterFacts` (the precise remaining obligation, now Forster §5 data)

`RamifiedCenterFacts.ofSheetData` reduces the per-centre obligation `ExistsRamifiedCenterFacts`
(`SerreResidueRamifiedCenter.lean`) to the precise Forster §5 normal-form *data* `RamifiedSheetData`
(at a single ramified preimage that is the unique pole in its fibre).  `residueTheorem_ofRamifiedCenters_genus0_mod`
then gives `hoff_cs`-free Gate A from per-centre `RamifiedSheetData`.  The genuine remaining analytic
content is exactly the `RamifiedSheetData` fields: the slit `m`-th-root branch `w₀`, the geometric trace
identification `hgeom_slit`, the single-valued analytic remainder trace `Rem`, and the single-valued
meromorphy `hvct_mero` — all true (Forster §5 / Miranda (3.1)), supplied as data, none asserted as a
free lemma. -/

/-- **`ExistsRamifiedCenterFacts` from a single-preimage `RamifiedSheetData`.**  Packaging the sound
constructor `RamifiedCenterFacts.ofSheetData` as the named per-centre obligation: the Forster §5 sheet
data at a ramified preimage `p` (the unique pole in the fibre `F⁻¹(coe c)`) inhabits
`ExistsRamifiedCenterFacts`.  This is the bridge that lets the `hoff_cs`-free capstone
`residueTheorem_ofRamifiedCenters_genus0_mod` consume per-centre `RamifiedSheetData`. -/
theorem existsRamifiedCenterFacts_ofSheetData {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {poles : Finset X} {c : ℂ}
    (S : RamifiedSheetData ω₀ g f Φ c) (hp_pole : S.p ∈ poles)
    (hp_fibre : f.toRiemannSphere S.p = ((c : ℂ) : RiemannSphere))
    (hp_unique : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → a = S.p) :
    ExistsRamifiedCenterFacts ω₀ g f Φ poles c :=
  ⟨RamifiedCenterFacts.ofSheetData S hp_pole hp_fibre hp_unique⟩

/-- **Gate A `∑Res = 0` (kirovGenus `0`) from per-centre Forster §5 sheet data — `hoff_cs`-FREE, end to
end.**  The cleanest fully-reduced statement: each finite pole-value centre `cs i` carries a
`RamifiedSheetData` `Sf i` (the Forster §5 `z = wᵐ` normal-form geometry) at a single ramified
preimage that is the unique pole of `α = ω₀·g` in the fibre `F⁻¹(coe (cs i))`, together with the
off-centre analyticity `hreg`/`hbnd` and the `∞`-group.  Gate A then holds with **NO** `hoff_cs` (the
finite centres may be ramified).  This composes `existsRamifiedCenterFacts_ofSheetData` (the proven
`hcoh` via the normal form + the atom) into `residueTheorem_ofRamifiedCenters_genus0_mod`.  The genuine
remaining content is *only* the per-centre `RamifiedSheetData` — the holomorphic `m`-th-root branch and
the geometric trace identification (Forster §5), supplied as data. -/
theorem residueTheorem_ofSheetData_genus0 {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {poles : Finset X}
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    -- The per-centre Forster §5 sheet data (the only genuine remaining content; admits ramification).
    (Sf : ∀ i, RamifiedSheetData ω₀ g f Φ (cs i))
    (hp_pole : ∀ i, (Sf i).p ∈ poles)
    (hp_fibre : ∀ i, f.toRiemannSphere (Sf i).p = ((cs i : ℂ) : RiemannSphere))
    (hp_unique : ∀ i, ∀ a ∈ poles, f.toRiemannSphere a = ((cs i : ℂ) : RiemannSphere) → a = (Sf i).p)
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfullInf_inj : Function.Injective Dinf_full.xs)
    {ιInfP : Type} [Fintype ιInfP] (xsInf_po : ιInfP → X)
    (hpoInf_inj : Function.Injective xsInf_po)
    (hpoInf_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpoInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image_inf : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofRamifiedCenters_genus0_mod (poles := poles) Φ m cs ρ hcs_ball hcs_inj br hreg hbnd
    hcenters_cs
    (fun i => existsRamifiedCenterFacts_ofSheetData (Sf i) (hp_pole i) (hp_fibre i) (hp_unique i))
    Dinf_full hcoh_full hfullInf_inj xsInf_po hpoInf_inj hpoInf_mem hpoInf_surj hpole_image_inf
    hnonpole_inf_an

end Jacobians.Dolbeault.SerreResidueTheorem
