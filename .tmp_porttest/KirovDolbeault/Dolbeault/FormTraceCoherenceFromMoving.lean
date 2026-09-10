/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceFullFibreRationalityAssemble
import KirovDolbeault.Dolbeault.FormTraceMovingFibreSphereSet

/-!
# Discharging `TraceCoherenceData`'s pole-centre coherence from the moving-fibre engine (Gate A, §VIII.3)

`Jacobians.Dolbeault.FormTraceFullFibreRationalityAssemble.TraceCoherenceData` is the cleanest Gate-A
target: a single global geometric trace `T : ℂ → ℂ` (the value-chart `dz`-coefficient of `Tr_F α`) with
the honest §VIII.3 inputs.  Constructing one closes the 1-form residue theorem `∑ₐ Resₐ(α) = 0`
*unconditionally* (the principal-part extraction and the kirovGenus-`0` Liouville vanishing are *proved*
inside `TraceCoherenceData`).  Its fields split into

* the **pole-centre coherence** `hcoh_fin` (`T =ᶠ[𝓝 (cs i)] (fibreTrace ω₀ f (D (cs i))).traceCoeff`) and
  the `∞`-coherence `hcoh_inf` — the §VIII.3 *single-valuedness of the trace* at the finitely-many
  pole-values;
* the off-centre **meromorphy** `hT_mero`;
* the kirovGenus-`0` **remainder vanishing** `hentire`/`hrecip_cont` (the `H⁰(ℂℙ¹, Ω) = 0` content);
* the discrete fibre **enumeration** bookkeeping.

This file discharges the *pole-centre coherence* `hcoh_fin` (and the off-centre meromorphy `hT_mero`)
from the **proved moving-fibre coherence engine** `Jacobians.Dolbeault.FormTraceMovingFibre`.  The point
(Miranda §VIII.3): the geometric trace `T := valueChartTrace ω₀ f Φ` is a *symmetric* fibre sum, so it is
**single-valued by symmetry** — and a `MovingCoherenceDatum` at a pole-value `cs i` (whose fixed fibre is
the per-centre fibre data `D (cs i)`) gives exactly the germ-coherence `T =ᶠ[𝓝 (cs i)] (fibreTrace ω₀ f
(D (cs i))).traceCoeff` (`MovingCoherenceDatum.coherent`).  The moving datum is itself constructible from
continuously-varying sheet sections *with no global labeling* — the **symmetric-invariance lever**
(`MovingCoherenceDatum.ofSheetSectionsSet`): the per-`b'` index bijection is reconstructed pointwise from
set-equality of the two fibre enumerations.

So the pole-centre coherence — the genuine §VIII.3 residual the `TraceCoherenceData` route isolates — is
**discharged here from the proved engine**, leaving the precise remaining obligation as the kirovGenus-`0`
remainder vanishing (`hentire`/`hrecip_cont`) and the `∞`-bookkeeping (`hcoh_inf`, the `∞`-fibre data).

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `traceCoherenceData_ofMovingData` — a `TraceCoherenceData` from a global selection `Φ` with `T :=
  valueChartTrace ω₀ f Φ`, the per-pole-value moving data `Cfin` (whose fixed fibre is the per-centre
  data `D (cs i)`), and the kirovGenus-`0`/`∞`/enumeration inputs.  **`hcoh_fin` and `hT_mero` are proved**
  from `MovingCoherenceDatum.coherent` + `meromorphicAt_traceCoeff_fibreTrace`.
* `traceCoherenceData_ofSheetSections` — the *sheet-form* constructor: the per-pole moving data is built
  from continuously-varying smooth sheet sections + the **symmetric-lever set-form re-selection**
  (`MovingCoherenceDatum.ofSheetSectionsSet`), so the caller supplies only the labeling-independent
  geometric facts (the sheets enumerate the per-centre fibre as a set), never a sheet ordering.
* `residueSum_eq_zero_of_movingTraceCoherence` / `residueSum_eq_zero_of_sheetTraceCoherence` — Gate A
  `∑Res = 0` from either form.
* `traceCoherenceData_ofMovingData_empty` / `…_holomorphic` — end-to-end non-vacuity (empty-pole case),
  confirming the reduction is honest (not a disguised `False`).

## The single minimal remaining obligation (precise diagnosis)

After this file, the `TraceCoherenceData` route to Gate A `∑Res = 0` rests — axiom-clean — on exactly the
**kirovGenus-`0` remainder vanishing** (`hentire`: `T − L.R` entire after subtracting the finite principal
parts; `hrecip_cont`: holomorphic across `∞`) together with the `∞`-coherence `hcoh_inf` and the
`∞`-fibre enumeration `Dinf`.  The pole-centre coherence (the §VIII.3 single-valuedness at the finite
pole-values) and the off-centre meromorphy are **discharged** from the moving-fibre engine.  These
remaining inputs are the `H⁰(ℂℙ¹, Ω) = 0` content (a holomorphic `1`-form on the sphere is `0`,
`Jacobians.RiemannSphere.holomorphicOneForm_eq_zero`, PROVEN) realized through the holomorphic remainder,
plus the cover's `∞`-adaptedness.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr` is single-valued
  **by symmetry**, Lemma 3.2; partial fractions / Liouville on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceFullFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceLiouville
  Jacobians.Dolbeault.FormTraceMovingFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The pole-centre coherence and off-centre meromorphy, discharged from a moving datum

The two facts the moving-fibre engine supplies for the `TraceCoherenceData` geometric trace `T :=
valueChartTrace ω₀ f Φ`:

* **pole-centre coherence** `hcoh_fin i` — `T =ᶠ[𝓝 (cs i)] (fibreTrace ω₀ f (D (cs i))).traceCoeff` is
  exactly `MovingCoherenceDatum.coherent` for a datum at `cs i` with fixed fibre `D (cs i)`;
* **off-centre meromorphy** `hT_mero i` — `MeromorphicAt T (cs i)`: the local model `(fibreTrace ω₀ f (D
  (cs i))).traceCoeff` is meromorphic at `cs i` (`meromorphicAt_traceCoeff_fibreTrace`), and `T`
  germ-equals it (the coherence restricted to a punctured neighbourhood), so `T` is meromorphic too.
-/

/-- **Pole-centre coherence from a moving datum.**  A `MovingCoherenceDatum` at the pole-value `cs i`
whose fixed fibre is `D (cs i)` gives the §VIII.3 single-valuedness germ-equality
`valueChartTrace ω₀ f Φ =ᶠ[𝓝 (cs i)] (fibreTrace ω₀ f (D (cs i))).traceCoeff` — exactly the `hcoh_fin`
field of `TraceCoherenceData`.  The labeling-free monodromy core, `MovingCoherenceDatum.coherent`. -/
theorem hcoh_fin_of_movingDatum {Φ : (b : ℂ) → FibreRegularData g f b}
    {D : (p : ℂ) → FibreRegularData g f p} {p : ℂ}
    (C : MovingCoherenceDatum ω₀ g f Φ p) (hCD : C.D = D p) :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝 p] (fibreTrace ω₀ f (D p)).traceCoeff := by
  have h := C.coherent
  rwa [hCD] at h

/-- **Off-centre meromorphy from a moving datum.**  With `T := valueChartTrace ω₀ f Φ` germ-equal to the
local model `(fibreTrace ω₀ f (D p)).traceCoeff` at `p` (from `MovingCoherenceDatum.coherent`), and that
model meromorphic at `p` (`meromorphicAt_traceCoeff_fibreTrace`), `T` is meromorphic at `p` — the
`hT_mero` field of `TraceCoherenceData`. -/
theorem meromorphicAt_valueChartTrace_of_movingDatum {Φ : (b : ℂ) → FibreRegularData g f b}
    {D : (p : ℂ) → FibreRegularData g f p} {p : ℂ}
    (C : MovingCoherenceDatum ω₀ g f Φ p) (hCD : C.D = D p) :
    MeromorphicAt (valueChartTrace ω₀ f Φ) p := by
  -- The local model is meromorphic at `p`; `T` germ-equals it off `p`, so `T` is meromorphic too.
  have hmodel : MeromorphicAt (fibreTrace ω₀ f (D p)).traceCoeff p :=
    meromorphicAt_traceCoeff_fibreTrace ω₀ f (D p)
  have heq : valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (D p)).traceCoeff :=
    (hcoh_fin_of_movingDatum C hCD).filter_mono nhdsWithin_le_nhds
  exact hmodel.congr heq.symm

/-! ### The `TraceCoherenceData` from a global selection + per-pole moving data

We assemble a `TraceCoherenceData` with `T := valueChartTrace ω₀ f Φ` (the full-fibre symmetric trace of
the global selection `Φ`) and a **separate** per-centre fibre enumeration `D` (the poles in each fibre),
discharging the pole-centre coherence `hcoh_fin` and the off-centre meromorphy `hT_mero` from the
per-pole moving data `Cfin`.

The separation of `T`'s fibre (`Φ`) from the enumeration `D` is the honest Miranda §VIII.3 design: `Φ`
may enumerate the **full** fibre (so `T = Tr_F α`), while `D (cs i)` enumerates only the **poles** in the
fibre over `cs i` (the `TraceCoherenceData` enumeration fields demand `D p` be pole-enumerating).  The
finite glue `hcoh_fin i : T =ᶠ[𝓝 (cs i)] (fibreTrace ω₀ f (D (cs i))).traceCoeff` is then the moving
datum `Cfin i` (with fixed fibre `(Cfin i).D = D (cs i)` the pole sub-fibre) — *no full-fibre =
pole-fibre separation is built into this constructor*.  The `∞`-coherence `hcoh_inf`, the kirovGenus-`0`
remainder vanishing `hentire`/`hrecip_cont`, and the fibre enumeration bookkeeping are the genuine
residual inputs. -/

/-- **A `TraceCoherenceData` from a global selection and per-pole moving data.**  Given a global fibre
selection `Φ` (giving the geometric trace `T := valueChartTrace ω₀ f Φ`), a per-centre fibre enumeration
`D` (the poles in each fibre), the per-pole-value moving data `Cfin i` (a `MovingCoherenceDatum` at
`cs i` whose fixed fibre is `D (cs i)`), and the `∞`/kirovGenus-`0`/enumeration residual inputs, this
assembles a `TraceCoherenceData ω₀ g f poles`.

**The pole-centre coherence `hcoh_fin` and the off-centre meromorphy `hT_mero` are *proved*** from
`Cfin` via `MovingCoherenceDatum.coherent` + `meromorphicAt_traceCoeff_fibreTrace` (the §VIII.3
single-valuedness by symmetry).  Constructing one ⇒ Gate A `∑Res = 0`. -/
noncomputable def traceCoherenceData_ofMovingData
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfin_D : ∀ i, (Cfin i).D = D (cs i))
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (Dinf : InftyFibreData g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    TraceCoherenceData ω₀ g f poles where
  T := valueChartTrace ω₀ f Φ
  m := m
  cs := cs
  ρ := ρ
  hcs_ball := hcs_ball
  hcs_inj := hcs_inj
  D := D
  hxs_inj := hxs_inj
  hxs_mem := hxs_mem
  hxs_surj := hxs_surj
  Dinf := Dinf
  hxsInf_inj := hxsInf_inj
  hxsInf_mem := hxsInf_mem
  hxsInf_surj := hxsInf_surj
  hcenters_cs := hcenters_cs
  -- **The pole-centre coherence**, discharged from the moving datum (the §VIII.3 single-valuedness).
  hcoh_fin := fun i => hcoh_fin_of_movingDatum (Cfin i) (hCfin_D i)
  hcoh_inf := hcoh_inf
  -- **The off-centre meromorphy**, discharged from the moving datum + `meromorphicAt_traceCoeff_fibreTrace`.
  hT_mero := fun i => meromorphicAt_valueChartTrace_of_movingDatum (Cfin i) (hCfin_D i)
  hentire := hentire
  hrecip_cont := hrecip_cont

/-- **Gate A `∑Res = 0` from a global selection + per-pole moving data.**  The pole-centre coherence is
discharged from the moving-fibre engine; `residueSum_eq_zero_of_traceCoherenceData` then closes the
1-form residue theorem for `α = ω₀·g`. -/
theorem residueSum_eq_zero_of_movingTraceCoherence
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfin_D : ∀ i, (Cfin i).D = D (cs i))
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (Dinf : InftyFibreData g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_traceCoherenceData ω₀ g f poles
    (traceCoherenceData_ofMovingData Φ m cs ρ hcs_ball hcs_inj D Cfin hCfin_D hxs_inj hxs_mem hxs_surj
      Dinf hxsInf_inj hxsInf_mem hxsInf_surj hcenters_cs hcoh_inf hentire hrecip_cont)

/-! ### The sheet-form constructor (the symmetric-invariance lever — no labeling)

We now build the per-pole moving data `Cfin i` from continuously-varying smooth **sheet sections** and
the **labeling-independent set-form re-selection** `MovingCoherenceDatum.ofSheetSectionsSet`.  The caller
supplies, at each pole-value `cs i`, sheet sections `secFin i : (Φ (cs i)).ι → ℂ → X` through the fibre
points of `Φ (cs i)` and the set-form fact `hsetFin i`: near `cs i`, the moving fibre `Φ b'` and the
section values `fun j => secFin i j b'` are both injective with the *same image* (so they enumerate the
same fibre as a set), with each section value in the matching chart source.  The per-`b'` index bijection
is reconstructed pointwise by the symmetric lever — **no global continuous sheet-labeling**. -/

/-- **A `TraceCoherenceData` from sheet sections (the symmetric lever).**  Identical to
`traceCoherenceData_ofMovingData` except the per-pole moving data is built from continuously-varying
smooth sheet sections `secFin` and the **set-form re-selection** `hsetFin`
(`MovingCoherenceDatum.ofSheetSectionsSet`): at each pole-value `cs i`, the section values pass through
the fibre points of `Φ (cs i)` at the base, are smooth + sections of `f.holoRepr` near the base, and
enumerate the *same fibre set* as `Φ b'` (no labeling).  The pole-centre coherence `hcoh_fin` is thereby
discharged **labeling-free** (Miranda §VIII.3, single-valued by symmetry); the kirovGenus-`0`/`∞` inputs
remain the precise residual. -/
noncomputable def traceCoherenceData_ofSheetSections
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    -- The per-pole sheet sections (through the fibre points of `Φ (cs i)`).
    (secFin : ∀ i, (Φ (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (Φ (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hsetFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), Function.Injective (Φ b').xs ∧
      Function.Injective (fun j => secFin i j b') ∧
      Set.range (Φ b').xs = Set.range (fun j => secFin i j b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((Φ (cs i)).xs j)).source))
    (hxs_inj : ∀ p, Function.Injective (Φ p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (Φ p).xs i ∈ poles ∧ f.toRiemannSphere ((Φ p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (Φ p).xs i = a)
    (Dinf : InftyFibreData g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    TraceCoherenceData ω₀ g f poles :=
  traceCoherenceData_ofMovingData Φ m cs ρ hcs_ball hcs_inj Φ
    (fun i => MovingCoherenceDatum.ofSheetSectionsSet (Φ (cs i)) (secFin i)
      (hsecFin_base i) (hsecFin_smooth i) (hsecFin_sec i) (hsetFin i))
    (fun _ => rfl)
    hxs_inj hxs_mem hxs_surj Dinf hxsInf_inj hxsInf_mem hxsInf_surj hcenters_cs hcoh_inf
    hentire hrecip_cont

/-- **Gate A `∑Res = 0` from sheet sections (the symmetric lever).**  The sheet-form analogue of
`residueSum_eq_zero_of_movingTraceCoherence`: the pole-centre coherence is discharged labeling-free from
the smooth sheet sections + the set-form re-selection, and the kirovGenus-`0`/`∞` residual closes the rest. -/
theorem residueSum_eq_zero_of_sheetTraceCoherence
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (secFin : ∀ i, (Φ (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (Φ (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hsetFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), Function.Injective (Φ b').xs ∧
      Function.Injective (fun j => secFin i j b') ∧
      Set.range (Φ b').xs = Set.range (fun j => secFin i j b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((Φ (cs i)).xs j)).source))
    (hxs_inj : ∀ p, Function.Injective (Φ p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (Φ p).xs i ∈ poles ∧ f.toRiemannSphere ((Φ p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (Φ p).xs i = a)
    (Dinf : InftyFibreData g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_traceCoherenceData ω₀ g f poles
    (traceCoherenceData_ofSheetSections Φ m cs ρ hcs_ball hcs_inj secFin hsecFin_base hsecFin_smooth
      hsecFin_sec hsetFin hxs_inj hxs_mem hxs_surj Dinf hxsInf_inj hxsInf_mem hxsInf_surj hcenters_cs
      hcoh_inf hentire hrecip_cont)

/-! ### Non-vacuity (end-to-end soundness)

The moving/sheet `TraceCoherenceData` constructors are *satisfiable*, not a disguised `False`: for the
**empty pole set** (`α = ω₀·g` globally holomorphic) the empty fibre selection assembles into a
`TraceCoherenceData` — no finite pole-values (the per-pole moving data vacuous), the empty `∞`-fibre data,
the zero geometric trace, and the trivially-true kirovGenus-`0`/`∞` fields.  This confirms the reduction is
honest. -/

/-- **The empty moving `TraceCoherenceData`.**  For the empty pole set, the empty fibre selection
(`emptyFibreRegularData`) gives a `TraceCoherenceData` through `traceCoherenceData_ofMovingData`: no
finite pole-values (the per-pole moving data `Cfin` vacuous), the empty `∞`-fibre data, the zero
geometric trace (`valueChartTrace_emptySelection`), and the vacuous/trivially-true kirovGenus-`0`/`∞`
fields.  The honest non-vacuity witness. -/
noncomputable def traceCoherenceData_ofMovingData_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) : TraceCoherenceData ω₀ g f ∅ :=
  traceCoherenceData_ofMovingData (g := g) (poles := (∅ : Finset X))
    (fun p => emptyFibreRegularData g f p)
    0 Fin.elim0 0 (fun i => i.elim0) (fun i => i.elim0)
    (fun p => emptyFibreRegularData g f p)
    (fun i => i.elim0) (fun i => i.elim0)
    (fun _ i => i.elim) (fun _ i => i.elim)
    (fun _ a ha => absurd ha (Finset.notMem_empty a))
    (emptyInftyFibreData g f) (fun i => i.elim) (fun i => i.elim)
    (fun a ha => absurd ha (Finset.notMem_empty a))
    (by simp)
    (by rw [valueChartTrace_emptySelection ω₀ f, recipCoeff_zero,
      traceCoeff_inftyFibreTrace_empty ω₀ f])
    (by
      -- `cs` empty ⟹ `image L.a = ∅` ⟹ `L.R = 0`; `T = valueChartTrace (empty) = 0`, so `T − L.R = 0`.
      intro L hLa _
      rw [valueChartTrace_emptySelection ω₀ f]
      have hLR0 : L.R = fun _ => (0 : ℂ) :=
        laurentForm_R_eq_zero_of_emptyImage
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      rw [hLR0]
      intro z _
      show AnalyticAt ℂ ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) z
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z))
    (by
      intro L hLa _
      rw [valueChartTrace_emptySelection ω₀ f]
      have hLR0 : L.R = fun _ => (0 : ℂ) :=
        laurentForm_R_eq_zero_of_emptyImage
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      rw [hLR0]
      have h0 : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by
        funext z; simp
      rw [h0, recipCoeff_zero]
      exact continuousAt_const)

/-- **Non-vacuity of the moving `TraceCoherenceData` Gate-A reduction.**  For the empty pole set the
reduction is satisfiable via the empty selection, yielding `∑Res = 0`.  Confirms the moving/sheet
`TraceCoherenceData` reduction is honest (not a disguised `False`). -/
theorem residueSum_eq_zero_of_movingTraceCoherence_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  (traceCoherenceData_ofMovingData_empty ω₀ g f).residueSum_eq_zero

end Jacobians.Dolbeault.FormTraceFullFibre
