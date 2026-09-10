/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceMovingFibreSphereSet
import KirovDolbeault.Dolbeault.FormTraceBranchExtension

/-!
# The branch-aware trace selection (Gate A, §VIII.3 — symmetric lever + removable singularity)

This file assembles the two new structural ingredients into the **cleanest honest reduction** of Gate A
`∑Res = 0` to the genuine §VIII.3 geometry, *with no false global-labeling constraint and with branch
values handled by Riemann's removable singularity*:

1. **The symmetric-invariance lever** (`FormTraceMovingFibreSymm` / `…SphereSet`): the moving-fibre
   self-coherence needs only the *labeling-independent* fact that the moving fibre `Φ b'` enumerates the
   same fibre set as the local sheets; the per-`b'` index bijection is reconstructed pointwise.

2. **The branch extension** (`FormTraceBranchExtension`): the off-centre analyticity `hT_off` holds at
   the finitely-many branch values by Riemann's removable singularity (analytic on a punctured
   neighbourhood + continuous at the branch point), *without* a sheet system there.

The result is `BranchAwareTraceSelection` — a Gate-A input whose fields are exactly the genuine
geometry:
* the per-pole-value and per-regular-value moving-sheet *coherence data* `Cfin`/`Creg` (built upstream
  from the set-form sphere-sheet constructor, *no labeling*);
* the regular-value `g`-analyticity (so the coherence gives analyticity at regular values);
* the finitely-many branch values `br` and the **continuity of the trace at each** (the only
  branch-specific input — Riemann extension);
* the `∞`-glue, junk-freeness, and the kirovGenus-`0` `∞`-vanishing.

It produces Gate A `∑Res = 0` via the proved `residueSum_eq_zero_of_glue` (the low-level descent whose
off-centre requirement is *analyticity*, exactly what the branch extension supplies — `CoherentTraceSelection`
would instead demand germ-coherence at branch values, which is false there).

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `BranchAwareTraceSelection` — the Gate-A input bundling the moving-sheet coherence (no labeling), the
  regular-value `g`-analyticity, the branch-value continuity, and the `∞`/junk/kirovGenus-`0` data.
* `residueSum_eq_zero_of_branchAwareSelection` — Gate A `∑Res = 0` from it.
* `branchAwareTraceSelection_empty` / `residueSum_eq_zero_of_branchAwareSelection_holomorphic` —
  end-to-end non-vacuity (empty-pole case), confirming the reduction is honest.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr` is single-valued by
  *symmetry* and extends across branch points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceMovingFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceGlobal
  Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### Regular-value analyticity from the moving-sheet coherence

At a regular value `z` off the centres and off the branch values, a moving-sheet coherence datum
`Creg z` (with `g`'s chart-pullback analytic at its fibre points) gives `valueChartTrace` analytic at
`z`: the datum's self-coherence `valueChartTrace =ᶠ[𝓝 z] (fibreTrace ω₀ f (Creg z).D).traceCoeff`
(`MovingCoherenceDatum.coherent`) feeds `analyticAt_valueChartTrace_of_eventuallyEq`.  This is the
regular-value half of `hT_off`, supplied by the symmetric-lever coherence (no labeling). -/

/-- **Regular-value analyticity from a moving-sheet coherence datum.**  A `MovingCoherenceDatum` at a
regular value `z` whose fixed fibre `C.D` has `g`'s chart-pullback analytic at each fibre point gives
`AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z` — via the datum's self-coherence
(`MovingCoherenceDatum.coherent`) and `analyticAt_valueChartTrace_of_eventuallyEq`. -/
theorem analyticAt_valueChartTrace_of_movingDatum {Φ : (b : ℂ) → FibreRegularData g f b} {z : ℂ}
    (C : MovingCoherenceDatum ω₀ g f Φ z)
    (hg : ∀ i, AnalyticAt ℂ (fun w => g ((chartAt ℂ (C.D.xs i)).symm w))
      ((chartAt ℂ (C.D.xs i)) (C.D.xs i))) :
    AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z :=
  analyticAt_valueChartTrace_of_eventuallyEq ω₀ f Φ C.D hg C.coherent

/-! ### The branch-aware trace selection

The Gate-A input bundling the genuine §VIII.3 geometry, *no labeling, branch values via removable
singularity*.  Mirrors `MovingCoherenceFamily` for the finite/∞ bookkeeping and the pole-value
coherence, but:
* the off-exceptional content is split: a moving-sheet coherence datum `Creg z` (with `g`-analyticity)
  at every value off `centres ∪ br`, and the *continuity* `hbranch` at the finitely-many branch values
  `br` (the Riemann-extension input);
* `hT_off` is then `analyticAt_valueChartTrace_off_centres` — regular values via the coherence,
  branch values via the extension. -/

/-- **A branch-aware trace selection** for `α = ω₀·g` over `poles`, relative to an adapted cover `hac`.
The honest §VIII.3 Gate-A input *without the false global-labeling constraint and with branch values
handled by Riemann's removable singularity*:

* `Φ`, `cs`/`ρ`/`hcenters_cs`, `Dinf`/`hxs_*` — the global selection + finite/∞ enumeration (verbatim);
* `Cfin i` (with `hCfin_D : (Cfin i).D = fibreReg hac (cs i)`) — the per-pole-value moving-sheet
  coherence datum (built upstream from the set-form sphere-sheet constructor, *no labeling*);
* `br : Finset ℂ` — the finite branch values;
* `Creg z` (for `z ∉ cs ∪ br`) + `hCreg_g` — the per-regular-value moving-sheet coherence datum with
  `g`'s chart-pullback analytic at its fibre points (giving regular-value analyticity);
* `hbranch` — the trace is *continuous* at each branch value off the centres (the Riemann-extension
  input; the only branch-specific content);
* `hglue_inf` / `hcont_int` / `R₀`+`hR₀_*` — the `∞`-glue, junk-freeness, kirovGenus-`0` `∞`-vanishing.

Produces Gate A `∑Res = 0` via `residueSum_eq_zero_of_glue`. -/
structure BranchAwareTraceSelection (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X) (hac : AdaptedCover ω₀ g f poles) where
  /-- The global fibre selection. -/
  Φ : (b : ℂ) → FibreRegularData g f b
  /-- The number of finite pole-values. -/
  m : ℕ
  /-- The finite pole-values (the `L`-centres). -/
  cs : Fin m → ℂ
  /-- A radius bounding the finite pole-values. -/
  ρ : ℝ
  /-- The finite pole-values lie inside `ball 0 ρ`. -/
  hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ
  /-- The finite pole-values are distinct. -/
  hcs_inj : Function.Injective cs
  /-- The finite pole-values, mapped to the sphere, are exactly the finite-value pole images. -/
  hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- The `∞`-fibre regularity data. -/
  Dinf : InftyFibreData g f
  /-- The `∞`-fibre enumeration is injective. -/
  hxs_inj : Function.Injective Dinf.xs
  /-- Each `∞`-fibre point is a pole mapping to `∞`. -/
  hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty
  /-- The `∞`-fibre enumeration is surjective onto the `∞` fibre. -/
  hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a
  /-- **Per-pole-value moving-sheet coherence datum** (fixed fibre = the pole sub-fibre). -/
  Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i)
  /-- The per-pole datum's fixed fibre is the pole sub-fibre (the honest pole/regular separation). -/
  hCfin_D : ∀ i, (Cfin i).D = fibreReg hac (cs i)
  /-- **The finite branch values** of the cover (off the centres). -/
  br : Finset ℂ
  /-- **Per-regular-value moving-sheet coherence datum** off `cs ∪ br`. -/
  Creg : ∀ z, z ∉ Finset.univ.image cs ∪ br → MovingCoherenceDatum ω₀ g f Φ z
  /-- `g`'s chart-pullback is analytic at each fibre point of the regular datum. -/
  hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
    AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Creg z hz).D.xs i)).symm w))
      ((chartAt ℂ ((Creg z hz).D.xs i)) ((Creg z hz).D.xs i))
  /-- **Branch-value continuity** (the Riemann-extension input): the trace is continuous at each branch
  value off the centres. -/
  hbranch : ∀ z ∈ br, z ∉ Finset.univ.image cs → ContinuousAt (valueChartTrace ω₀ f Φ) z
  /-- **`∞` glue.** The reciprocal coefficient germ-equals the `∞`-fibre trace off `0`. -/
  hglue_inf : recipCoeff (valueChartTrace ω₀ f Φ)
    =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff
  /-- **Junk-freeness.** The remainder is continuous at each centre. -/
  hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
      (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
    ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTrace ω₀ f Φ - L.R) p
  /-- The kirovGenus-`0` analytic continuation of the reciprocal remainder. -/
  R₀ : ℂ → ℂ
  /-- `R₀` is analytic at `0`. -/
  hR₀_an : AnalyticAt ℂ R₀ 0
  /-- **Genus-`0` `∞`-vanishing.** `R₀` vanishes at `0`. -/
  hR₀0 : R₀ 0 = 0
  /-- The reciprocal remainder germ-equals `R₀` off `0`. -/
  hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    recipCoeff (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] 0] R₀

/-- **The finite glue of a branch-aware selection** (from the per-pole moving datum + pole sub-fibre).
`valueChartTrace =ᶠ[𝓝[≠] cs i] (fibreTrace ω₀ f (fibreReg hac (cs i))).traceCoeff`. -/
theorem BranchAwareTraceSelection.glue_fin {hac : AdaptedCover ω₀ g f poles}
    (S : BranchAwareTraceSelection ω₀ g f poles hac) (i : Fin S.m) :
    valueChartTrace ω₀ f S.Φ
      =ᶠ[𝓝[≠] S.cs i] (fibreTrace ω₀ f (fibreReg hac (S.cs i))).traceCoeff := by
  have h := (S.Cfin i).coherent_punctured
  rw [S.hCfin_D i] at h
  exact h

/-- **The off-centre analyticity of a branch-aware selection** (regular ⊕ branch).  At every value off
the centres `z ∉ cs`, `valueChartTrace` is analytic: regular values (off `cs ∪ br`) via the moving-sheet
coherence datum (`analyticAt_valueChartTrace_of_movingDatum`), branch values `z ∈ br` via the
removable-singularity extension (`analyticAt_valueChartTrace_off_centres`). -/
theorem BranchAwareTraceSelection.hT_off {hac : AdaptedCover ω₀ g f poles}
    (S : BranchAwareTraceSelection ω₀ g f poles hac) {z : ℂ}
    (hz : z ∉ Finset.univ.image S.cs) :
    AnalyticAt ℂ (valueChartTrace ω₀ f S.Φ) z := by
  refine analyticAt_valueChartTrace_off_centres ω₀ f S.Φ (Finset.univ.image S.cs) S.br
    (fun w hw => analyticAt_valueChartTrace_of_movingDatum (S.Creg w hw) (S.hCreg_g w hw))
    S.hbranch hz

/-- **Gate A `∑Res = 0` from a branch-aware trace selection.**  Via `residueSum_eq_zero_of_glue` (the
low-level descent whose off-centre requirement is *analyticity*, supplied by the branch extension), with
the finite glue from the per-pole moving datum, the off-centre analyticity from the regular-value
coherence ⊕ branch extension, and the `∞`/junk/kirovGenus-`0` data.  This is the §VIII.3 reduction of Gate A
**with the symmetric lever (no labeling) and branch values via removable singularity**. -/
theorem residueSum_eq_zero_of_branchAwareSelection (hac : AdaptedCover ω₀ g f poles)
    (S : BranchAwareTraceSelection ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_glue hac (valueChartTrace ω₀ f S.Φ) S.cs S.ρ S.hcs_ball S.hcs_inj
    S.hcenters_cs S.Dinf S.hxs_inj S.hxs_mem S.hxs_surj S.glue_fin S.hglue_inf
    (fun _ hz => S.hT_off hz) S.hcont_int S.R₀ S.hR₀_an S.hR₀0 S.hR₀_eq

/-! ### Non-vacuity of the branch-aware selection (end-to-end soundness)

For the **empty pole set** the empty fibre selection assembles into a `BranchAwareTraceSelection`: no
finite pole-values (per-pole fields vacuous), no branch values (`br = ∅`, `Creg`/`hbranch` vacuous over
`cs ∪ ∅`), the empty `∞`-trace, vacuous junk-freeness, and the vanishing kirovGenus-`0` continuation.
Confirms the reduction is honest. -/

/-- **The empty branch-aware trace selection.**  For the empty pole set, the empty fibre selection
assembles into a `BranchAwareTraceSelection`: per-regular-value empty moving datum
(`movingCoherenceDatum_empty`, `valueChartTrace ≡ 0`), `br = ∅`, vacuous finite/branch fields, and the
vanishing kirovGenus-`0` continuation.  The honest non-vacuity witness. -/
noncomputable def branchAwareTraceSelection_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    BranchAwareTraceSelection ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
  Φ := fun p => emptyFibreRegularData g f p
  m := 0
  cs := Fin.elim0
  ρ := 0
  hcs_ball := fun i => i.elim0
  hcs_inj := fun i => i.elim0
  hcenters_cs := by simp
  Dinf := emptyInftyFibreData g f
  hxs_inj := fun i => i.elim
  hxs_mem := fun i => i.elim
  hxs_surj := fun a ha _ => absurd ha (Finset.notMem_empty a)
  Cfin := fun i => i.elim0
  hCfin_D := fun i => i.elim0
  br := ∅
  Creg := fun z _ => movingCoherenceDatum_empty ω₀ g f z
  hCreg_g := fun z _ i => i.elim
  hbranch := fun z hz _ => absurd hz (Finset.notMem_empty z)
  hglue_inf := by
    rw [valueChartTrace_emptySelection ω₀ f, inftyFibreTrace_emptyData_traceCoeff ω₀ f,
      recipCoeff_zero]
  hcont_int := by
    intro L hLa _ p hp
    rw [hLa, Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0))] at hp
    exact absurd hp (Finset.notMem_empty p)
  R₀ := fun _ => 0
  hR₀_an := analyticAt_const
  hR₀0 := rfl
  hR₀_eq := by
    intro L hLa
    rw [valueChartTrace_emptySelection ω₀ f]
    have hLR0 : L.R = fun _ => (0 : ℂ) := by
      have hempty : (Finset.univ : Finset L.ι) = ∅ :=
        Finset.image_eq_empty.mp
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      funext z
      show (∑ p : L.ι, L.c p * (z - L.a p) ^ L.n p) = 0
      rw [hempty, Finset.sum_empty]
    rw [hLR0]
    filter_upwards with ζ
    show recipCoeff ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) ζ = (0 : ℂ)
    simp [recipCoeff]

/-- **Non-vacuity of the branch-aware Gate-A reduction.**  For the empty pole set the reduction
`residueSum_eq_zero_of_branchAwareSelection` is satisfiable via the empty selection
(`branchAwareTraceSelection_empty`), yielding `∑Res = 0`.  Confirms the reduction is honest (not a
disguised `False`). -/
theorem residueSum_eq_zero_of_branchAwareSelection_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_branchAwareSelection (adaptedCover_empty ω₀ g f hdiv)
    (branchAwareTraceSelection_empty ω₀ g f hdiv)

end Jacobians.Dolbeault.FormTraceMovingFibre
