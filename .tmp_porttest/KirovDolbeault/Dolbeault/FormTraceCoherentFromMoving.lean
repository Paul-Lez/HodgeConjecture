/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceMovingFibre

/-!
# Building `CoherentTraceSelection` from the moving-fibre self-coherence (Gate A, §VIII.3)

`Jacobians.Dolbeault.FormTraceMovingFibre` proved the monodromy heart: a `MovingCoherenceDatum` at a
base value `b₀` yields the **local self-coherence** `valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀] (fibreTrace ω₀
f D).traceCoeff` of the geometric trace with a *fixed* fibre — and that datum is now constructible from
the irreducible monodromy core (the continuously-varying index bijection, `MovingCoherenceDatum.ofBijection`).

This file **assembles** those local self-coherences into the global `CoherentTraceSelection` obligation
of `Jacobians.Dolbeault.FormTraceCoherentSelection`, which (by the proved
`residueSum_eq_zero_of_coherentSelection`) turns the key on Gate A `∑Res = 0`.  The packaging makes the
remaining geometry explicit and *minimal*:

* the **finite glue** `hglue_fin i` is exactly the local self-coherence at the pole-value `cs i` with the
  fixed fibre the **pole sub-fibre** `fibreReg hac (cs i)` (honest soundness: NOT the full fibre — the
  pole/regular separation is folded into the selection `Φ`, encoded by the index bijection at `cs i`);
* the **off-exceptional coherence** `hreg z` is the local self-coherence at a regular value `z` with a
  regular fibre `Dreg z` (with `g`'s chart-pullback analytic at each fibre point);
* the **`∞` glue** `hglue_inf` is the reciprocal-chart analogue (the `∞`-fibre trace);
* the **kirovGenus-`0` `∞`-vanishing** `R₀ 0 = 0` is `coeffAt_eq_zero_of_sphereForm` (`H⁰(ℂℙ¹, Ω) = 0`).

We bundle these as a `MovingCoherenceFamily` and prove it produces a `CoherentTraceSelection`, hence Gate
A `∑Res = 0` *unconditionally* (modulo the family's existence).  This isolates the remaining work to a
single structure whose fields are, individually, either proved (the per-value local self-coherence from
`MovingCoherenceDatum`, the kirovGenus-`0` vanishing) or the precise residual (the `∞`-glue + junk-freeness +
the family-existence = the continuously-varying index bijections + the pole/regular separation
genericity).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
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

/-! ### The finite/regular glue from moving-fibre data

The finite glue `hglue_fin i` and the off-exceptional coherence `hreg z` of `CoherentTraceSelection` are
*exactly* the punctured/full self-coherence `MovingCoherenceDatum.coherent_punctured`/`.coherent` with
the appropriate fixed fibre.  We record the two specializations: the finite glue against the **pole
sub-fibre** `fibreReg hac (cs i)`, and the regular glue against a regular fibre `Dreg`. -/

/-- **Finite glue from a moving datum at a pole-value.**  A `MovingCoherenceDatum` at `cs i` whose fixed
fibre is the pole sub-fibre `fibreReg hac (cs i)` gives the finite glue
`valueChartTrace =ᶠ[𝓝[≠] cs i] (fibreTrace ω₀ f (fibreReg hac (cs i))).traceCoeff` directly.  This is
the honest pole-sub-fibre glue (the `Φ`-encoded separation lives in the datum's index bijection at
`cs i`). -/
theorem glue_fin_of_movingDatum {Φ : (b : ℂ) → FibreRegularData g f b} {hac : AdaptedCover ω₀ g f poles}
    {cs : ℂ} (C : MovingCoherenceDatum ω₀ g f Φ cs) (hCD : C.D = fibreReg hac cs) :
    valueChartTrace ω₀ f Φ
      =ᶠ[𝓝[≠] cs] (fibreTrace ω₀ f (fibreReg hac cs)).traceCoeff := by
  have h := C.coherent_punctured
  rw [hCD] at h
  exact h

/-- **Off-exceptional coherence from a moving datum at a regular value.**  A `MovingCoherenceDatum` at a
regular value `z` whose fixed fibre `C.D` has `g`'s chart-pullback analytic at each fibre point gives the
`hreg`-witness: the regular fibre `C.D` with the full-neighbourhood coherence
`valueChartTrace =ᶠ[𝓝 z] (fibreTrace ω₀ f C.D).traceCoeff`. -/
theorem hreg_of_movingDatum {Φ : (b : ℂ) → FibreRegularData g f b} {z : ℂ}
    (C : MovingCoherenceDatum ω₀ g f Φ z)
    (hg : ∀ i, AnalyticAt ℂ (fun w => g ((chartAt ℂ (C.D.xs i)).symm w))
      ((chartAt ℂ (C.D.xs i)) (C.D.xs i))) :
    ∃ Dreg : FibreRegularData g f z,
      (∀ i, AnalyticAt ℂ (fun w => g ((chartAt ℂ (Dreg.xs i)).symm w))
        ((chartAt ℂ (Dreg.xs i)) (Dreg.xs i))) ∧
      valueChartTrace ω₀ f Φ =ᶠ[𝓝 z] (fibreTrace ω₀ f Dreg).traceCoeff :=
  ⟨C.D, hg, C.coherent⟩

/-! ### The moving-fibre coherence family — the assembled Gate-A input

We bundle: the global selection `Φ`, the adapted-cover finite/∞ bookkeeping (verbatim from
`CoherentTraceSelection`), the **per-pole-value moving data** (whose fixed fibre is the pole sub-fibre),
the **per-regular-value moving data** (regular fibre + `g`-analyticity), the `∞`-glue, junk-freeness, and
the kirovGenus-`0` continuation.  The finite glue and off-exceptional coherence are then *derived* from the
moving data (`glue_fin_of_movingDatum`/`hreg_of_movingDatum`); the rest is carried verbatim. -/

/-- **A moving-fibre coherence family** for `α = ω₀·g` over `poles`, relative to an adapted cover `hac`.
The Gate-A input assembled from the §VIII.3 monodromy data: the global selection `Φ`, the finite/∞
enumeration bookkeeping, the per-value moving-fibre self-coherence data (finite pole-values against the
pole sub-fibre, regular values against a regular fibre), the `∞`-glue, junk-freeness, and the kirovGenus-`0`
continuation.  Produces a `CoherentTraceSelection` (hence Gate A `∑Res = 0`). -/
structure MovingCoherenceFamily (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (poles : Finset X) (hac : AdaptedCover ω₀ g f poles) where
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
  /-- **Per-pole-value moving datum** (fixed fibre = the pole sub-fibre `fibreReg hac (cs i)`). -/
  Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i)
  /-- The per-pole datum's fixed fibre is the pole sub-fibre (the honest pole/regular separation). -/
  hCfin_D : ∀ i, (Cfin i).D = fibreReg hac (cs i)
  /-- **Per-regular-value moving datum** off the centres. -/
  Creg : ∀ z, z ∉ Finset.univ.image cs → MovingCoherenceDatum ω₀ g f Φ z
  /-- `g`'s chart-pullback is analytic at each fibre point of the regular datum. -/
  hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs), ∀ i,
    AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Creg z hz).D.xs i)).symm w))
      ((chartAt ℂ ((Creg z hz).D.xs i)) ((Creg z hz).D.xs i))
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

/-- **A moving-fibre coherence family yields a coherent trace selection.**  The finite glue and
off-exceptional coherence are derived from the per-value moving data (`glue_fin_of_movingDatum`,
`hreg_of_movingDatum` — the proved §VIII.3 self-coherence); the remaining fields carry over verbatim. -/
noncomputable def MovingCoherenceFamily.toCoherentTraceSelection {hac : AdaptedCover ω₀ g f poles}
    (F : MovingCoherenceFamily ω₀ g f poles hac) :
    CoherentTraceSelection ω₀ g f poles hac where
  Φ := F.Φ
  m := F.m
  cs := F.cs
  ρ := F.ρ
  hcs_ball := F.hcs_ball
  hcs_inj := F.hcs_inj
  hcenters_cs := F.hcenters_cs
  Dinf := F.Dinf
  hxs_inj := F.hxs_inj
  hxs_mem := F.hxs_mem
  hxs_surj := F.hxs_surj
  hglue_fin := fun i => glue_fin_of_movingDatum (F.Cfin i) (F.hCfin_D i)
  hglue_inf := F.hglue_inf
  hreg := fun z hz => hreg_of_movingDatum (F.Creg z hz) (F.hCreg_g z hz)
  hcont_int := F.hcont_int
  R₀ := F.R₀
  hR₀_an := F.hR₀_an
  hR₀0 := F.hR₀0
  hR₀_eq := F.hR₀_eq

/-- **Gate A `∑Res = 0` from a moving-fibre coherence family.**  Via
`MovingCoherenceFamily.toCoherentTraceSelection` and the proved
`residueSum_eq_zero_of_coherentSelection`, a moving-fibre coherence family closes Gate A's 1-form
residue theorem for `α = ω₀·g`.  This is the §VIII.3-monodromy reduction of Gate A: every field is
either proved (the per-value self-coherence, the kirovGenus-`0` vanishing) or the precise residual (the
`∞`-glue, junk-freeness, and the family-existence = the continuously-varying index bijections + the
pole/regular separation genericity). -/
theorem residueSum_eq_zero_of_movingCoherenceFamily (hac : AdaptedCover ω₀ g f poles)
    (F : MovingCoherenceFamily ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_coherentSelection hac F.toCoherentTraceSelection

/-! ### Non-vacuity of the moving-fibre coherence family (end-to-end soundness)

The `MovingCoherenceFamily` obligation is *satisfiable*, not a disguised `False`: for the **empty pole
set** (`α = ω₀·g` globally holomorphic) the empty fibre selection gives a family — the per-regular-value
data is the empty datum (`movingCoherenceDatum_empty`, `valueChartTrace ≡ 0`), no finite pole-values, the
empty `∞`-trace (`recipCoeff 0 ≡ 0`), vacuous junk-freeness, and the vanishing kirovGenus-`0` continuation.
This confirms the family produces a genuine `∑Res = 0`, mirroring `coherentTraceSelection_empty`. -/

/-- **The empty moving coherence family.**  For the empty pole set, the empty fibre selection assembles
into a `MovingCoherenceFamily`: per-regular-value empty data, vacuous finite/∞-pole fields, and the
vanishing kirovGenus-`0` continuation.  The honest non-vacuity witness. -/
noncomputable def movingCoherenceFamily_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    MovingCoherenceFamily ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
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
  Creg := fun z _ => movingCoherenceDatum_empty ω₀ g f z
  hCreg_g := fun z _ i => i.elim
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

/-- **Non-vacuity of the moving-fibre Gate-A reduction.**  For the empty pole set the reduction
`residueSum_eq_zero_of_movingCoherenceFamily` is satisfiable via the empty family
(`movingCoherenceFamily_empty`), yielding `∑Res = 0`.  Confirms the family reduction is honest (not a
disguised `False`). -/
theorem residueSum_eq_zero_of_movingCoherenceFamily_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_movingCoherenceFamily (adaptedCover_empty ω₀ g f hdiv)
    (movingCoherenceFamily_empty ω₀ g f hdiv)

end Jacobians.Dolbeault.FormTraceMovingFibre
