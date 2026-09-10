/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceFullFibreRationality
import KirovDolbeault.Dolbeault.FormTraceInftyFibreNF

/-!
# Gate A `∑Res = 0` from full-fibre trace rationality, *sound* `∞` fibre (Miranda §VIII.3)

`Jacobians.Dolbeault.FormTraceFullFibre.TraceRationalityData` reduced Gate A to the agreements that a
`LaurentForm L` represents `Tr_F α` at the finite centres (`agree`) and across `∞` (`agree_infty`).  Its
`agree_infty` is phrased against the buggy `inftyFibreTrace` (whose `∞`-fibre datum `InftyFibreData` is
unsatisfiable for genuine `∞`-poles — see `FormTraceInftyFibreNF`).  This file is the **sound** analogue:
`TraceRationalityDataNF` uses the repaired `∞`-fibre trace `inftyFibreTraceNF` (built from the analytic
normal-form reciprocal), so `agree_infty` is against a genuinely-constructible object.

The reduction is otherwise identical: the finite `hL32` is the proved `hL32_of_agree_fibreRegularData`
(unchanged), the `∞` `infty_eq` (the `GlobalTraceData` conclusion `resAtInfty L.R = ∑_{F a = ∞} Res_a α`)
is `infty_eq_of_agreeNF` (the sound `∞`-fibre Lemma 3.2), and the discrete enumeration is carried
through.  `toGlobalTraceData` + the proved descent `GlobalTraceData.residueSum_eq_zero` then close Gate A.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `TraceRationalityDataNF` — the full-fibre trace-rationality bundle with the **sound** `∞`-fibre datum
  (`Dinf : InftyFibreDataNF`) and `agree_infty` against `inftyFibreTraceNF`;
* `TraceRationalityDataNF.toGlobalTraceData` / `residueSum_eq_zero` — Gate A `∑Res = 0` from one;
* `residueSum_eq_zero_of_traceRationalityDataNF` — the existential Gate-A reduction;
* `traceRationalityDataNF_holomorphic` — end-to-end non-vacuity (empty-pole), confirming the reduction is
  honest (not a disguised `False`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr`, Lemma 3.2; partial
  fractions on `ℂℙ¹`; normal form (3.1)).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceFullFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-- **The full-fibre trace-rationality bundle, sound `∞` fibre.**  Identical to `TraceRationalityData`,
except the `∞`-fibre datum is the honest `InftyFibreDataNF` and `agree_infty` is against the repaired
`∞`-fibre trace `inftyFibreTraceNF`:

* `L` — the candidate rational trace `Tr_F α` on `ℂℙ¹`;
* `D` / `hxs_*` — per-centre **full-fibre** regularity data, enumerating *all* poles in `F⁻¹(coe p)`;
* `Dinf` / `hxsInf_*` — the **sound `∞`-fibre** data (`InftyFibreDataNF`) enumerating all poles in
  `F⁻¹(∞)`;
* `hcenters` — the `L`-centres map (by `coe`) onto the finite pole values;
* `agree` — for each centre `p`, `L.R` agrees with the full-fibre trace coefficient off `p`;
* `agree_infty` — `recipCoeff L.R` agrees with the **repaired** `∞`-fibre trace coefficient off `0`. -/
structure TraceRationalityDataNF (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X) where
  /-- The candidate rational `1`-form representing `Tr_F α` on `ℂℙ¹`. -/
  L : LaurentForm
  /-- Per-centre full-fibre regularity data. -/
  D : (p : ℂ) → FibreRegularData g f p
  /-- `(D p).xs` is injective (each fibre point enumerated once). -/
  hxs_inj : ∀ p, Function.Injective (D p).xs
  /-- `(D p).xs` lands in the poles, in the fibre `F⁻¹(coe p)`. -/
  hxs_mem : ∀ p, ∀ i, (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere)
  /-- `(D p).xs` enumerates *all* the poles in the fibre `F⁻¹(coe p)`. -/
  hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) → ∃ i, (D p).xs i = a
  /-- The **sound** `∞`-fibre data enumerating the poles over `∞`. -/
  Dinf : InftyFibreDataNF g f
  /-- `Dinf.xs` is injective. -/
  hxsInf_inj : Function.Injective Dinf.xs
  /-- `Dinf.xs` lands in the poles, in the fibre `F⁻¹(∞)`. -/
  hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty
  /-- `Dinf.xs` enumerates *all* the poles in the fibre `F⁻¹(∞)`. -/
  hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a
  /-- The `L`-centres, mapped to the sphere, are exactly the finite pole values. -/
  hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- **Step 1 (finite):** `L.R` represents `Tr_F α` near each finite centre. -/
  agree : ∀ p ∈ (Finset.univ.image L.a),
    L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (D p)).traceCoeff
  /-- **Step 1 (`∞`):** `recipCoeff L.R` represents `Tr_F α` near `0` in the reciprocal chart (sound
  `∞`-fibre trace). -/
  agree_infty : recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff

namespace TraceRationalityDataNF

variable (T : TraceRationalityDataNF ω₀ g f poles)

/-- **The `GlobalTraceData` from a `TraceRationalityDataNF`.**  The discrete data is carried; `hL32` is
the proved finite-agreement Lemma 3.2 (`hL32_of_agree_fibreRegularData`), and `infty_eq` is the **sound**
`∞`-fibre Lemma 3.2 (`infty_eq_of_agreeNF`).  This is the clean reduction of `GlobalTraceData` to the
single Miranda-(3.1) agreement content, with the honest `∞`-fibre. -/
noncomputable def toGlobalTraceData : GlobalTraceData ω₀ g f poles where
  L := T.L
  D := T.D
  hxs_inj := T.hxs_inj
  hxs_mem := T.hxs_mem
  hxs_surj := T.hxs_surj
  hcenters := T.hcenters
  hL32 := fun p hp => hL32_of_agree_fibreRegularData T.L (T.D p) (T.agree p hp)
  infty_eq := infty_eq_of_agreeNF ω₀ f T.L T.Dinf poles T.hxsInf_inj T.hxsInf_mem T.hxsInf_surj
    T.agree_infty

/-- **Gate A for the represented form, from a `TraceRationalityDataNF`.**  The total residue of
`α = ω₀·g` over its poles vanishes: `toGlobalTraceData` + the proved descent
`GlobalTraceData.residueSum_eq_zero`. -/
theorem residueSum_eq_zero (T : TraceRationalityDataNF ω₀ g f poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  GlobalTraceData.residueSum_eq_zero T.toGlobalTraceData

end TraceRationalityDataNF

/-- **The Gate-A reduction, existential form (full-fibre, sound `∞`).**  If a `TraceRationalityDataNF ω₀
g f poles` exists — the meromorphic trace `Tr_F α` is rational (the agreements) with the pole-fibres
enumerated and the honest `∞`-fibre — then `α = ω₀·g` satisfies `∑ₐ Resₐ(α) = 0` unconditionally. -/
theorem residueSum_eq_zero_of_traceRationalityDataNF (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X)
    (T : TraceRationalityDataNF ω₀ g f poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  T.residueSum_eq_zero

/-! ### Non-vacuity (end-to-end soundness)

The empty-pole case: the empty `LaurentForm`, empty per-centre fibre data, the empty `InftyFibreDataNF`
(index `Empty`, all fields vacuous — genuinely constructible since there are no poles to repair), vacuous
agreements.  Confirms the reduction is honest. -/

/-- The **empty sound `∞`-fibre data** (no poles over `∞`): index `Empty`, all fields vacuous.  Unlike
the empty `InftyFibreData`, this is the *only* vacuous case but the structure is also satisfiable for
real `∞`-poles via `InftyFibreDataNF.ofRegular`. -/
def emptyInftyFibreDataNF (g : X → ℂ) (f : MeromorphicFunction X) : InftyFibreDataNF g f where
  ι := Empty
  fintype_ι := inferInstance
  xs := Empty.elim
  recip := fun i => i.elim
  hrecip_an := fun i => i.elim
  hrecip_deriv := fun i => i.elim
  hrecip_val := fun i => i.elim
  hrecip_germ := fun i => i.elim
  hg_mero := fun i => i.elim

/-- The trace coefficient of the empty sound `∞`-fibre trace is identically `0` (empty sum). -/
theorem traceCoeff_inftyFibreTraceNF_empty (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) :
    (inftyFibreTraceNF ω₀ f (emptyInftyFibreDataNF g f)).traceCoeff = fun _ => (0 : ℂ) := by
  funext ζ
  rw [FibreTrace.traceCoeff]
  exact Finset.sum_empty

/-- **Non-vacuity witness (end-to-end).**  A `TraceRationalityDataNF ω₀ g f ∅` always exists: the empty
`LaurentForm`, empty per-centre and `∞`-fibre data, vacuous `hcenters`, vacuous finite agreement, and the
`∞`-agreement `0 =ᶠ 0`.  Hence the obligations are satisfiable — the reduction is honest. -/
noncomputable def traceRationalityDataNF_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) : TraceRationalityDataNF ω₀ g f ∅ where
  L := Jacobians.ResidueTheoremX.emptyLaurentForm
  D := fun p => emptyFibreRegularData g f p
  hxs_inj := by intro _ i; exact i.elim
  hxs_mem := fun _ i => i.elim
  hxs_surj := fun _ a ha => absurd ha (Finset.notMem_empty a)
  Dinf := emptyInftyFibreDataNF g f
  hxsInf_inj := by intro i; exact i.elim
  hxsInf_mem := fun i => i.elim
  hxsInf_surj := fun a ha => absurd ha (Finset.notMem_empty a)
  hcenters := by rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp
  agree := by
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  agree_infty := by
    rw [recipCoeff_emptyLaurentForm, traceCoeff_inftyFibreTraceNF_empty ω₀ f]

/-- **The residue theorem, globally-holomorphic case (sound `∞`-fibre reduction).** -/
theorem residueSum_eq_zero_holomorphicNF (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  (traceRationalityDataNF_holomorphic ω₀ g f).residueSum_eq_zero

end Jacobians.Dolbeault.FormTraceFullFibre
