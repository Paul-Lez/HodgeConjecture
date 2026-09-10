/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedFullFibre
import KirovDolbeault.Dolbeault.SerreResidueGateAInftyBuilder

/-!
# The SOUND full-fibre residue close of Gate A (whole-fibre `D`, non-poles → residue `0`)

This file closes the Gate-A residue theorem `∑_{a ∈ poles} formFnResidue ω₀ g a = 0` *soundly*, fixing
the full-fibre-vs-pole-only inconsistency of `FibreClusterReindex`
(`SerreResidueRamifiedFullFibreBuilder.lean`).

## The bug it fixes

`FibreClusterReindex` carried *two incompatible* requirements on its fibre `D`:

* `hgeom_fibre` (the full-fibre cluster identity) + the conservation-of-number count
  `hcard : ∑ᵢ D.mult i = S.n = deg f` force `D` to enumerate the **WHOLE fibre** `F⁻¹(coe c)` (all
  `deg f` preimages — pole *and* non-pole), because the geometric trace is a sum over **all** sheets;
* `hD_mem : ∀ i, D.xs i ∈ poles` forces `D` to be the **α-poles only**.

For a fibre over a pole-value that contains non-pole points (the *generic* case) these conflict, so
`FibreClusterReindex` is uninstantiable (vacuous) and `∑Res = 0` is NOT closed.

## The fix (the correct full-fibre design)

`D` = the **WHOLE fibre**.  The geometric/conservation fields (`hgeom_fibre`, `hcard`) are then
consistent.  The residue sum is reconciled at the *residue level*: the per-cluster residue is
`formFnResidue ω₀ g (D.xs i)`, and

* a **non-pole** preimage `D.xs i ∉ poles` contributes residue `0` (`α` is holomorphic there —
  `formFnResidue_eq_zero_of_analyticAt`, the PROVEN `Res(holo) = 0`);
* the **pole** preimages enumerate exactly the α-poles of the fibre.

So the full-fibre residue sum collapses to the pole-only fibre sum (`residueSum_full_eq_poleOnly`, the
PROVEN shared full→pole-only engine, already used in the unramified `Cfull` route), which is the
fibre-restricted pole-set sum.  Summed over the finite centres + the `∞` group (the proven
`residueSum_eq_zero_of_centerFacts`), the total residue vanishes.

This is exactly the `Cfull` route's residue-level discharge (`hres_fin_of_fullFibreCoherence`), but with
the per-centre trace coherence coming from the **ramified** full-fibre cluster geometry
(`FullFibreClusterData`) instead of the unramified `MovingCoherenceDatum`.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `FullFibreClusterData.resAt_patched_filter_of_nonpole` — fact (B, filtered) directly from a whole-fibre
  `FullFibreClusterData` + the non-pole-residue-`0` datum + the pole-fibre surjectivity: the residue of
  the patched trace at `c` equals the fibre-restricted pole-set sum.
* `FullFibreCenterReindex` — the SOUND per-centre residual (the corrected `FibreClusterReindex`):
  whole-fibre `FullFibreClusterData` + the eventual analyticity/pole-order meromorphy bound + the
  non-pole-residue-`0` datum + the pole surjectivity.  **No `hD_mem` (no all-poles assumption).**
* `residueSum_eq_zero_of_fullFibreReindex` — `∑Res = 0` from per-centre `FullFibreCenterReindex` +
  `GateAInftyData`.
* `residueSum_eq_zero_of_fullFibreReindex_adaptedFRamified` — the same from an `AdaptedFRamified` datum
  (the `hnonpole` datum then comes for free from `A.hg_an_offpoles`).

## ⚠ Soundness

`D` = the WHOLE fibre (all `deg f` preimages), **never** the poles.  Non-pole clusters genuinely
contribute residue `0` (`formFnResidue_eq_zero_of_analyticAt`, `α` holomorphic).  The reconciliation is
the PROVEN `residueSum_full_eq_poleOnly`.  No all-poles assumption; no full Riemann–Roch (no
circularity); no custom axiom; no unproved obligation on a false statement; no false/junk/circular field.  Sanity: at a
fibre with both poles and non-poles the non-pole contribution is `0` and the formula holds (the explicit
non-vacuity witnesses `fullFibreCenterReindex_zero` / `…_empty`).

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (conservation of number), §5 (`z = wᵐ`), §17.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1 + Lemma 3.2).
* `SerreResidueRamifiedFullFibre.lean` (`FullFibreClusterData`, `resAt_fibreTrace`),
  `SerreResidueDirect.lean` (`residueSum_full_eq_poleOnly`, the full→pole-only engine),
  `SerreResidueRamifiedCenter.lean` (`residueSum_eq_zero_of_centerFacts`),
  `SerreResidueGateAInftyBuilder.lean` (`gateAInftyData_of_adaptedFRamified`, `AdaptedFRamified`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip
  Jacobians.Dolbeault.FormTraceFullFibre

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Fact (A)/(B, filtered) from a whole-fibre `FullFibreClusterData`

`FullFibreClusterData` already carries the SOUND whole-fibre geometry: its `D` is the whole fibre, and
`resAt_fibreTrace` reads `resAt T c = ∑ᵢ formFnResidue ω₀ g (D.xs i)` over *all* preimages.  Combined with
the geometric coherence `hcoh` (`valueChartTrace =ᶠ[𝓝[≠] c] fibreTrace`) the *patched* trace germ-equals
`fibreTrace`, so its residue at `c` is the same whole-fibre sum.  Splitting that sum by pole-membership —
non-poles → `0` — gives the pole-fibre residue sum, exactly fact (B, filtered). -/

namespace FullFibreClusterData

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ}

/-- **Fact (A): the patched trace is meromorphic at `c`.**  The patched trace germ-equals
`valueChartTrace` (patch inert off `c`), which germ-equals `fibreTrace` (the geometric coherence `hcoh`),
which is meromorphic (`meromorphicAt_fibreTrace`). -/
theorem meromorphicAt_patched (F : FullFibreClusterData ω₀ g f Φ c) (br : Finset ℂ) :
    MeromorphicAt (valueChartTracePatched ω₀ f Φ br) c := by
  have hgerm : valueChartTracePatched ω₀ f Φ br =ᶠ[𝓝[≠] c] F.fibreTrace :=
    (valueChartTracePatched_eventuallyEq ω₀ f Φ br c).trans F.hcoh
  exact F.meromorphicAt_fibreTrace.congr hgerm.symm

/-- **The patched residue is the whole-fibre residue sum.**  `resAt (patched) c = ∑ᵢ formFnResidue ω₀ g
(D.xs i)` over the **whole fibre**: take residues across the germ-equality (`resAt_congr`), then
`resAt_fibreTrace`. -/
theorem resAt_patched (F : FullFibreClusterData ω₀ g f Φ c) (br : Finset ℂ) :
    resAt (valueChartTracePatched ω₀ f Φ br) c = ∑ i, formFnResidue ω₀ g (F.D.xs i) := by
  have hgerm : valueChartTracePatched ω₀ f Φ br =ᶠ[𝓝[≠] c] F.fibreTrace :=
    (valueChartTracePatched_eventuallyEq ω₀ f Φ br c).trans F.hcoh
  rw [resAt_congr hgerm, F.resAt_fibreTrace]

/-- **Fact (B, filtered), the SOUND reconciliation.**  From a **whole-fibre** `FullFibreClusterData` `F`,
the non-pole-residue-`0` datum (`hnonpole`: a preimage off `poles` has `formFnResidue = 0`, true by
`α` holomorphy), and the pole surjectivity (`hD_surj`: every α-pole of the fibre is some `D.xs i`), the
residue of the patched trace at `c` equals the **fibre-restricted pole-set sum**:

> `resAt (valueChartTracePatched ω₀ f Φ br) c
>    = ∑_{a ∈ poles, F a = coe c} formFnResidue ω₀ g a`.

Proof: `resAt_patched` reads the residue as the **whole-fibre** sum `∑ᵢ formFnResidue ω₀ g (D.xs i)`;
the PROVEN full→pole-only engine `residueSum_full_eq_poleOnly` collapses it to the sum over the pole
sub-fibre `{i // D.xs i ∈ poles}` (non-poles contribute `0`), which the `Finset` re-indexing identifies
with the fibre-restricted pole-set sum (via `hD_inj`/`hD_surj`).  **No `hD_mem` (no all-poles
assumption)** — the whole fibre is enumerated, and the non-poles drop out at the residue level. -/
theorem resAt_patched_filter_of_nonpole (F : FullFibreClusterData ω₀ g f Φ c) (br : Finset ℂ)
    {poles : Finset X}
    (hnonpole : ∀ i, F.D.xs i ∉ poles → formFnResidue ω₀ g (F.D.xs i) = 0)
    (hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, F.D.xs i = a) :
    resAt (valueChartTracePatched ω₀ f Φ br) c
      = ∑ a ∈ poles with f.toRiemannSphere a = ((c : ℂ) : RiemannSphere), formFnResidue ω₀ g a := by
  classical
  rw [F.resAt_patched br]
  -- The pole sub-fibre, as a subtype of the whole-fibre index.
  let ιP := {i : F.D.ι // F.D.xs i ∈ poles}
  let xsPo : ιP → X := fun j => F.D.xs j.1
  have hpo_inj : Function.Injective xsPo := fun a b hab => Subtype.ext (F.hD_inj hab)
  -- The pole points of the whole fibre = image of the pole sub-fibre enumeration.
  have hpole_image : (Finset.univ.image F.D.xs).filter (· ∈ poles)
      = Finset.univ.image xsPo := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, xsPo]
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩; exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩
  -- Full-fibre residue sum = pole-sub-fibre residue sum (non-poles → 0).
  rw [residueSum_full_eq_poleOnly (poles := poles) F.D.xs xsPo F.hD_inj hpo_inj hpole_image hnonpole]
  -- The pole-sub-fibre residue sum = the fibre-restricted pole-set sum (pure `Finset` re-indexing).
  have hImg : (Finset.univ : Finset ιP).image xsPo
      = poles.filter (fun a => f.toRiemannSphere a = ((c : ℂ) : RiemannSphere)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, xsPo]
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨hi, F.D.hmem i⟩
    · rintro ⟨ha_pole, ha_fib⟩
      obtain ⟨i, rfl⟩ := hD_surj a ha_pole ha_fib
      exact ⟨⟨i, ha_pole⟩, rfl⟩
  rw [← hImg, Finset.sum_image (fun i _ j _ h => hpo_inj h)]

end FullFibreClusterData

/-! ## The SOUND per-centre residual `FullFibreCenterReindex`

The corrected replacement of `FibreClusterReindex`.  At a finite pole-value centre `c`, it carries the
**whole-fibre** `FullFibreClusterData` (the genuine §5 cluster geometry — all preimages, genuine
`clusterSheet` points), the eventual analyticity / pole-order bound feeding the meromorphy of the
geometric trace (already a field of `FullFibreClusterData` as `hvct_mero`, so not duplicated here), the
non-pole-residue-`0` datum, and the pole surjectivity.  **There is no `hD_mem` (no all-poles
assumption)** — that is precisely the inconsistency we drop. -/

/-- **The SOUND per-centre full-fibre residual** at a finite pole-value centre `c`.  The corrected
`FibreClusterReindex`: a **whole-fibre** `FullFibreClusterData` for the canonical selection, plus the
residue-level reconciliation data:

* `F` — the whole-fibre cluster data (`F.D` enumerates the *whole* fibre `F⁻¹(coe c)`, the `hcard`
  consistency; carries `hgeom_fibre`, `hcoh`, and the meromorphy `hvct_mero` internally);
* `hnonpole` — a non-pole preimage `F.D.xs i ∉ poles` contributes residue `0` (`α` is holomorphic
  there; the PROVEN `formFnResidue_eq_zero_of_analyticAt`);
* `hD_surj` — every α-pole of the fibre is enumerated by `F.D.xs`.

**No `hD_mem` (no all-poles assumption):** the fibre `F.D` is the WHOLE fibre, and the non-pole points
genuinely drop out at the residue level.  This is the fix of the full-fibre-vs-pole inconsistency. -/
structure FullFibreCenterReindex (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) (c : ℂ) where
  /-- The whole-fibre cluster data for the canonical selection (`F.D` = the whole fibre `F⁻¹(coe c)`). -/
  F : FullFibreClusterData ω₀ g f (canonicalFibreSelection g f hdiv) c
  /-- A non-pole preimage contributes residue `0` (`α` holomorphic; `formFnResidue_eq_zero_of_analyticAt`). -/
  hnonpole : ∀ i, F.D.xs i ∉ poles → formFnResidue ω₀ g (F.D.xs i) = 0
  /-- Every α-pole of the fibre over `coe c` is enumerated by the whole-fibre `F.D.xs`. -/
  hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, F.D.xs i = a

namespace FullFibreCenterReindex

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {c : ℂ}

/-- **Fact (A) from a `FullFibreCenterReindex`** — the patched trace is meromorphic at `c`. -/
theorem meromorphicAt_patched (R : FullFibreCenterReindex ω₀ g f hdiv poles c) (br : Finset ℂ) :
    MeromorphicAt (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br) c :=
  R.F.meromorphicAt_patched br

/-- **Fact (B, filtered) from a `FullFibreCenterReindex`** — the residue of the patched trace at `c` is
the fibre-restricted pole-set sum (the SOUND reconciliation, non-poles → `0`). -/
theorem resAt_patched_filter (R : FullFibreCenterReindex ω₀ g f hdiv poles c) (br : Finset ℂ) :
    resAt (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br) c
      = ∑ a ∈ poles with f.toRiemannSphere a = ((c : ℂ) : RiemannSphere), formFnResidue ω₀ g a :=
  R.F.resAt_patched_filter_of_nonpole br R.hnonpole R.hD_surj

end FullFibreCenterReindex

/-! ## `∑Res = 0` from per-centre `FullFibreCenterReindex` + `GateAInftyData`

Feeding the per-centre facts (A)/(B, filtered) — now SOUNDLY built from the whole-fibre cluster geometry
— into the PROVEN `hoff_cs`-free `residueSum_eq_zero_of_centerFacts` closes Gate A. -/

/-- **Gate A `∑Res = 0` from per-centre `FullFibreCenterReindex` (the SOUND full-fibre close).**  Given
the per-centre SOUND full-fibre residual `FullFibreCenterReindex` (whole fibre, non-poles → residue `0` —
NO all-poles assumption) and the already-Gate-A-discharged off-centre/∞ bundle `GateAInftyData`, the
total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g a = 0`.

This routes facts (A)/(B, filtered) (`FullFibreCenterReindex.meromorphicAt_patched` /
`resAt_patched_filter`) into the PROVEN `residueSum_eq_zero_of_centerFacts`.  The full-fibre-vs-pole
inconsistency of `FibreClusterReindex` is gone: `F.D` is the WHOLE fibre, and the non-pole preimages
drop out of the residue sum (`residueSum_full_eq_poleOnly`). -/
theorem residueSum_eq_zero_of_fullFibreReindex {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {m : ℕ}
    {cs : Fin m → ℂ} {br : Finset ℂ}
    (A : Jacobians.GateAInftyData ω₀ g f hdiv poles cs br)
    (R : ∀ i, FullFibreCenterReindex ω₀ g f hdiv poles (cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_centerFacts (canonicalFibreSelection g f hdiv) m cs A.ρ A.hcs_ball A.hcs_inj br
    A.hreg A.hbnd A.hcenters_cs
    (fun i => (R i).meromorphicAt_patched br)
    (fun i => (R i).resAt_patched_filter br)
    A.Dinf_full A.hcoh_full A.hfullInf_inj A.xsInf_po A.hpoInf_inj A.hpoInf_mem A.hpoInf_surj
    A.hpole_image_inf A.hnonpole_inf_an

/-- **Gate A `∑Res = 0` from an `AdaptedFRamified` + per-centre `FullFibreCenterReindex`.**  For a genuine
meromorphic numerator `g`, an `AdaptedFRamified` datum `A` (the off-centre/∞ genericity, **admitting
ramified finite pole fibres**) and at each finite pole-value centre `A.cs i` a SOUND full-fibre residual
`FullFibreCenterReindex`, the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This composes `gateAInftyData_of_adaptedFRamified` (TARGET 2, discharged) with the per-centre SOUND
full-fibre residuals (TARGET 1) into `residueSum_eq_zero_of_fullFibreReindex`.  The *only*
genuinely-remaining analytic content is the per-centre `FullFibreCenterReindex` (the whole-fibre cluster
geometry); the off-centre/∞ bundle is fully discharged. -/
theorem residueSum_eq_zero_of_fullFibreReindex_adaptedFRamified {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles)
    (R : ∀ i, FullFibreCenterReindex ω₀ g.toFun A.f A.hdiv poles (A.cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueSum_eq_zero_of_fullFibreReindex (gateAInftyData_of_adaptedFRamified A) R

/-! ## Soundness: `FullFibreCenterReindex` is NOT a disguised `False`

The decisive #17-style soundness check: `FullFibreCenterReindex` is inhabited at a genuine
multi-preimage ramified fibre — and crucially it imposes **no** restriction that the fibre be all-poles
(the inconsistency we fixed).  For the zero numerator `g ≡ 0` the canonical-selection geometric trace
vanishes identically, so for *any* injective whole fibre `D` over `c` (any preimages, any multiplicities
`≥ 1`, **any mix of pole and non-pole points**) we inhabit a `FullFibreCenterReindex` with the empty pole
set: `hnonpole` is then vacuously the residue-`0` fact (and indeed `formFnResidue ω₀ 0 a = 0` for the
zero numerator), and `hD_surj` is vacuous.  With `poles = ∅` no preimage is a pole, so the fibre is
*entirely non-pole* — the precise generic case that broke `FibreClusterReindex.hD_mem`. -/

/-- **The form residue of the zero numerator vanishes.**  `formFnResidue ω₀ (fun _ => 0) a = 0` — the
chart integrand `coeffAt ω₀ a · 0 = 0` is analytic, so its residue is `0`. -/
theorem formFnResidue_zero_numerator (ω₀ : HolomorphicOneForms X) (a : X) :
    formFnResidue ω₀ (fun _ => (0 : ℂ)) a = 0 :=
  formFnResidue_eq_zero_of_analyticAt ω₀ (fun _ => (0 : ℂ)) a (by simpa using analyticAt_const)

/-- **The whole-fibre `FullFibreClusterData` for the canonical selection at the zero numerator.**  For
`g ≡ 0` the canonical-selection geometric trace vanishes (`valueChartTrace_zero_numerator`), so *any*
injective whole fibre `D` over `c` carries a `FullFibreClusterData` for the *canonical* selection — each
preimage a genuine `clusterTraceData_slit` cluster (the `cpow` slit branch), `hgeom_fibre` the identity
`0 = ∑ᵢ ∑ⱼ 0`.  This is the canonical-selection analogue of `fullFibreClusterData_zero` (which uses the
empty selection), built to match the `canonicalFibreSelection` parameter of `FullFibreCenterReindex`. -/
noncomputable def fullFibreClusterData_zero_canonical (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (D : FibreRamifiedData (fun _ => (0 : ℂ)) f c) (hD_inj : Function.Injective D.xs) :
    FullFibreClusterData ω₀ (fun _ => (0 : ℂ)) f
      (canonicalFibreSelection (fun _ => (0 : ℂ)) f hdiv) c where
  D := D
  hD_inj := hD_inj
  S := {z | z - c ∈ slitPlane}
  hS_acc := (fibreClusterReindex_zero ω₀ f hdiv c D hD_inj).hS_acc
  Cl := fun i => clusterTraceData_slit ω₀ (D.xs i) c (D.mult i) (D.hmult_pos i)
    (Complex.exp (2 * π * Complex.I / (D.mult i)))
    (Complex.isPrimitiveRoot_exp (D.mult i) (D.hmult_pos i).ne')
  hmult := fun _ => rfl
  hsplit0 := by
    intro i
    refine Filter.EventuallyEq.of_eq ?_
    funext u
    simp [straightenedIntegrand, chartIntegrand, negTail, clusterTraceData_slit]
  hvct_mero := by
    rw [valueChartTrace_zero_numerator ω₀ f hdiv]
    exact analyticAt_const.meromorphicAt
  hgeom_fibre := by
    intro z _
    rw [valueChartTrace_zero_numerator ω₀ f hdiv]
    symm
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    rw [show chartIntegrand ω₀ (fun _ => (0 : ℂ)) (D.xs i) = (fun _ => (0 : ℂ)) by
      funext w; simp [chartIntegrand]]
    simp

/-- **`FullFibreCenterReindex` is inhabited at a genuine all-non-pole ramified fibre** (the #17 soundness
witness — the precise generic case `FibreClusterReindex` could not express).  For the zero numerator
`g ≡ 0` and *any* injective whole fibre `D` over `c` (any preimages, any multiplicities `≥ 1`), with the
**empty** pole set, a `FullFibreCenterReindex` is inhabited: the whole-fibre `FullFibreClusterData` is
`fullFibreClusterData_zero_canonical`, `hnonpole` holds (zero-numerator residue `0`), and `hD_surj` is
vacuous (empty poles).  Every preimage is a non-pole, yet the structure is satisfiable — confirming **no
all-poles assumption** and that it is **not** a disguised `False`. -/
noncomputable def fullFibreCenterReindex_zero (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (D : FibreRamifiedData (fun _ => (0 : ℂ)) f c) (hD_inj : Function.Injective D.xs) :
    FullFibreCenterReindex ω₀ (fun _ => (0 : ℂ)) f hdiv (∅ : Finset X) c where
  F := fullFibreClusterData_zero_canonical ω₀ f hdiv c D hD_inj
  hnonpole := fun _ _ => formFnResidue_zero_numerator ω₀ _
  hD_surj := fun a ha _ => absurd ha (Finset.notMem_empty a)

/-- **`FullFibreCenterReindex` is inhabited at a genuine MIXED fibre** (the decisive #17 sanity check —
both poles and non-poles in the same fibre).  For the zero numerator `g ≡ 0` and any injective whole
fibre `D` over `c`, with **any** pole set `poles` whose fibre part lies in the fibre (`hpoles_sub`:
`poles ⊆ range D.xs`, so some fibre points are poles and others may not be), a `FullFibreCenterReindex` is
inhabited.  This is the case the old `FibreClusterReindex.hD_mem` (which demanded the *whole* fibre be
poles) could not express: here a *proper* nonempty subset of the fibre can be the poles, the rest are
non-poles contributing residue `0`.  `hnonpole` holds (zero-numerator residue `0` everywhere), and
`hD_surj` holds since `poles ⊆ range D.xs`. -/
noncomputable def fullFibreCenterReindex_zero_mixed (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (D : FibreRamifiedData (fun _ => (0 : ℂ)) f c) (hD_inj : Function.Injective D.xs)
    (poles : Finset X) (hpoles_sub : ↑poles ⊆ Set.range D.xs) :
    FullFibreCenterReindex ω₀ (fun _ => (0 : ℂ)) f hdiv poles c where
  F := fullFibreClusterData_zero_canonical ω₀ f hdiv c D hD_inj
  hnonpole := fun _ _ => formFnResidue_zero_numerator ω₀ _
  hD_surj := fun _ ha _ => hpoles_sub ha

/-- **The MIXED-fibre residue formula holds** (the directive's decisive sanity check).  For the zero
numerator, at a fibre over `c` enumerated by an injective `D` (genuinely mixing pole/non-pole points via
`poles ⊆ range D.xs`), the residue of the patched trace at `c` equals the fibre-restricted pole-set sum,
which is `0` — the non-pole contribution is `0` (zero numerator) and the pole contribution is `0` too,
confirming the reconciliation `resAt = ∑_{a ∈ poles, F a = coe c} formFnResidue` is correct at a MIXED
fibre (not secretly all-poles or all-non-poles). -/
theorem resAt_patched_filter_mixed_zero (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (D : FibreRamifiedData (fun _ => (0 : ℂ)) f c) (hD_inj : Function.Injective D.xs)
    (poles : Finset X) (hpoles_sub : ↑poles ⊆ Set.range D.xs) (br : Finset ℂ) :
    resAt (valueChartTracePatched ω₀ f (canonicalFibreSelection (fun _ => (0 : ℂ)) f hdiv) br) c
      = ∑ a ∈ poles with f.toRiemannSphere a = ((c : ℂ) : RiemannSphere),
          formFnResidue ω₀ (fun _ => (0 : ℂ)) a := by
  exact (fullFibreCenterReindex_zero_mixed ω₀ f hdiv c D hD_inj poles hpoles_sub).resAt_patched_filter br

/-- **Non-vacuity of `residueSum_eq_zero_of_fullFibreReindex`'s premise (no finite pole-value centres).**
When there are no finite pole-value centres (`m = 0`), the per-centre residual is vacuously inhabited —
the SOUND full-fibre route is **not** a disguised `False`. -/
theorem fullFibreReindex_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X)
    (br : Finset ℂ) (A : Jacobians.GateAInftyData ω₀ g f hdiv poles (m := 0) Fin.elim0 br) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_fullFibreReindex A (fun i => i.elim0)

end Jacobians.Dolbeault.SerreResidueTheorem
