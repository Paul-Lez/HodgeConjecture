/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedFullFibreBuilder
import KirovDolbeault.Dolbeault.SerreResidueGateAClosed
import KirovDolbeault.Dolbeault.SerreResidueInftyCoherence

/-!
# The Gate-A off-centre/∞ bundle `GateAInftyData` from an adapted cover (TARGET 2)

The `hoff_cs`-free ramified Gate-A capstone `residueSum_eq_zero_of_reindex`
(`SerreResidueRamifiedFullFibreBuilder.lean`) consumes two residuals: the per-centre fibre-cluster
reindexing `FibreClusterReindex` (the geometric wall, TARGET 1) **and** the off-centre/∞ genericity bundle
`GateAInftyData` (`SerreResidueRamifiedRealCover.lean`).  This file **builds `GateAInftyData`** for the
canonical full-fibre selection from a genericity datum that is exactly the unramified `AdaptedF`
(`SerreResidueGateAClosed.lean`) *minus* the unramified-pole-fibre demand `hoff_cs` — i.e. the same
"choose any nonconstant `f` with simple `∞`-poles" selection, but **admitting ramified finite pole
fibres** (which the cluster route handles).

Every field of `GateAInftyData` is discharged from the **already-proven** unramified machinery for the
canonical selection:

* `hreg` (off-centre analyticity) — `hreg_canonical_at_goodValue_sound` (the moving-datum coherence lever
  `analyticAt_valueChartTrace_of_movingDatum`), valid at every value off the finite bad set, since `g`
  meromorphic ⟹ every off-pole fibre is `g`-analytic and every off-branch value is `GoodValue`;
* `hbnd` (branch-value boundedness) — the αBr-free SOUND `g`-weighted route `hbnd_canonical_sound_full`;
* the entire **∞-group** (`Dinf_full`/`hcoh_full`/`hfullInf_inj` + the ∞-pole enumeration) — the simple-∞
  reciprocal-chart coherence `InftyMovingCoherenceData.ofInftySheetSystem` (gated by `hsimpleInf`) and the
  full ∞-fibre datum `inftyFibreDataNF_full`, exactly as in the proven `…_inftyClosed` route.

So `GateAInftyData` is NOT new analytic content: it is the off-centre/∞ genericity isolate, identical to
what the unramified route discharges, packaged into the bundle the ramified route consumes.  The *only*
genuinely-remaining content of the ramified Gate-A route is then TARGET 1 (`FibreClusterReindex`).

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `AdaptedFRamified` — the genericity datum (`AdaptedF` minus `hoff_cs`): a nonconstant `f` with simple
  `∞`-poles and the pole-value enumeration, NOT demanding unramified finite pole fibres.
* `gateAInftyData_of_adaptedFRamified` — **the `GateAInftyData` builder** from an `AdaptedFRamified` for a
  genuine meromorphic numerator `g`.
* `residueSum_eq_zero_of_reindex_adaptedFRamified` — `∑Res = 0` from an `AdaptedFRamified` *and* the
  per-centre `FibreClusterReindex` (TARGET 1), routing through `residueSum_eq_zero_of_reindex`.

## ⚠ Soundness

`AdaptedFRamified` is the honest off-centre/∞ genericity residual (a strict weakening of `AdaptedF`,
dropping `hoff_cs`), supplied as data.  The builder uses only proven dischargers; no false/junk/circular
field, no custom axiom, no gaps.  Non-vacuity: the `AdaptedF → AdaptedFRamified` forgetful map shows it
is inhabited whenever the unramified `AdaptedF` is.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, p. 254 ("choose any nonconstant `f`").
* `Jacobians/Dolbeault/SerreResidueGateAClosed.lean` (`AdaptedF`, `hreg_canonical_at_goodValue_sound`,
  `hbnd_canonical_sound_full`), `SerreResidueInftyCoherence.lean`
  (`InftyMovingCoherenceData.ofInftySheetSystem`, `hcoh_geom_of_inftyMovingCoherenceData`),
  `SerreResidueRamifiedRealCover.lean` (`GateAInftyData`),
  `SerreResidueRamifiedFullFibreBuilder.lean` (`residueSum_eq_zero_of_reindex`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceMovingFibre
  Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The `hoff_cs`-free genericity datum -/

/-- **The `hoff_cs`-free adapted-cover genericity datum** for `α = ω₀·g` (genuine meromorphic `g`) over
`poles`.  Identical to `AdaptedF` (`SerreResidueGateAClosed.lean`) **except** it drops the
unramified-pole-fibre genericity `hoff_cs` — the finite pole fibres may be **ramified** (the cluster
route, TARGET 1, handles them).  Every `g`-meromorphy/holomorphy field is still automatic from `g`'s
global meromorphy, so the only fields are the generic-position facts about `f`: nonconstancy, the
pole-value enumeration `cs`, simple `∞`-poles, and the definition of `poles` (off it `g` is analytic). -/
structure AdaptedFRamified (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X) where
  /-- The cover `f` is nonconstant. -/
  f : MeromorphicFunction X
  /-- `f.div ≠ 0`. -/
  hdiv : (f.div : Divisor X) ≠ 0
  /-- The number of finite pole-values of `α`. -/
  m : ℕ
  /-- The enumeration of the finite pole-values of `α` (the `f`-images of `poles`, off `∞`). -/
  cs : Fin m → ℂ
  /-- A radius bounding the finite pole-values. -/
  ρ : ℝ
  hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ
  hcs_inj : Function.Injective cs
  hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- **Genericity (the *only* one kept):** `f` has simple poles over `∞`. -/
  hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1
  /-- `poles` is exactly the pole set of `α = ω₀·g`: off `poles`, `g`'s chart-pullback is analytic. -/
  hg_an_offpoles : ∀ x : X, x ∉ poles →
    AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)

/-- **The forgetful map `AdaptedF → AdaptedFRamified`** (non-vacuity / soundness).  An unramified
adapted cover `AdaptedF` (which additionally demands `hoff_cs`) is in particular an `AdaptedFRamified`;
so `AdaptedFRamified` is inhabited whenever `AdaptedF` is.  This certifies `AdaptedFRamified` is a strict
*weakening*, not a disguised `False`. -/
def AdaptedFRamified.ofAdaptedF {ω₀ : HolomorphicOneForms X} {g : MeromorphicFunction X}
    {poles : Finset X} (A : AdaptedF ω₀ g poles) : AdaptedFRamified ω₀ g poles where
  f := A.f
  hdiv := A.hdiv
  m := A.m
  cs := A.cs
  ρ := A.ρ
  hcs_ball := A.hcs_ball
  hcs_inj := A.hcs_inj
  hcenters_cs := A.hcenters_cs
  hsimpleInf := A.hsimpleInf
  hg_an_offpoles := A.hg_an_offpoles

/-! ## The `GateAInftyData` builder -/

/-- **The Gate-A off-centre/∞ bundle from an adapted cover (TARGET 2).**  For a genuine meromorphic
numerator `g`, an `AdaptedFRamified` datum produces a `GateAInftyData` for the canonical full-fibre
selection, with `br := branchValues f`.  Every field is discharged from the proven canonical-selection
machinery:

* the discrete bookkeeping (`ρ`/`hcs_ball`/`hcs_inj`/`hcenters_cs`) — from the datum;
* `hreg` (off-centre analyticity at every `w ∉ image cs ∪ br`) — `hreg_canonical_at_goodValue_sound`,
  with the `GoodValue`/meromorphy automatic from `g`'s global meromorphy and analyticity off `poles`;
* `hbnd` (branch-value boundedness) — the αBr-free `hbnd_canonical_sound_full`;
* the ∞-group (`Dinf_full := inftyFibreDataNF_full`, `hcoh_full` via the reciprocal-chart coherence
  `InftyMovingCoherenceData.ofInftySheetSystem` gated by `hsimpleInf`, the ∞-pole enumeration via
  `inftyFibreEnum`).

This is the off-centre/∞ genericity isolate — identical to what the unramified `…_inftyClosed` route
discharges, repackaged into the bundle the ramified cluster route consumes. -/
noncomputable def gateAInftyData_of_adaptedFRamified {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles) :
    Jacobians.GateAInftyData ω₀ g.toFun A.f A.hdiv poles A.cs (branchValues A.f A.hdiv) := by
  classical
  -- `g` is meromorphic at every point; `GoodValue` off the branch locus is then automatic.
  have hmero_pt : ∀ y : X, MeromorphicAt (fun w => g.toFun ((chartAt ℂ y).symm w)) ((chartAt ℂ y) y) :=
    fun y => g.meromorphic y
  -- `GoodValue` from off-branch (the `g`-meromorphy of the full-fibre points is free).
  have hgood_of_off : ∀ w, (((w : ℂ) : RiemannSphere)) ∉ branchLocus A.f.toRiemannSphere →
      GoodValue g.toFun A.f A.hdiv w := fun w hw =>
    ⟨hw, fun i => hmero_pt (fullFibreEnum A.f A.hdiv w i)⟩
  -- Eventual fibre `g`-meromorphy: holds for ALL `b'` (genuine meromorphic `g`).
  have hgmero_all : ∀ w : ℂ, ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g.toFun ((chartAt ℂ (fullFibreEnum A.f A.hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum A.f A.hdiv b' j)) (fullFibreEnum A.f A.hdiv b' j)) := fun w =>
    Filter.Eventually.of_forall (fun b' j => hmero_pt (fullFibreEnum A.f A.hdiv b' j))
  -- A value `w ∉ image cs ∪ branchValues f` is off the branch locus, hence a `GoodValue`.
  have hgood_reg : ∀ w ∉ Finset.univ.image A.cs ∪ branchValues A.f A.hdiv,
      GoodValue g.toFun A.f A.hdiv w := fun w hw =>
    hgood_of_off w (coe_notMem_branchLocus_of_notMem_branchValues A.f A.hdiv
      (fun h => hw (Finset.mem_union_right _ h)))
  -- `g`'s chart-pullback is analytic at non-poles; over a value `w` whose fibre point is a non-pole
  -- (off `poles`), this is `hg_an_offpoles`.  A finite pole-value off `image cs` is impossible, so the
  -- fibre over any off-`cs` value contains no pole (its sheet points are non-poles).
  have hg_an_at : ∀ {w : ℂ}, w ∉ Finset.univ.image A.cs → ∀ y : X,
      A.f.toRiemannSphere y = (((w : ℂ) : RiemannSphere)) →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ y).symm z)) ((chartAt ℂ y) y) := by
    intro w hwcs y hy
    refine A.hg_an_offpoles y ?_
    -- If `y` were a pole, `F y = ∞ ≠ coe w`; so `y` is a non-pole, hence off `poles` (poles ⊆ {coe-val
    -- centres} ∪ {∞-poles}); a non-`∞` value off `image cs` cannot be a pole-value.
    intro hy_pole
    -- `y ∈ poles` and `F y = coe w` (finite), so `coe w` is a finite pole-value, i.e. `coe w ∈
    -- (poles.image F).erase ∞ = (image cs).image coe`; thus `w = cs i` for some `i`, contradiction.
    have hmem : (((w : ℂ) : RiemannSphere)) ∈
        (poles.image A.f.toRiemannSphere).erase OnePoint.infty := by
      rw [Finset.mem_erase]
      exact ⟨OnePoint.coe_ne_infty w, hy ▸ Finset.mem_image_of_mem _ hy_pole⟩
    rw [← A.hcenters_cs, Finset.mem_image] at hmem
    obtain ⟨q, hq, hqw⟩ := hmem
    rw [Finset.mem_image] at hq
    obtain ⟨i, _, hi⟩ := hq
    exact hwcs (by
      have : ((A.cs i : ℂ) : RiemannSphere) = (((w : ℂ) : RiemannSphere)) := by rw [hi, hqw]
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ i, OnePoint.coe_injective this⟩)
  -- The `∞`-pole enumeration of `α`: the subtype of the `∞`-fibre enumeration lying in `poles`.
  set ιInfP : Type := {j : Fin (A.f.finite_poles.toFinset.card) // inftyFibreEnum A.f j ∈ poles}
    with hιInfP
  set xsInf_po : ιInfP → X := fun j => inftyFibreEnum A.f j.1 with hxsInf
  have hxsInf_inj : Function.Injective xsInf_po := by
    intro a b hab
    exact Subtype.ext (inftyFibreEnum_injective A.f hab)
  refine
    { ρ := A.ρ
      hcs_ball := A.hcs_ball
      hcs_inj := A.hcs_inj
      hreg := fun w hw => hreg_canonical_at_goodValue_sound A.hdiv
        (hgood_reg w hw) (hgmero_all w) (hg_an_at (fun h => hw (Finset.mem_union_left _ h)))
      hbnd := fun b₀ hb₀br hb₀cs => hbnd_canonical_sound_full A.hdiv (Finset.Subset.refl _) hb₀br
        hgood_reg (fun w _ => hgmero_all w)
        (fun x hx => continuousAt_of_chartPullback_analyticAt (A.hg_an_offpoles x
          (notMem_poles_of_fibrePoint_offCentres A.hcenters_cs hb₀cs
            (by rwa [Set.mem_preimage, Set.mem_singleton_iff] at hx))))
        (fun hnbr => hgood_of_off b₀
          (coe_notMem_branchLocus_of_notMem_branchValues A.f A.hdiv hnbr))
        (fun _ => hgmero_all b₀)
        (fun _ => hg_an_at hb₀cs)
      hcenters_cs := A.hcenters_cs
      Dinf_full := inftyFibreDataNF_full g.toFun A.f A.hsimpleInf
        (fun i => hmero_pt (inftyFibreEnum A.f i))
      hcoh_full := ?_
      hfullInf_inj := by
        rw [inftyFibreDataNF_full_xs]; exact inftyFibreEnum_injective A.f
      ιInfP := ιInfP
      fintype_ιInfP := inferInstance
      xsInf_po := xsInf_po
      hpoInf_inj := hxsInf_inj
      hpoInf_mem := fun j => ⟨j.2, inftyFibreEnum_mem A.f j.1⟩
      hpoInf_surj := ?_
      hpole_image_inf := ?_
      hnonpole_inf_an := fun k hk => A.hg_an_offpoles (inftyFibreEnum A.f k) hk }
  · -- `hcoh_full`: the reciprocal-chart ∞-coherence (`valueChartTracePatched` bridge ∘ the geometric
    -- coherence `hcoh_geom_of_inftyMovingCoherenceData` from `InftyMovingCoherenceData.ofInftySheetSystem`).
    refine (recipCoeff_valueChartTracePatched_eventuallyEq ω₀ A.f
      (canonicalFibreSelection g.toFun A.f A.hdiv) (branchValues A.f A.hdiv)).trans ?_
    exact hcoh_geom_of_inftyMovingCoherenceData ω₀ A.f (canonicalFibreSelection g.toFun A.f A.hdiv)
      (inftyFibreDataNF_full g.toFun A.f A.hsimpleInf (fun i => hmero_pt (inftyFibreEnum A.f i)))
      (InftyMovingCoherenceData.ofInftySheetSystem ω₀ A.f (canonicalFibreSelection g.toFun A.f A.hdiv)
        (inftyFibreDataNF_full g.toFun A.f A.hsimpleInf (fun i => hmero_pt (inftyFibreEnum A.f i)))
        (by rw [inftyFibreDataNF_full_xs]; exact inftyFibreEnum_injective A.f)
        (by rw [inftyFibreDataNF_full_xs]; exact inftyFibreEnum_range A.f)
        (exists_inftySheetSystem A.f A.hdiv A.hsimpleInf).some
        (canonicalFibreSelection_hΦinj_infty g.toFun A.f A.hdiv (Finset.univ.image A.cs)
          (branchValues A.f A.hdiv) hgood_reg)
        (canonicalFibreSelection_hΦrange_infty g.toFun A.f A.hdiv (Finset.univ.image A.cs)
          (branchValues A.f A.hdiv) hgood_reg))
  · -- `hpoInf_surj`: every pole `a` of `α` over `∞` is `xsInf_po j` for some `j`.
    intro a ha hfa
    obtain ⟨k, hk⟩ := inftyFibreEnum_surj A.f hfa
    exact ⟨⟨k, hk ▸ ha⟩, hk⟩
  · -- `hpole_image_inf`: `(image inftyFibreEnum).filter (· ∈ poles) = image xsInf_po`.
    rw [inftyFibreDataNF_full_xs]
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hxsInf]
    constructor
    · rintro ⟨⟨k, hk⟩, hxp⟩
      exact ⟨⟨k, hk ▸ hxp⟩, hk⟩
    · rintro ⟨j, hj⟩
      exact ⟨⟨j.1, hj⟩, hj ▸ j.2⟩

/-! ## The capstone: `∑Res = 0` from an adapted cover + the per-centre fibre-cluster reindexing

With TARGET 2 (`GateAInftyData`) built from the off-centre/∞ genericity datum `AdaptedFRamified`, the
*entire* remaining content of the `hoff_cs`-free ramified Gate-A route is TARGET 1 — the per-centre
fibre-cluster reindexing `FibreClusterReindex` (the geometric wall).  This capstone composes the two: an
`AdaptedFRamified` plus a per-centre `FibreClusterReindex` discharges `∑Res = 0` unconditionally (for the
genuine meromorphic numerator). -/

/-- **Gate A `∑Res = 0` from an adapted cover + the per-centre fibre-cluster reindexing.**  For a genuine
meromorphic numerator `g`, given:

* an `AdaptedFRamified` datum `A` (the off-centre/∞ genericity — a nonconstant `f` with simple `∞`-poles
  and the finite pole-value enumeration, **admitting ramified finite pole fibres**), and
* at each finite pole-value centre `A.cs i`, a `FibreClusterReindex` (TARGET 1 — the genuine full-fibre
  cluster geometric reindexing of the moving trace),

the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This routes the TARGET-2 bundle `gateAInftyData_of_adaptedFRamified` and the TARGET-1 per-centre residuals
into the PROVEN capstone `residueSum_eq_zero_of_reindex`.  The *only* genuinely-remaining analytic content
is `FibreClusterReindex` (the per-centre `hgeom_fibre` — the fibre-cluster reindexing of the moving
full-fibre trace); the off-centre/∞ bundle is fully discharged here. -/
theorem residueSum_eq_zero_of_reindex_adaptedFRamified {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles)
    (R : ∀ i, FibreClusterReindex ω₀ g.toFun A.f A.hdiv poles (A.cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueSum_eq_zero_of_reindex (gateAInftyData_of_adaptedFRamified A) R

/-! ## The precise remaining obligation, isolated

`ExistsAdaptedFRamified` packages the off-centre/∞ genericity selection (always achievable — Miranda
p. 254 "choose any nonconstant `f`"), so that the unconditional residue theorem rests on **exactly two**
named residuals: this genericity selection (TARGET 2's *input*, the same isolate as `ExistsAdaptedF`) and
the per-centre fibre-cluster reindexing `FibreClusterReindex` (TARGET 1). -/

/-- **The off-centre/∞ genericity selection obligation.**  An adapted (ramification-tolerant) cover
exists for `α = ω₀·g` over any finite `poles` off which `g` is analytic.  This is the `hoff_cs`-FREE
analogue of `ExistsAdaptedF` (`SerreResidueGateAClosed.lean`) — it drops the unramified-pole-fibre demand,
since the ramified cluster route (TARGET 1) handles ramified finite pole fibres.  It is genuinely
achievable (Miranda p. 254 + the simple-`∞` reciprocal `f' = (f₀ − a)⁻¹`); strictly weaker than
`ExistsAdaptedF`, hence *no harder* to discharge. -/
def ExistsAdaptedFRamified (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X) : Prop :=
  (∀ x : X, x ∉ poles →
    AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) →
  Nonempty (AdaptedFRamified ω₀ g poles)

/-- **`ExistsAdaptedFRamified` from `ExistsAdaptedF`** (non-vacuity).  The unramified genericity obligation
`ExistsAdaptedF` (`SerreResidueGateAClosed.lean`) implies the `hoff_cs`-free `ExistsAdaptedFRamified` via
the forgetful map — confirming the latter is **not** a disguised `False` and is *no harder* than the
unramified one. -/
theorem existsAdaptedFRamified_of_existsAdaptedF {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (h : ExistsAdaptedF ω₀ g poles) :
    ExistsAdaptedFRamified ω₀ g poles :=
  fun hpoles => (h hpoles).map AdaptedFRamified.ofAdaptedF

end Jacobians.Dolbeault.SerreResidueTheorem
