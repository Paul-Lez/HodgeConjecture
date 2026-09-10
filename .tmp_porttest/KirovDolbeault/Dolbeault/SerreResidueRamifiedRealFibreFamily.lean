/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedFullFibreReindexBuilder
import KirovDolbeault.Dolbeault.SerreResidueRamifiedFibreConservation
import KirovDolbeault.Dolbeault.SerreResidueRamifiedMultiplicityBridge
import KirovDolbeault.Dolbeault.SerreResidueGateAGenericity

/-!
# The per-centre §5-data assembly for the real cover (feeding the SOUND `∑Res = 0` capstone)

`SerreResidueRamifiedFullFibreReindexBuilder.lean` reduced Gate-A `∑Res = 0`, for the real cover, to the
per-centre SOUND residual `FullFibreCenterReindex`, built by `ofFibreClusterTopologyFamily_adaptedFRamified`
from, at each finite pole-value centre `c`:

* a slit `Sset` accumulating at `c`;
* the WHOLE pole-value fibre `D : FibreRamifiedData g f c` (all `deg f` preimages — non-poles drop out at
  the residue level via `hnonpole_of_adaptedFRamified`);
* per-preimage cluster data `Cl i : ClusterTraceData ω₀ g (D.xs i) c Sset`;
* a slit-wide `FibreClusterTopology` family `hfam : ∀ z ∈ Sset, FibreClusterTopology … D Cl z`.

This file performs that per-centre assembly for the **real** canonical cover, discharging the genuinely
constructible parts and isolating the irreducible per-slit conservation-of-number geometry.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`realFibreData`** — the WHOLE pole-value fibre `D` as a genuine `FibreRamifiedData g.toFun f c`: the
  index is `Fin (fullFibreCard f hdiv c)` (the whole sphere fibre `F⁻¹(coe c)`), the preimages are
  `fullFibreEnum`, the multiplicities are the genuine intrinsic local degrees
  `mult i = (localDeg f (coe c) (xs i)).toNat`, with `g.toFun`'s chart pullback meromorphic at each
  (`g.meromorphic`).  Injective (`fullFibreEnum_injective`), range the whole fibre
  (`fullFibreEnum_range`), surjective onto poles.  This is the SOUND whole fibre — NOT poles only.
* **`realFibreData_mult_pos_of_nonpole`** — at a non-pole preimage the multiplicity is `≥ 1` (the
  multiplicity bridge); ⇒ `D.hmult_pos`.
* **`RealCenterClusterFamily`** — the precise per-centre residual as a named predicate: the slit, the
  whole-fibre `D`, the per-preimage `Cl`, and the slit-wide `FibreClusterTopology` family (the genuine
  §4 conservation-of-number + §5 normal-form geometry).  **Not** asserted.
* **`FullFibreCenterReindex.ofRealCenterClusterFamily`** — builds the SOUND per-centre residual from a
  `RealCenterClusterFamily`, via `ofFibreClusterTopologyFamily_adaptedFRamified` (`hnonpole` automatic).
* **`residueSum_eq_zero_of_realCenterClusterFamily`** — Gate-A `∑Res = 0` from an `AdaptedFRamified`
  datum + a per-centre `RealCenterClusterFamily`, anchoring the precise remaining content.

## ⚠ Soundness

`D` = the WHOLE fibre `F⁻¹(coe c)` (all `deg f` preimages — NOT poles).  The multiplicities are the
genuine intrinsic `localDeg` (the §17.9 conservation-of-number multiplicity, the one
`exists_properMapDegree` is built from), never ad-hoc.  No `hD_mem` (no all-poles assumption — the #17
fix).  The cluster data / topology family is the SAME genuine §5/§4 content the capstone consumes; this
file constructs the real-cover `D`/slit and isolates the per-slit topology as `RealCenterClusterFamily`.
No custom axiom; no unproved obligation on a false statement; no false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (conservation of number), §5 (`z = wᵐ`), §17.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1, Lemma 3.2).
* `SerreResidueRamifiedFullFibreReindexBuilder.lean`
  (`FullFibreCenterReindex.ofFibreClusterTopologyFamily_adaptedFRamified`,
  `residueSum_eq_zero_of_fullFibreReindex_adaptedFRamified`),
  `SerreResidueRamifiedFibreConservation.lean` (`FibreClusterTopology.ofClusterSplitData`),
  `SerreResidueRamifiedMultiplicityBridge.lean` (`analyticOrderAt_holoRepr_sub_eq_mult`),
  `FormTraceGlobalFibreSelection.lean` (`fullFibreEnum`, `fullFibreCard`).
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
  Jacobians.Dolbeault.FormTraceMovingFibre
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The WHOLE pole-value fibre as a genuine `FibreRamifiedData` (the SOUND `D`)

At a finite value-centre `c` of a non-constant cover `f` (`f.div ≠ 0`), the sphere fibre `F⁻¹(coe c)` is
finite (`fibre_finite_of_div_ne_zero`).  We enumerate it by `fullFibreEnum` and equip each preimage with
its genuine intrinsic ramification multiplicity `(localDeg f (coe c) ·).toNat`.  For the numerator a
genuine meromorphic `g : MeromorphicFunction X`, `g.toFun`'s chart pullback is meromorphic at every
preimage (`g.meromorphic`).  This is the SOUND whole fibre — *all* `deg f` preimages, NOT poles only. -/

/-- **Every preimage of a finite value-centre is a non-pole** (`hnp` is automatic, not a hidden false
assumption).  At a finite centre `c` (`coe c ≠ ∞`), every fibre preimage `fullFibreEnum f hdiv c i` has
sphere value `coe c` which is finite, so `0 ≤ f.orderAtPoint` there
(`nonpole_of_toRiemannSphere_eq_coe`).  This discharges the `hnp` hypothesis of `realFibreData` /
`RealCenterClusterFamily` for any finite value-centre — it is TRUE, never an all-poles assumption. -/
theorem realFibre_nonpole {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (i : Fin (fullFibreCard f hdiv c)) : 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i) :=
  (f.nonpole_of_toRiemannSphere_eq_coe (fullFibreEnum_mem f hdiv c i)).1

/-- **The genuine intrinsic multiplicity of a non-pole fibre preimage is positive.**  At a preimage `p`
over `coe c` with `0 ≤ f.orderAtPoint p` (a non-pole — the case at a finite value-centre), the
multiplicity bridge gives `1 ≤ (localDeg f (coe c) p).toNat`. -/
theorem realFibre_mult_pos {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    {p : X} (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere)) (hp_np : 0 ≤ f.orderAtPoint p) :
    0 < (localDeg f ((c : ℂ) : RiemannSphere) p).toNat :=
  (Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1

/-- **The WHOLE pole-value fibre `D` for the real cover** (the SOUND `D`).  At a finite value-centre `c`
of a non-constant cover `f` (`f.div ≠ 0`) where **every** fibre preimage is a non-pole (`hnp` — true at
a finite value-centre, where `coe c ≠ ∞`), the whole sphere fibre `F⁻¹(coe c)` is a genuine
`FibreRamifiedData g.toFun f c`:

* index `Fin (fullFibreCard f hdiv c)`, preimages `fullFibreEnum f hdiv c`;
* multiplicities the genuine intrinsic `localDeg` (`mult i = (localDeg f (coe c) (xs i)).toNat`);
* `g.toFun`'s chart pullback meromorphic at each preimage (`g.meromorphic`).

**Soundness:** the whole fibre (all `deg f` preimages), the genuine `localDeg` multiplicities — NOT an
all-poles assumption.  The non-pole hypothesis `hnp` is true at any finite value-centre. -/
noncomputable def realFibreData (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    FibreRamifiedData g.toFun f c where
  ι := Fin (fullFibreCard f hdiv c)
  fintype_ι := inferInstance
  xs := fullFibreEnum f hdiv c
  hmem := fullFibreEnum_mem f hdiv c
  mult := fun i => (localDeg f ((c : ℂ) : RiemannSphere) (fullFibreEnum f hdiv c i)).toNat
  hmult_pos := fun i => realFibre_mult_pos hdiv (fullFibreEnum_mem f hdiv c i) (hnp i)
  hg_mero := fun i => by
    -- `g.toFun`'s chart pullback is meromorphic at every point (`g.meromorphic`).
    have h := g.meromorphic (fullFibreEnum f hdiv c i)
    simpa [Function.comp] using h

@[simp] theorem realFibreData_xs (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) (i) :
    (realFibreData g hdiv c hnp).xs i = fullFibreEnum f hdiv c i := rfl

@[simp] theorem realFibreData_mult (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) (i) :
    (realFibreData g hdiv c hnp).mult i
      = (localDeg f ((c : ℂ) : RiemannSphere) (fullFibreEnum f hdiv c i)).toNat := rfl

/-- `realFibreData.xs` is injective (`fullFibreEnum_injective`). -/
theorem realFibreData_inj (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    Function.Injective (realFibreData g hdiv c hnp).xs :=
  fullFibreEnum_injective f hdiv c

/-- `realFibreData.xs` has range exactly the sphere fibre `F⁻¹(coe c)` (`fullFibreEnum_range`). -/
theorem realFibreData_range (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    Set.range (realFibreData g hdiv c hnp).xs
      = f.toRiemannSphere ⁻¹' {(((c : ℂ) : RiemannSphere))} :=
  fullFibreEnum_range f hdiv c

/-- **Pole surjectivity of the whole fibre** (`hD_surj`).  Every preimage `a` of `coe c` (in particular
every α-pole there) is enumerated by `realFibreData.xs`, since the range is the whole fibre. -/
theorem realFibreData_surj (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ) {poles : Finset X}
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) →
      ∃ i, (realFibreData g hdiv c hnp).xs i = a := by
  intro a _ ha
  have : a ∈ Set.range (realFibreData g hdiv c hnp).xs := by
    rw [realFibreData_range g hdiv c hnp]; exact ha
  exact this

/-! ## The slit accumulating at `c` (a reusable atom)

The standard slit `{z | z − c ∈ slitPlane}` (the plane minus the closed negative-real ray through `c`) is
simply connected, supports the `m`-th-root branches, and accumulates at `c` (it has `c` as a limit point
from the upper imaginary direction).  This is the slit the §5 cluster data uses; we extract its
accumulation as a reusable lemma. -/

/-- **The shifted slit accumulates at its centre.**  `c` is a limit point of `{z | z − c ∈ slitPlane}`
through `𝓝[≠] c` (approach along `c + i/(n+1)`, whose imaginary part is positive so it lies in the
shifted slit, tending to `c`).  This is the `hS_acc` field for the standard slit. -/
theorem slitPlane_shift_accumulates (c : ℂ) :
    ∃ᶠ z in 𝓝[≠] c, z ∈ {z : ℂ | z - c ∈ slitPlane} := by
  rw [← accPt_iff_frequently_nhdsNE]
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

/-! ## The precise per-centre residual `RealCenterClusterFamily` (the genuine remaining geometry)

We isolate, as a named predicate, exactly the per-centre data the SOUND capstone
`FullFibreCenterReindex.ofFibreClusterTopologyFamily_adaptedFRamified` consumes for the real cover at one
finite pole-value centre `c`: the slit `Sset` accumulating at `c`, the per-preimage cluster data `Cl` on
the WHOLE-fibre `D = realFibreData …`, the residue-split / meromorphy bookkeeping, and the slit-wide
`FibreClusterTopology` family (the genuine §4 conservation-of-number + §5 normal-form geometry, built per
slit value by `FibreClusterTopology.ofClusterSplitData`).  **Not** asserted — it is the named target. -/

/-- **The precise per-centre cluster-family residual for the real cover** at a finite pole-value centre
`c`.  Bundles, for the WHOLE-fibre `D = realFibreData g hdiv c hnp`:

* `hnp` — every fibre preimage is a non-pole (true at a finite value-centre `coe c ≠ ∞`);
* `Sset`/`hS_acc` — a slit accumulating at `c` (the simply-connected punctured-disk-minus-a-ray where the
  `m`-th-root branches live);
* `hanalytic` — eventual off-centre analyticity of the geometric trace (the meromorphy input);
* `Cl`/`hmult`/`hsplit0` — per-preimage genuine §5 cluster data of matching `localDeg` multiplicity, with
  the residue split on `𝓝[≠] 0`;
* `ppord`/`hbnd` — a finite pole-order bound feeding the meromorphy;
* `hfam` — a slit-wide `FibreClusterTopology` family (the conservation-of-number geometry, `hcard = deg f`).

This is the genuine remaining content the `∑Res = 0` close needs at each centre; everything outside it
(the residue calculus, the off-centre/∞ machinery, the genericity `AdaptedFRamified`) is PROVEN. -/
structure RealCenterClusterFamily (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) (c : ℂ) where
  /-- Every fibre preimage over `coe c` is a non-pole (true at a finite value-centre). -/
  hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)
  /-- The eventual off-centre analyticity of the geometric trace. -/
  hanalytic : ∀ᶠ z in 𝓝[≠] c,
    AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv)) z
  /-- The slit on which the per-cluster branches are defined. -/
  Sset : Set ℂ
  /-- The slit accumulates at `c`. -/
  hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset
  /-- The per-preimage genuine §5 cluster data on the slit. -/
  Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset
  /-- The cluster multiplicity matches the genuine `localDeg` fibre multiplicity. -/
  hmult : ∀ i, (Cl i).m = (realFibreData g hdiv c hnp).mult i
  /-- The principal-part split of each straightened integrand on `𝓝[≠] 0`. -/
  hsplit0 : ∀ i, straightenedIntegrand ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) (Cl i).s
      =ᶠ[𝓝[≠] 0] fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u
  /-- The pole order of the geometric trace at `c`. -/
  ppord : ℕ
  /-- The finite pole-order bound feeding the meromorphy. -/
  hbnd : Tendsto (fun z => (z - c) ^ ppord *
    valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z) (𝓝[≠] c) (𝓝 0)
  /-- **The slit-wide conservation-of-number topology family** (the genuine §4/§5 geometry). -/
  hfam : ∀ z ∈ Sset,
    FibreClusterTopology (canonicalFibreSelection g.toFun f hdiv) (realFibreData g hdiv c hnp) Cl z

/-- **The SOUND per-centre residual `FullFibreCenterReindex` from a `RealCenterClusterFamily`.**  Feeds
the real-cover whole-fibre `D = realFibreData …`, the per-preimage cluster data, the meromorphy bound,
the slit, the pole surjectivity (automatic from the whole-fibre range), and the slit-wide
`FibreClusterTopology` family into `ofFibreClusterTopologyFamily_adaptedFRamified` (so `hnonpole` is
automatic from `A.hg_an_offpoles`).  **No `hD_mem` (no all-poles assumption)** — `D` is the whole fibre,
non-poles drop out at the residue level. -/
noncomputable def FullFibreCenterReindex.ofRealCenterClusterFamily {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles) {c : ℂ}
    (R : RealCenterClusterFamily ω₀ g A.hdiv poles c) :
    FullFibreCenterReindex ω₀ g.toFun A.f A.hdiv poles c :=
  FullFibreCenterReindex.ofFibreClusterTopologyFamily_adaptedFRamified A R.hanalytic
    (realFibreData g A.hdiv c R.hnp) (realFibreData_inj g A.hdiv c R.hnp)
    (realFibreData_surj g A.hdiv c R.hnp) R.hS_acc R.Cl R.hmult R.hsplit0 R.ppord R.hbnd R.hfam

/-- **Gate-A `∑Res = 0` from an `AdaptedFRamified` + per-centre `RealCenterClusterFamily`** (the SOUND
real-cover close, modulo the per-slit conservation-of-number geometry).  For a genuine meromorphic
numerator `g`, an `AdaptedFRamified` datum `A`, and at each finite pole-value centre `A.cs i` a
`RealCenterClusterFamily` (the slit + whole-fibre `D` + per-preimage §5 cluster data + slit-wide
`FibreClusterTopology` family), the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This anchors the precise remaining content of the residue theorem for the real cover to **exactly** the
per-centre `RealCenterClusterFamily` (and via `FibreClusterTopology.ofClusterSplitData`, the per-slit
§5 normal-form + §4 conservation-of-number facts).  The full-fibre-vs-pole inconsistency is resolved
(`D` is the WHOLE fibre, non-poles → residue `0`), and the genericity `AdaptedFRamified` is PROVEN. -/
theorem residueSum_eq_zero_of_realCenterClusterFamily {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles)
    (R : ∀ i, RealCenterClusterFamily ω₀ g A.hdiv poles (A.cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueSum_eq_zero_of_fullFibreReindex_adaptedFRamified A
    (fun i => FullFibreCenterReindex.ofRealCenterClusterFamily A (R i))

/-! ## Reducing the topology family to the §5/§4 per-slit-value primitives (`ofClusterSplitData`)

`FibreClusterTopology.ofClusterSplitData` is the documented *minimal-residual* constructor: it proves the
three conservation-of-number facts internally from the §5 / §4 geometric primitives.  For the real cover
the WHOLE-fibre fields it needs (`hD_inj`/`hrange`/`hnp`/`hmult_eq`) are already discharged by
`realFibreData` — in particular `hmult_eq` is *definitionally* `rfl` (the multiplicity *is*
`(localDeg …).toNat`).  So `hfam` reduces, per slit value `z`, to exactly the genuine §5 normal-form
section data + the sphere sheet-system regularity (the per-slit primitives).  We package this as a
per-slit-value bundle and reduce `RealCenterClusterFamily` to it. -/

/-- **The per-slit-value §5/§4 primitives** for the real cover at one regular slit value `z`, packaging
exactly the `FibreClusterTopology.ofClusterSplitData` inputs *not* already discharged by `realFibreData`:
the sphere sheet system regularity (`S`/`hderiv`/`hmero`/`hcoh`), the §5 section + non-pole facts
(`hcs_sec`/`hcs_np`), the within/cross-cluster distinctness (`hwithin`/`hcross`), the regular-value
fibre primitives (`hfin_z`/`hreg_z`), and the routine cluster-sheet residuals (`hsrc`/`hsheet_diff`).

`D := realFibreData g hdiv c hnp` discharges `hD_inj` (`realFibreData_inj`), `hrange`
(`realFibreData_range`), `hnp` (the carried fibre non-pole datum), and `hmult_eq` (`rfl`). -/
structure RealSlitClusterSplitData (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ) {Sset : Set ℂ}
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i))
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset) (z : ℂ) where
  /-- The sphere sheet system of `F = f.toRiemannSphere` at `coe z`. -/
  S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))
  /-- Regular-value: the chart-pullback derivative of `f.holoRepr` is nonzero at each sheet point. -/
  hderiv : ∀ k, deriv (fun w => f.holoRepr
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
    ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
      (S.sheet k (((z : ℂ) : RiemannSphere)))) ≠ 0
  /-- `g.toFun`'s chart-pullback is meromorphic at each sheet point. -/
  hmero : ∀ k, MeromorphicAt
    (fun w => g.toFun ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
    ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
      (S.sheet k (((z : ℂ) : RiemannSphere))))
  /-- The regular-value coherence (proven off-branch by `valueChartTrace_eq_sphereSheetFibreTrace`). -/
  hcoh : valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z
    = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z
  /-- The cluster section is a genuine local section of `f.holoRepr` near `z` (§5 normal form). -/
  hcs_sec : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
    ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection (realFibreData g hdiv c hnp) Cl i j w) = w
  /-- The cluster section is a non-pole at `z` (`0 ≤ orderAtPoint`). -/
  hcs_np : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
    0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp) Cl i j z)
  /-- Within-cluster injectivity at `z` (§5 straightening uniqueness). -/
  hwithin : ∀ (i : (realFibreData g hdiv c hnp).ι)
    (j k : Fin ((realFibreData g hdiv c hnp).mult i)),
    clusterSection (realFibreData g hdiv c hnp) Cl i j z
        = clusterSection (realFibreData g hdiv c hnp) Cl i k z → j = k
  /-- Cross-cluster separation at `z` (distinct preimages give disjoint clusters). -/
  hcross : ∀ (i i' : (realFibreData g hdiv c hnp).ι)
    (j : Fin ((realFibreData g hdiv c hnp).mult i)) (k : Fin ((realFibreData g hdiv c hnp).mult i')),
    i ≠ i' → clusterSection (realFibreData g hdiv c hnp) Cl i j z
      ≠ clusterSection (realFibreData g hdiv c hnp) Cl i' k z
  /-- The fibre over `coe z` is finite (regular value, off branch locus). -/
  hfin_z : (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).Finite
  /-- Each `coe z` preimage is an unramified (`localDeg = 1`) regular point. -/
  hreg_z : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
    localDeg f (((z : ℂ) : RiemannSphere)) x = 1
  /-- The cluster sheet value stays in the fixed preimage's chart target near `z`. -/
  hsrc : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
    ∀ᶠ w in 𝓝 z, clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w
      ∈ (chartAt ℂ ((realFibreData g hdiv c hnp).xs i)).target
  /-- The cluster sheet is differentiable at `z`. -/
  hsheet_diff : ∀ (i : (realFibreData g hdiv c hnp).ι)
    (j : Fin ((realFibreData g hdiv c hnp).mult i)),
    DifferentiableAt ℂ (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z

/-- **`FibreClusterTopology` from the per-slit-value primitives** (the real-cover instance of
`ofClusterSplitData`).  Feeds the `realFibreData`-discharged whole-fibre fields (`hD_inj`/`hrange`/`hnp`/
`hmult_eq = rfl`) and the carried per-slit primitives into `FibreClusterTopology.ofClusterSplitData`. -/
noncomputable def RealSlitClusterSplitData.toFibreClusterTopology {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {c : ℂ}
    {Sset : Set ℂ} {hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)}
    {Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset} {z : ℂ}
    (P : RealSlitClusterSplitData ω₀ g hdiv c hnp Cl z) :
    FibreClusterTopology (canonicalFibreSelection g.toFun f hdiv) (realFibreData g hdiv c hnp) Cl z :=
  FibreClusterTopology.ofClusterSplitData hdiv P.S P.hderiv P.hmero P.hcoh P.hcs_sec P.hcs_np
    P.hwithin P.hcross P.hfin_z P.hreg_z (realFibreData_inj g hdiv c hnp)
    (realFibreData_range g hdiv c hnp) hnp (fun _ => rfl) P.hsrc P.hsheet_diff

/-- **`RealCenterClusterFamily` from a slit-wide family of `RealSlitClusterSplitData`** (the §5/§4
per-slit-value reduction).  Replaces the abstract `hfam : FibreClusterTopology` family with the concrete
per-slit-value §5 normal-form section + sphere sheet-system primitives, each fed through
`ofClusterSplitData` (so the three conservation-of-number facts are proven internally and the
`realFibreData` whole-fibre fields are discharged automatically). -/
noncomputable def RealCenterClusterFamily.ofSlitClusterSplitFamily {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0}
    {poles : Finset X} {c : ℂ}
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i))
    (hanalytic : ∀ᶠ z in 𝓝[≠] c,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv)) z)
    {Sset : Set ℂ} (hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset)
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset)
    (hmult : ∀ i, (Cl i).m = (realFibreData g hdiv c hnp).mult i)
    (hsplit0 : ∀ i, straightenedIntegrand ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) (Cl i).s
        =ᶠ[𝓝[≠] 0] fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u)
    (ppord : ℕ)
    (hbnd : Tendsto (fun z => (z - c) ^ ppord *
      valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z) (𝓝[≠] c) (𝓝 0))
    (hfam : ∀ z ∈ Sset, RealSlitClusterSplitData ω₀ g hdiv c hnp Cl z) :
    RealCenterClusterFamily ω₀ g hdiv poles c where
  hnp := hnp
  hanalytic := hanalytic
  Sset := Sset
  hS_acc := hS_acc
  Cl := Cl
  hmult := hmult
  hsplit0 := hsplit0
  ppord := ppord
  hbnd := hbnd
  hfam := fun z hz => (hfam z hz).toFibreClusterTopology

/-! ## Building `Cl` at a real-cover fibre preimage (the per-preimage §5 cluster data)

The per-preimage `ClusterTraceData` `Cl i` is built from the Forster §5 normal form at the preimage
`p = D.xs i` (the local inverse `s = η⁻¹`, `exists_clusterSplit_at_fibrePoint`) and the `cpow` slit
branch `w₀ z = (z − c)^{1/m}`.  We supply a constructor that *derives* the mechanical pieces — the slit
branch `w₀` and its differential calculus, and the Laurent principal part of the straightened integrand
`H` at `0` (`exists_principalPart_meromorphicAt`) — leaving as the genuine remaining §5 analytic content
exactly the three slit-locality residuals: the sheet arguments land in `s`'s analyticity domain
(`hs_an_sheet`), the principal-part split holds at the sheet arguments (`hpp_split_sheet`), and the
single-valued analytic remainder trace `Rem` (the symmetric-function descent, `hRem_an`/`hRem_slit`). -/

/-- **`ClusterTraceData` at a real-cover fibre preimage from the §5 normal form** (the per-preimage
builder).  At a non-pole fibre preimage `p` over `coe c` of the cover `f` (`f.div ≠ 0`), with
`m := (localDeg f (coe c) p).toNat` the genuine multiplicity, `ζ` a primitive `m`-th root, the §5
local-inverse data `s`/`hs_an`/`hs0`/`hs_deriv` (from `exists_clusterSplit_at_fibrePoint`), the Laurent
principal-part data `ppN`/`ppb`/`ppR` of the straightened integrand at `0` (supplied by the caller via
`exists_principalPart_meromorphicAt`, exactly as `ofNormalForm` does), and the three genuine
slit-analytic residuals (`hs_an_sheet`, `hpp_split_sheet`, `Rem`/`hRem_an`/`hRem_slit`) on the standard
`cpow` slit `S = {z | z − c ∈ slitPlane}`, build the `ClusterTraceData`.

The value-add over `ofNormalForm` is that the multiplicity `m` is the genuine intrinsic `localDeg` (the
multiplicity bridge supplies `hm`, so `m` is *not* asserted) and the slit branch `w₀ z = (z − c)^{1/m}`
and its differential calculus are derived from the proven `clusterTraceData_slit` `cpow` data — so the
caller supplies only the `s`-data (from the §5 atom), the principal part, and the three slit residuals.
`hg_mero` is `g.meromorphic`.  This connects `exists_clusterSplit_at_fibrePoint` directly to a
`ClusterTraceData`, isolating the genuine §5 analytic content as exactly those three residuals. -/
noncomputable def ClusterTraceData.ofFibrePointNormalForm (ω₀ : HolomorphicOneForms X)
    (g : MeromorphicFunction X) {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {c : ℂ} {p : X} (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere))
    (hp_np : 0 ≤ f.orderAtPoint p)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat)
    (s : ℂ → ℂ) (hs_an : AnalyticAt ℂ s 0) (hs0 : s 0 = (chartAt ℂ p) p) (hs_deriv : deriv s 0 ≠ 0)
    (ppN : ℕ) (ppb : ℕ → ℂ) (ppR : ℂ → ℂ) (hppR_an : AnalyticAt ℂ ppR 0)
    (hs_an_sheet : ∀ z ∈ {z : ℂ | z - c ∈ slitPlane},
      ∀ j ∈ Finset.range (localDeg f ((c : ℂ) : RiemannSphere) p).toNat,
      AnalyticAt ℂ s (ζ ^ j * (clusterTraceData_slit ω₀ p c
        (localDeg f ((c : ℂ) : RiemannSphere) p).toNat
        ((Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1) ζ hζ).w₀ z))
    (hpp_split_sheet : ∀ z ∈ {z : ℂ | z - c ∈ slitPlane},
      ∀ j ∈ Finset.range (localDeg f ((c : ℂ) : RiemannSphere) p).toNat,
      straightenedIntegrand ω₀ g.toFun p s (ζ ^ j * (clusterTraceData_slit ω₀ p c
          (localDeg f ((c : ℂ) : RiemannSphere) p).toNat
          ((Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1) ζ hζ).w₀ z)
        = negTail 0 ppb ppN (ζ ^ j * (clusterTraceData_slit ω₀ p c
            (localDeg f ((c : ℂ) : RiemannSphere) p).toNat
            ((Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1) ζ hζ).w₀ z)
          + ppR (ζ ^ j * (clusterTraceData_slit ω₀ p c
            (localDeg f ((c : ℂ) : RiemannSphere) p).toNat
            ((Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1) ζ hζ).w₀ z))
    (Rem : ℂ → ℂ) (hRem_an : AnalyticAt ℂ Rem c)
    (hRem_slit : ∀ z ∈ {z : ℂ | z - c ∈ slitPlane},
      Rem z = ∑ j ∈ Finset.range (localDeg f ((c : ℂ) : RiemannSphere) p).toNat,
        ppR (ζ ^ j * (clusterTraceData_slit ω₀ p c
            (localDeg f ((c : ℂ) : RiemannSphere) p).toNat
            ((Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1) ζ hζ).w₀ z)
          * deriv (fun ζz => (0 : ℂ) + ζ ^ j * (clusterTraceData_slit ω₀ p c
            (localDeg f ((c : ℂ) : RiemannSphere) p).toNat
            ((Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1) ζ hζ).w₀ ζz) z) :
    ClusterTraceData ω₀ g.toFun p c {z : ℂ | z - c ∈ slitPlane} :=
  let m := (localDeg f ((c : ℂ) : RiemannSphere) p).toNat
  let hm : 0 < m := (Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1
  let W := clusterTraceData_slit ω₀ p c m hm ζ hζ
  ClusterTraceData.ofNormalForm ω₀ g.toFun p c {z : ℂ | z - c ∈ slitPlane} m hm ζ hζ
    s hs_an hs0 hs_deriv
    W.w₀ W.hw₀_ne W.hw₀_pow W.hw₀_deriv W.hw₀_diff hs_an_sheet
    (by simpa [Function.comp] using g.meromorphic p) ppN ppb ppR hppR_an
    hpp_split_sheet Rem hRem_an hRem_slit

/-! ## The single isolated remaining obligation + the conditional residue theorem

We package the per-centre cluster geometry, over **every** adapted cover, as a single named obligation
`RealCoverClusterGeometry`, and prove the residue theorem `∑Res = 0` from it together with the PROVEN
genericity `existsAdaptedFRamified`.  This exhibits the *precise* remaining content of the residue
theorem for the real cover as exactly one predicate: at each finite pole-value centre of a generic
adapted cover, the per-centre `RealCenterClusterFamily` (the slit + whole-fibre `D` + per-preimage §5
cluster data + slit-wide conservation-of-number `FibreClusterTopology`). -/

/-- **The single remaining obligation for the residue theorem (real-cover route).**  For *every*
adapted cover `A : AdaptedFRamified ω₀ g poles`, at each finite pole-value centre `A.cs i` the per-centre
`RealCenterClusterFamily` holds.  This is the genuine remaining §4/§5 geometric content; everything else
(the residue calculus, the off-centre/∞ machinery, the whole-fibre `D`, the genericity) is PROVEN.

**Soundness (non-false).**  A genuinely-achievable existential, not a disguised `False`: it is the
per-slit conservation-of-number geometry (Forster §4) + the §5 normal-form data, which hold for any
nonconstant cover at any finite value-centre (the slit branch exists for any multiplicity; the cluster
sheets are the genuine `m` regular sheets near each ramification preimage by `exists_clusterSplit` +
properness).  It is reducible — via `RealCenterClusterFamily.ofSlitClusterSplitFamily` and
`ClusterTraceData.ofFibrePointNormalForm` — to the per-slit-value §5/§4 primitives. -/
def RealCoverClusterGeometry (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X) : Type _ :=
  ∀ (A : AdaptedFRamified ω₀ g poles) (i : Fin A.m),
    RealCenterClusterFamily ω₀ g A.hdiv poles (A.cs i)

/-- **The 1-form residue theorem `∑Res = 0` for `α = ω₀·g`, modulo the per-centre real-cover cluster
geometry.**  For a genuine meromorphic numerator `g` and any finite `poles` containing the poles of
`α = ω₀·g` (off which `g` is analytic), the total residue vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`,

given the single obligation `RealCoverClusterGeometry` (the per-centre slit + whole-fibre §5 cluster data
+ conservation-of-number topology family).  The genericity `existsAdaptedFRamified` is PROVEN
(axiom-clean), so an adapted cover `A` is obtained for free; the obligation then supplies the per-centre
`RealCenterClusterFamily`, and `residueSum_eq_zero_of_realCenterClusterFamily` closes the sum.  This is
the SOUND well-definedness content underlying the global `Res : H¹(X,Ω) → ℂ` (Forster 17.3) → §17.5. -/
theorem residueTheorem_of_realCoverClusterGeometry (ω₀ : HolomorphicOneForms X)
    (g : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hgeom : RealCoverClusterGeometry ω₀ g poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 := by
  obtain ⟨A⟩ := existsAdaptedFRamified ω₀ g poles hpoles
  exact residueSum_eq_zero_of_realCenterClusterFamily A (fun i => hgeom A i)

/-! ## Non-vacuity: the obligation is satisfiable (no finite pole-value centres)

When an adapted cover has no finite pole-value centres (`A.m = 0`), the per-centre family is vacuously
satisfied, so `RealCoverClusterGeometry` is satisfiable in that case — confirming the obligation is
**not** a disguised `False`.  (For a nonconstant cover with no finite α-pole-value, e.g. all α-poles over
`∞`, this is the genuine `m = 0` situation.) -/

/-- **The residue theorem holds vacuously when every adapted cover has no finite pole-value centres.**
If, for every adapted cover `A`, `A.m = 0` (no finite pole-value centres), then `RealCoverClusterGeometry`
holds vacuously and `∑Res = 0` follows.  This confirms the obligation is satisfiable (not a disguised
`False`) in the `m = 0` regime. -/
theorem residueTheorem_of_realCover_no_finite_centres (ω₀ : HolomorphicOneForms X)
    (g : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hm0 : ∀ A : AdaptedFRamified ω₀ g poles, A.m = 0) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 := by
  refine residueTheorem_of_realCoverClusterGeometry ω₀ g poles hpoles (fun A i => ?_)
  rw [hm0 A] at i
  exact i.elim0

end Jacobians.Dolbeault.SerreResidueTheorem
