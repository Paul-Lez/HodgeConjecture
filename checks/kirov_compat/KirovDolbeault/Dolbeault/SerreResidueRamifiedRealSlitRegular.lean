/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealFibreFamily

/-!
# The regular-value primitives of the per-slit-value data for the real cover

`SerreResidueRamifiedRealFibreFamily.lean` reduced the per-centre `RealCenterClusterFamily` to a
slit-wide family of `RealSlitClusterSplitData` (one per regular slit value `z`), via
`RealCenterClusterFamily.ofSlitClusterSplitFamily` + `RealSlitClusterSplitData.toFibreClusterTopology`
(feeding `FibreClusterTopology.ofClusterSplitData`).  The fields of `RealSlitClusterSplitData` fall into
two groups:

* the **regular-value primitives** — the sphere sheet system `S` and its regularity `hderiv`/`hmero`,
  the coherence `hcoh`, and the conservation-of-number cover-degree readings `hfin_z`/`hreg_z`; these are
  GENUINELY mechanical at a value `z` *off the branch locus* (a regular value of the cover) and are
  discharged here from the proven atoms;
* the **§5 normal-form section facts** — `hcs_sec`/`hcs_np`/`hwithin`/`hcross`/`hsrc`/`hsheet_diff`; these
  are the genuine Forster §5 normal-form geometry (the cluster section is a `holoRepr`-section, distinct
  sheets give distinct points, distinct preimages give disjoint clusters), which remain as the precise
  isolated content.

This file discharges the regular-value primitives:

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`localDeg_eq_one_of_regular_fibrePoint`** — at an off-branch fibre point `y` over `coe z`
  (`f.toRiemannSphere y = coe z`) where the chart-pullback derivative of `f.toRiemannSphere` is nonzero,
  the intrinsic local degree is `1` (the regular-value content `hreg_z`).  Mirrors the genericity
  `orderAtPoint_sub_eq_one_of_regular_fibrePoint`, reading off `localDeg` instead of the shift's order.
* **`localDeg_eq_one_of_regularValueWitness`** — the same, packaged from a `RegularValueWitnessReg`
  whose chosen value is `coe z` (so the `is_regular` certificate supplies the deriv-nonzero), for every
  fibre point.  This is the per-value `hreg_z` from the regular-value witness.
* **`exists_regularSlitData`** — at a value `z` off the branch locus (with the regular-value witness,
  finite fibre, and the sphere sheet system + canonical-selection conditions), the regular-value tuple
  `(S, hderiv, hmero, hcoh, hfin_z, hreg_z)` consumed by `RealSlitClusterSplitData`.

## ⚠ Soundness

`z` is a REGULAR slit value (off the branch locus) — the cover is genuinely unramified there, so
`localDeg = 1` is TRUE (not asserted).  The sheet system is the genuine `exists_sphereSheetSystem`
off-branch datum; `hcoh` is the PROVEN `valueChartTrace_eq_sphereSheetFibreTrace` wired for the canonical
selection (the eventual canonical-fibre conditions are the proven `canonicalFibreSelection_hΦinjReg`/
`hΦrangeReg` + the sheet-system continuity).  No custom axiom; no unproved obligation on a false statement; no
false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (the cover is a covering off the branch locus).
* `SerreResidueGateAGenericity.lean` (`orderAtPoint_sub_eq_one_of_regular_fibrePoint`),
  `MultiplicityPatchingConstruct.lean` (`localDeg_coe_eq_chartPullback_order`),
  `Discharge/Manifold/Degree.lean` (`RegularValueWitnessReg`),
  `FormTraceBundleBridge.lean` (`valueChartTrace_eq_sphereSheetFibreTrace`),
  `FormTraceGlobalFibreSelection.lean` (`canonicalFibreSelection_hΦinjReg`/`hΦrangeReg`).
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
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct Jacobians.RiemannSphere
  Jacobians.MultiplicityPatchingConstruct Jacobians.ProperMapDegreeSheets

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## `localDeg = 1` at a regular fibre point (the `hreg_z` content) -/

/-- **A regular sphere-fibre point has local degree `1`** (the `hreg_z` content).  At a fibre point `y`
over `coe z` (`f.toRiemannSphere y = coe z`) where the chart-pullback derivative of `f.toRiemannSphere`
(read through the affine chart at `coe z`) is nonzero, the intrinsic local degree is `1`:

> `localDeg f (coe z) y = 1`.

This is the regular-value content: off the branch locus the cover is unramified.  The proof mirrors
`orderAtPoint_sub_eq_one_of_regular_fibrePoint`: `y` is a non-pole (its sphere value `coe z` is finite),
the geometric chart pullback `g = holoRepr ∘ chart⁻¹` has `g (chart y) = z` with nonzero derivative (the
deriv transfers from `chartCoe ∘ F ∘ chart⁻¹ =ᶠ g`), so `g − z` has a simple zero
(`analyticOrderAt_eq_one_of_zero_deriv_ne_zero`); `localDeg f (coe z) y` is that order
(`localDeg_coe_eq_chartPullback_order` ∘ `meromorphicOrderAt_holoRepr_sub_eq`). -/
theorem localDeg_eq_one_of_regular_fibrePoint (f : MeromorphicFunction X) {z : ℂ} {y : X}
    (hyval : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere))
    (hderiv : deriv ((chartAt ℂ (((z : ℂ) : RiemannSphere))) ∘ f.toRiemannSphere ∘
      (chartAt ℂ y).symm) ((chartAt ℂ y) y) ≠ 0) :
    localDeg f (((z : ℂ) : RiemannSphere)) y = 1 := by
  -- `y` is a non-pole (its sphere value `coe z` is finite).
  have hnp : 0 ≤ f.orderAtPoint y := by
    by_contra hpole
    rw [f.toRiemannSphere_of_pole (not_le.mp hpole)] at hyval
    exact (OnePoint.coe_ne_infty z) hyval.symm
  set φ := chartAt (H := ℂ) y with hφ
  have hchart_z : chartAt ℂ (((z : ℂ) : RiemannSphere)) = chartCoe := chartAt_coe z
  have hholo_y : f.holoRepr y = z := holoRepr_eq_of_fibre_nonpole f hyval hnp
  set g : ℂ → ℂ := fun w => f.holoRepr (φ.symm w) with hg
  have hg_an : AnalyticAt ℂ g (φ y) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  -- The deriv transfers from `chartCoe ∘ F ∘ chart⁻¹ =ᶠ g`.
  set G : ℂ → ℂ := chartCoe ∘ f.toRiemannSphere ∘ φ.symm with hG
  have hyt : φ y ∈ φ.target := φ.map_source (mem_chart_source ℂ y)
  have hGeq : G =ᶠ[𝓝 (φ y)] g := by
    have hsymm : Filter.Tendsto φ.symm (𝓝 (φ y)) (𝓝 y) := by
      have h := (φ.continuousAt_symm hyt).tendsto
      rwa [φ.left_inv (mem_chart_source ℂ y)] at h
    have hbase := (f.toRiemannSphere_eventuallyEq_coe_holoRepr hnp).comp_tendsto hsymm
    filter_upwards [hbase] with w hw
    show chartCoe (f.toRiemannSphere (φ.symm w)) = f.holoRepr (φ.symm w)
    rw [show f.toRiemannSphere (φ.symm w) = ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere) from hw,
      chartCoe_apply_coe]
  have hderiv_g : deriv g (φ y) ≠ 0 := by
    have heq : deriv G (φ y) = deriv g (φ y) := hGeq.deriv_eq
    rw [hchart_z] at hderiv
    rw [← heq]; exact hderiv
  have hg_y : g (φ y) = z := by
    show f.holoRepr (φ.symm (φ y)) = z
    rw [φ.left_inv (mem_chart_source ℂ y), hholo_y]
  -- `g − z` has a simple zero at `φ y`.
  have hgz_an : AnalyticAt ℂ (fun w => g w - z) (φ y) := hg_an.sub analyticAt_const
  have hgz0 : (fun w => g w - z) (φ y) = 0 := by simp [hg_y]
  have hgzd : deriv (fun w => g w - z) (φ y) ≠ 0 := by
    have hd : HasDerivAt (fun w => g w - z) (deriv g (φ y)) (φ y) := by
      simpa using (hg_an.differentiableAt.hasDerivAt).sub_const z
    rw [hd.deriv]; exact hderiv_g
  have hord1 : analyticOrderAt (fun w => g w - z) (φ y) = 1 :=
    hgz_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hgz0 hgzd
  -- `localDeg f (coe z) y` is that order.
  rw [localDeg_coe_eq_chartPullback_order f z φ (chart_mem_atlas ℂ y) (mem_chart_source ℂ y),
    ← meromorphicOrderAt_holoRepr_sub_eq f y z hyt,
    show (fun w => f.holoRepr (φ.symm w) - z) = (fun w => g w - z) from rfl,
    hgz_an.meromorphicOrderAt_eq, hord1]
  rfl

/-- **Every fibre point over an off-branch value has local degree `1`** (the `hreg_z` content, packaged
from `branchLocus`).  For a nonconstant cover `f` (`f.div ≠ 0`) and a value `z` off the branch locus
(`coe z ∉ branchLocus f.toRiemannSphere`), every preimage `x ∈ F⁻¹(coe z)` is unramified:

> `localDeg f (coe z) x = 1`.

The regular-value witness at `coe z` (`exists_regularValueWitnessReg_value_eq`, available off the
critical-value set = branch locus) supplies the chart-pullback-deriv-nonzero certificate at each fibre
point, and `localDeg_eq_one_of_regular_fibrePoint` reads off the local degree. -/
theorem localDeg_eq_one_of_notMem_branchLocus (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    {x : X} (hx : x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}) :
    localDeg f (((z : ℂ) : RiemannSphere)) x = 1 := by
  -- The regularity-certified witness at `coe z` (off the critical-value set = branch locus).
  obtain ⟨w, hw⟩ := Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq
    f.toRiemannSphere f.contMDiff_toRiemannSphere
    (Jacobians.ProperMapDegreeSheets.toRiemannSphere_not_isConstant_of_div_ne_zero f hdiv)
    -- `coe z ∉ branchLocus = coe z ∉ criticalValuesGeneral` (defeq: `branchLocus = f '' criticalSet`,
    -- `criticalSet = criticalSetGeneral`, `criticalValuesGeneral = f '' criticalSetGeneral`).
    (show (((z : ℂ) : RiemannSphere)) ∉
      Jacobians.Discharge.Manifold.criticalValuesGeneral f.toRiemannSphere from hz)
  -- The chart-pullback deriv ≠ 0 at the fibre point `x` (the witness's `is_regular`).
  have hxw : x ∈ f.toRiemannSphere ⁻¹' {w.toWitness.value} := by
    rw [hw]; exact hx
  have hderiv := w.is_regular x hxw
  rw [hw] at hderiv
  have hxval : f.toRiemannSphere x = (((z : ℂ) : RiemannSphere)) := by
    simpa using hx
  exact localDeg_eq_one_of_regular_fibrePoint f hxval hderiv

/-- **The regular-fibre primitives `hfin_z`/`hreg_z` at an off-branch value.**  For a nonconstant cover
`f` and a value `z` off the branch locus, the fibre over `coe z` is finite and every local degree there
is `1` — exactly the two regular-fibre inputs (`hfin_z`, `hreg_z`) of `RealSlitClusterSplitData` /
`FibreClusterTopology.ofClusterSplitData`. -/
theorem regularFibre_primitives_of_notMem_branchLocus (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere) :
    (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).Finite ∧
      ∀ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
        localDeg f (((z : ℂ) : RiemannSphere)) x = 1 :=
  ⟨Jacobians.ProperMapDegreeSheets.fibre_finite_of_div_ne_zero f hdiv _,
    fun _ hx => localDeg_eq_one_of_notMem_branchLocus f hdiv hz hx⟩

/-! ## The sheet-system regularity `hderiv`/`hmero` (from a sphere sheet system off the branch locus) -/

/-- **`hderiv` for a sphere sheet system off the branch locus.**  For a nonconstant cover `f` and a
value `z` off the branch locus, with `S` a sphere sheet system of `F = f.toRiemannSphere` at `coe z`,
every sheet point `S.sheet k (coe z)` is a regular point of `f`: the chart-pullback derivative of
`f.holoRepr` there is nonzero.  Each sheet point has sphere value `coe z` (`sheet_section` at the base
`coe z ∈ S.V`), off the branch locus, so `sheet_holoRepr_deriv_ne_zero` applies. -/
theorem sphereSheet_hderiv (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) :
    ∀ k, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))) ≠ 0 := fun k =>
  sheet_holoRepr_deriv_ne_zero f hdiv hz (S.sheet_section k _ S.mem_V)

/-- **`hmero` for a sphere sheet system from a genuine meromorphic numerator.**  For `g :
MeromorphicFunction X` and a sphere sheet system `S`, `g.toFun`'s chart pullback is meromorphic at every
sheet point (`g.meromorphic`). -/
theorem sphereSheet_hmero (g : MeromorphicFunction X) {f : MeromorphicFunction X} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) :
    ∀ k, MeromorphicAt
      (fun w => g.toFun ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))) := fun _k => g.meromorphic _

/-! ## The eventual sheet-system conditions `hsheetInj`/`hsheetMem` (near a value `z`) -/

/-- **`hsheetInj` near `z` from a sphere sheet system.**  The sheets are injective on `S.V` (a
neighbourhood of `coe z`), so they are injective at every `coe b'` for `b'` near `z` (pull back `S.V`
along the continuous `coe`). -/
theorem sphereSheet_hsheetInj {f : MeromorphicFunction X} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) :
    ∀ᶠ b' in 𝓝 z, Function.Injective (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))) := by
  have hVnhds : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) ∈ 𝓝 z :=
    (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (S.isOpen_V.mem_nhds S.mem_V)
  filter_upwards [hVnhds] with b' hb'
  exact S.sheet_inj (((b' : ℂ) : RiemannSphere)) hb'

/-- **`hsheetMem` near `z` from a sphere sheet system.**  Each sheet `b' ↦ S.sheet i (coe b')` is
continuous at `z` (the moving section `holoReprSheet i` is `ContMDiffAt`), so it stays in the chart
source of `S.sheet i (coe z)` for `b'` near `z`. -/
theorem sphereSheet_hsheetMem {f : MeromorphicFunction X} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) :
    ∀ᶠ b' in 𝓝 z, ∀ i, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
      (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).source := by
  have hev : ∀ i : Fin S.n, ∀ᶠ b' in 𝓝 z,
      S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).source := by
    intro i
    have hcont : ContinuousAt (S.holoReprSheet i) z := (S.holoReprSheet_contMDiffAt i).continuousAt
    have hsrc : (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).source ∈
        𝓝 (S.sheet i (((z : ℂ) : RiemannSphere))) :=
      (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).open_source.mem_nhds (mem_chart_source ℂ _)
    have := hcont.preimage_mem_nhds (show
      (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).source ∈ 𝓝 (S.holoReprSheet i z) from hsrc)
    filter_upwards [this] with b' hb' using hb'
  rw [eventually_all]; exact hev

/-! ## The regular-value coherence `hcoh` for the canonical selection -/

/-- **The regular-value coherence `hcoh` for the canonical full-fibre selection.**  At a value `z` off
the branch locus, with a sphere sheet system `S` of `F = f.toRiemannSphere` at `coe z`, the geometric
trace of the canonical selection equals the sphere-sheet fibre trace:

> `valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z
>    = (fibreTrace ω₀ f (ofSphereSheetSystem S (sphereSheet_hderiv …) (sphereSheet_hmero …))).traceCoeff z`.

This is the PROVEN `valueChartTrace_eq_sphereSheetFibreTrace`, wired for the canonical selection: the
sheet regularity is `sphereSheet_hderiv`/`sphereSheet_hmero`, the canonical-fibre conditions are
`canonicalFibreSelection_hΦinjReg`/`hΦrangeReg` (the `g`-meromorphy is `g.meromorphic`, free), and the
sheet-system conditions are `sphereSheet_hsheetInj`/`sphereSheet_hsheetMem`. -/
theorem canonicalSelection_hcoh (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) :
    valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z
      = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S
          (sphereSheet_hderiv f hdiv hz S) (sphereSheet_hmero g S))).traceCoeff z := by
  -- The `g`-meromorphy near `z` (free from `g.meromorphic`), feeding the canonical-fibre conditions.
  have hgmero : ∀ᶠ b' in 𝓝 z, ∀ i,
      MeromorphicAt (fun w => g.toFun ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i)) :=
    Filter.Eventually.of_forall (fun b' i => g.meromorphic _)
  exact valueChartTrace_eq_sphereSheetFibreTrace ω₀ g.toFun f
    (canonicalFibreSelection g.toFun f hdiv) S (sphereSheet_hderiv f hdiv hz S)
    (sphereSheet_hmero g S)
    (canonicalFibreSelection_hΦinjReg g.toFun f hdiv hz hgmero)
    (canonicalFibreSelection_hΦrangeReg g.toFun f hdiv hz hgmero)
    (sphereSheet_hsheetInj S) (sphereSheet_hsheetMem S)

/-! ## Assembling `RealSlitClusterSplitData` from the sheet system + the §5 section facts

We package the per-slit-value builder: at a regular slit value `z` (off the branch locus), the
regular-value primitives (`hderiv`/`hmero`/`hcoh`/`hfin_z`/`hreg_z`) are discharged from the proven
atoms above, so `RealSlitClusterSplitData` reduces to **exactly** the sphere sheet system `S` and the §5
normal-form section facts (`hcs_sec`/`hcs_np`/`hwithin`/`hcross`/`hsrc`/`hsheet_diff`). -/

/-- **`RealSlitClusterSplitData` from the sheet system + the §5 section facts.**  At a regular slit value
`z` off the branch locus *on the slit* `Sset` (`hz_slit`), given a sphere sheet system `S` of `F =
f.toRiemannSphere` at `coe z` and the §5 normal-form section facts for the cluster data `Cl` (whose
multiplicity matches the fibre's, `hmult`), build the `RealSlitClusterSplitData`.  The regular-value
primitives are discharged: `hderiv` (`sphereSheet_hderiv`), `hmero` (`sphereSheet_hmero`), `hcoh`
(`canonicalSelection_hcoh`), and `hfin_z`/`hreg_z` (`regularFibre_primitives_of_notMem_branchLocus`).
The cluster-sheet differentiability `hsheet_diff` is also discharged from the `Cl` slit fields
(`hw₀_diff`/`hs_an_sheet`, via `clusterSheet_differentiableAt`).  Only the genuine §5 normal-form geometry
(the section property `hcs_sec`/`hcs_np`, the distinctness `hwithin`/`hcross`, and the chart-target
locality `hsrc`) remains as input — the precise isolated content. -/
noncomputable def RealSlitClusterSplitData.ofRegularValue {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {c : ℂ}
    {Sset : Set ℂ} {hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)}
    {Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset} {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere) (hz_slit : z ∈ Sset)
    (hmult : ∀ i, (Cl i).m = (realFibreData g hdiv c hnp).mult i)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hcs_sec : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
      ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection (realFibreData g hdiv c hnp) Cl i j w) = w)
    (hcs_np : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
      0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp) Cl i j z))
    (hwithin : ∀ (i : (realFibreData g hdiv c hnp).ι)
      (j k : Fin ((realFibreData g hdiv c hnp).mult i)),
      clusterSection (realFibreData g hdiv c hnp) Cl i j z
          = clusterSection (realFibreData g hdiv c hnp) Cl i k z → j = k)
    (hcross : ∀ (i i' : (realFibreData g hdiv c hnp).ι)
      (j : Fin ((realFibreData g hdiv c hnp).mult i)) (k : Fin ((realFibreData g hdiv c hnp).mult i')),
      i ≠ i' → clusterSection (realFibreData g hdiv c hnp) Cl i j z
        ≠ clusterSection (realFibreData g hdiv c hnp) Cl i' k z)
    (hsrc : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
      ∀ᶠ w in 𝓝 z, clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w
        ∈ (chartAt ℂ ((realFibreData g hdiv c hnp).xs i)).target) :
    RealSlitClusterSplitData ω₀ g hdiv c hnp Cl z where
  S := S
  hderiv := sphereSheet_hderiv f hdiv hz S
  hmero := sphereSheet_hmero g S
  hcoh := canonicalSelection_hcoh ω₀ g hdiv hz S
  hcs_sec := hcs_sec
  hcs_np := hcs_np
  hwithin := hwithin
  hcross := hcross
  hfin_z := (regularFibre_primitives_of_notMem_branchLocus f hdiv hz).1
  hreg_z := (regularFibre_primitives_of_notMem_branchLocus f hdiv hz).2
  hsrc := hsrc
  hsheet_diff := fun i j => by
    -- The cluster sheet `s(ζʲ·w₀ z)` is differentiable: `w₀` differentiable on the slit (`hw₀_diff`)
    -- and `s` analytic at the sheet argument `ζʲ·w₀ z` (`hs_an_sheet`, `j < (Cl i).m`).
    refine clusterSheet_differentiableAt ?_ ((Cl i).hw₀_diff z hz_slit)
    refine (Cl i).hs_an_sheet z hz_slit (j : ℕ) ?_
    rw [Finset.mem_range, hmult i]; exact j.isLt

end Jacobians.Dolbeault.SerreResidueTheorem
