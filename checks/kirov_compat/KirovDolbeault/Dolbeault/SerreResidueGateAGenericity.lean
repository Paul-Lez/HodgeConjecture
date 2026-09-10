/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueGateAInftyBuilder
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealCover
import KirovDolbeault.Discharge.Manifold.RegularValueExistsRegUnconditional

/-!
# Gate-A TARGET 2: the off-centre/∞ genericity selection `ExistsAdaptedFRamified` (Miranda §VIII.3)

`Jacobians.Dolbeault.SerreResidueTheorem.ExistsAdaptedFRamified ω₀ g poles`
(`SerreResidueGateAInftyBuilder.lean`) is the `hoff_cs`-free off-centre/∞ genericity *input* of the
ramified Gate-A residue route: it asks for a single nonconstant cover `f` with **simple `∞`-poles** and
the finite pole-value enumeration, *admitting ramified finite pole fibres* (which the cluster route,
TARGET 1, handles).  Miranda §VIII.3, p. 254 ("simply choose *any* nonconstant `f`") + the standard
generic-position adjustment makes it genuinely achievable; this file **proves it directly** via the
reciprocal-cover construction, with NO Riemann–Roch-with-prescribed-jets (which the book never needs).

## The construction (generic position; reciprocal of a shift at a regular value)

Take the nonconstant meromorphic `f₀` of `exists_nonconstant_meromorphic` (the Riemann inequality,
Serre-independent — `SerreOmega0.lean`).  Pick a *finite regular value* `a : ℂ` of the sphere map
`f₀.toRiemannSphere`, i.e. `coe a ∉ branchLocus = criticalValuesGeneral f₀.toRiemannSphere` (the
critical values are FINITE for a nonconstant `f₀`, and `coe '' ℂ` is cofinite, so such `a` exists).
Set the cover to the reciprocal of the shift:

> `f := (f₀ − a·1)⁻¹`.

* **Nonconstant (`hdiv : f.div ≠ 0`).** `f₀ − a·1` is nonconstant (else `f₀` would be germ-constant),
  hence its reciprocal is nonconstant (`orderAtPoint_inv`).
* **Simple `∞`-poles (`hsimpleInf`).** The poles of `f` are the zeros of `f₀ − a·1`
  (`orderAtPoint_inv`).  A zero `y` of `f₀ − a·1` is a preimage of `coe a` under `f₀.toRiemannSphere`
  (where `f₀` is a non-pole with `holoRepr = a`); since `coe a` is a regular value, the chart pullback of
  `f₀.toRiemannSphere` has nonzero derivative at `y`, so the zero is **simple**
  (`analyticOrderAt … = 1`), i.e. `(f₀ − a·1).orderAtPoint y = 1`, whence `f.orderAtPoint y = −1`.
* **Pole-value enumeration (`cs`/`hcenters_cs`).** The finite set
  `(poles.image f.toRiemannSphere).erase ∞` of finite pole-values of `α = ω₀·g` is enumerated by pulling
  back along the affine chart `chartCoe : RiemannSphere → ℂ` (a section of `coe` off `∞`).
* **`hg_an_offpoles`.** Supplied as the defining hypothesis of `poles` (off `poles`, `g` is analytic).

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `MeromorphicFunction.div_ne_zero_of_not_isGermConstant` — nonconstant ⟹ `div ≠ 0` (compact Liouville).
* `exists_finite_regularValue` — a finite regular value of `f₀.toRiemannSphere` exists.
* `orderAtPoint_sub_eq_one_of_regular_fibrePoint` — the genericity heart: a regular sphere-fibre point is
  a simple zero of `f₀ − a·1`.
* `toRiemannSphere_eq_coe_of_sub_orderPos` — a zero of `f₀ − a·1` is a preimage of `coe a`.
* `adaptedFRamified_of_regularValue` — **the `AdaptedFRamified` builder** from a finite regular value.
* `existsAdaptedFRamified` — **TARGET 2**, fully proven: `ExistsAdaptedFRamified ω₀ g poles` holds for
  every `ω₀`, genuine meromorphic `g`, and finite `poles`.

## ⚠ Soundness

Every genericity field is GENUINELY satisfied by the constructed `f := (f₀ − a·1)⁻¹`: no custom axiom, no
unproved obligations on false statements, no false/junk/circular field, no Riemann–Roch (the construction is
generic-position only — Miranda's "choose any nonconstant `f`" + a regular-value shift).  `hsimpleInf` is
achieved for the *general* `f₀` by the reciprocal-at-a-regular-value trick, verified end-to-end here.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, p. 254 ("choose any nonconstant `f`").
* `Jacobians/Dolbeault/SerreOmega0.lean` (`exists_nonconstant_meromorphic`),
  `SerreResidueRamifiedRealCover.lean` (`MeromorphicFunction.Inv`, `orderAtPoint_inv`),
  `Discharge/Manifold/RegularValueExistsRegUnconditional.lean`
  (`exists_regularValueWitnessReg_value_eq`),
  `Discharge/Manifold/CriticalSetDerivBridge.lean`.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

open Jacobians Jacobians.Dolbeault Jacobians.RiemannSphere

namespace Jacobians.Dolbeault.SerreResidueTheorem

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Nonconstant ⟹ `div ≠ 0` (compact Liouville) -/

/-- **A non-germ-constant meromorphic function has nontrivial divisor.**  If `f.div = 0` then every
order is `0`, so `f ∈ L(0)`, so `f` is germ-constant by the repo Liouville
`germ_eq_const_of_mem_linearSystem_zero` — contradiction.  (This is the bridge from the existence
output `¬ IsGermConstant f` to the cover hypothesis `f.div ≠ 0`.) -/
theorem div_ne_zero_of_not_isGermConstant (f : MeromorphicFunction X)
    (hf : ¬ IsGermConstant f) : (f.div : Divisor X) ≠ 0 := by
  intro hdiv
  apply hf
  have hmem : f ∈ linearSystem (X := X) 0 := by
    intro x
    have hord : f.orderAtPoint x = 0 := by
      have := congrFun (congrArg (DFunLike.coe) hdiv) x
      simpa [div_apply] using this
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    refine untop₀_nonneg_iff.mp ?_
    show (0 : ℤ) ≤ f.orderAtPoint x
    rw [hord]
  exact germ_eq_const_of_mem_linearSystem_zero f hmem

/-- **The shift `f₀ − a·1` is nonconstant when `f₀` is.**  If `f₀ − a·1` were germ-constant `= c`, then
`f₀` would be germ-constant `= c + a`.  Hence `(f₀ − a·1).div ≠ 0`. -/
theorem div_sub_smul_ne_zero_of_not_isGermConstant (f₀ : MeromorphicFunction X)
    (hf₀ : ¬ IsGermConstant f₀) (a : ℂ) :
    ((f₀ - a • (constOneMero (X := X))).div : Divisor X) ≠ 0 := by
  refine div_ne_zero_of_not_isGermConstant _ ?_
  rintro ⟨c, hc⟩
  apply hf₀
  refine ⟨c + a, fun x => ?_⟩
  filter_upwards [hc x] with z hz
  have hz' : (f₀ - a • (constOneMero (X := X))).toFun z = c := hz
  simp only [MeromorphicFunction.sub_toFun, MeromorphicFunction.smul_toFun, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, constOneMero] at hz'
  linear_combination hz'

/-! ## Existence of a finite regular value -/

/-- **A finite regular value of `f₀.toRiemannSphere` exists.**  Its critical values are finite (for a
nonconstant `f₀`); pulling back along the injection `coe : ℂ → RiemannSphere` keeps them finite, and `ℂ`
is infinite — so a finite `a` with `coe a ∉ criticalValuesGeneral f₀.toRiemannSphere` exists. -/
theorem exists_finite_regularValue (f₀ : MeromorphicFunction X)
    (hdiv : (f₀.div : Divisor X) ≠ 0) :
    ∃ a : ℂ, ((a : ℂ) : RiemannSphere) ∉
      Jacobians.Discharge.Manifold.criticalValuesGeneral f₀.toRiemannSphere := by
  have hcv_fin : (Jacobians.Discharge.Manifold.criticalValuesGeneral f₀.toRiemannSphere).Finite :=
    Jacobians.Discharge.Manifold.criticalValues_finite_general f₀.toRiemannSphere
      f₀.contMDiff_toRiemannSphere
      (Jacobians.ProperMapDegreeSheets.toRiemannSphere_not_isConstant_of_div_ne_zero f₀ hdiv)
  have hpre_fin : ((fun z : ℂ => ((z : ℂ) : RiemannSphere)) ⁻¹'
      (Jacobians.Discharge.Manifold.criticalValuesGeneral f₀.toRiemannSphere)).Finite :=
    hcv_fin.preimage ((OnePoint.coe_injective (X := ℂ)).injOn)
  obtain ⟨a, ha⟩ := ((Set.infinite_univ (α := ℂ)).diff hpre_fin).nonempty
  exact ⟨a, ha.2⟩

/-! ## The genericity heart: a regular sphere-fibre point is a simple zero of `f₀ − a·1` -/

/-- **A zero of `f₀ − a·1` is a preimage of `coe a`.**  If `f₀ − a·1` has *positive* order at `y`, then
`f₀.toFun → a` on the punctured neighbourhood, so `f₀` is a *non-pole* at `y` with `holoRepr y = a`,
hence `f₀.toRiemannSphere y = coe a`. -/
theorem toRiemannSphere_eq_coe_of_sub_orderPos (f₀ : MeromorphicFunction X) (a : ℂ) {y : X}
    (hy : 0 < (f₀ - a • (constOneMero (X := X))).orderAtPoint y) :
    f₀.toRiemannSphere y = ((a : ℂ) : RiemannSphere) := by
  set h := f₀ - a • (constOneMero (X := X)) with hh
  set φ := chartAt (H := ℂ) y with hφ
  have hxsrc : y ∈ φ.source := mem_chart_source ℂ y
  have htoFun_h : h.toFun = fun x => f₀.toFun x - a := by
    funext x
    simp [hh, MeromorphicFunction.sub_toFun, MeromorphicFunction.smul_toFun, constOneMero]
  -- h.toFun → 0 along 𝓝[≠] y (positive order).
  have hHlim : Filter.Tendsto h.toFun (𝓝[≠] y) (𝓝 0) := by
    set F := h.toFun ∘ φ.symm with hFdef
    have hordF : meromorphicOrderAt F (φ y) = (h.orderAtPoint y : ℤ) :=
      h.meromorphicOrderAt_chartPullback_of_zero hy
    have hordpos : 0 < meromorphicOrderAt F (φ y) := by rw [hordF]; exact_mod_cast hy
    have hFlim : Filter.Tendsto F (𝓝[≠] (φ y)) (𝓝 0) :=
      tendsto_zero_of_meromorphicOrderAt_pos hordpos
    have hfwd : Filter.Tendsto φ (𝓝[≠] y) (𝓝[≠] (φ y)) := φ.tendsto_nhdsNE hxsrc
    have hcomp : Filter.Tendsto (F ∘ φ) (𝓝[≠] y) (𝓝 0) := hFlim.comp hfwd
    refine hcomp.congr' ?_
    have hev : ∀ᶠ x in 𝓝 y, x ∈ φ.source := φ.open_source.mem_nhds hxsrc
    filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with x hx
    simp [hFdef, Function.comp, φ.left_inv hx]
  -- f₀.toFun → a (since f₀.toFun = h.toFun + a).
  have hF₀lim : Filter.Tendsto f₀.toFun (𝓝[≠] y) (𝓝 a) := by
    have heq : f₀.toFun = fun x => h.toFun x + a := by rw [htoFun_h]; funext x; ring
    rw [heq]; simpa using hHlim.add_const a
  haveI : (𝓝[≠] y).NeBot := by
    have htsymm : Filter.Tendsto φ.symm (𝓝[≠] (φ y)) (𝓝[≠] y) := by
      have := φ.symm.tendsto_nhdsNE (x := φ y) (by simpa using φ.map_source hxsrc)
      simpa [φ.left_inv hxsrc] using this
    exact htsymm.neBot
  have hholo : f₀.holoRepr y = a := by
    show Filter.limUnder (𝓝[≠] y) f₀.toFun = a
    exact hF₀lim.limUnder_eq
  -- f₀ non-pole at y: orderAtPoint f₀ y ≥ 0, algebraically from `f₀ = h + a·1`.
  have hnp_f₀ : 0 ≤ f₀.orderAtPoint y := by
    have hf₀_eq : f₀ = h + a • (constOneMero (X := X)) := by rw [hh]; abel
    have hordW_h : (0 : WithTop ℤ) ≤ h.orderW y :=
      untop₀_nonneg_iff.mp (le_of_lt hy)
    have hordW_const : (0 : WithTop ℤ) ≤ (a • (constOneMero (X := X))).orderW y := by
      rcases eq_or_ne a 0 with rfl | ha
      · rw [show (0 : ℂ) • (constOneMero (X := X)) = 0 from by simp,
          MeromorphicFunction.orderW_zero]
        exact le_top
      · rw [show (a • (constOneMero (X := X))).orderW y = (constOneMero (X := X)).orderW y from
          meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using ha),
          constOneMero_orderW]
    have hadd : min (h.orderW y) ((a • (constOneMero (X := X))).orderW y) ≤ f₀.orderW y := by
      conv_rhs => rw [hf₀_eq]
      exact meromorphicOrderAt_add (h.meromorphic y) ((a • (constOneMero (X := X))).meromorphic y)
    have hf₀W : (0 : WithTop ℤ) ≤ f₀.orderW y := (le_min hordW_h hordW_const).trans hadd
    show (0 : ℤ) ≤ (f₀.orderW y).untop₀
    exact untop₀_nonneg_iff.mpr hf₀W
  rw [f₀.toRiemannSphere_of_nonneg hnp_f₀, hholo]

/-- **A regular sphere-fibre point is a simple zero of `f₀ − a·1`** (the genericity heart).  At a
non-pole `y` with `f₀.toRiemannSphere y = coe a`, if the chart pullback of `f₀.toRiemannSphere` has
nonzero derivative at `chart y` (the regularity certificate), then `(f₀ − a·1).orderAtPoint y = 1`.
Routes through: the sphere-chart pullback `chartCoe ∘ F ∘ chart⁻¹ =ᶠ holoRepr ∘ chart⁻¹`, so the deriv
transfers; `analyticOrderAt_eq_one_of_zero_deriv_ne_zero`; and `meromorphicOrderAt_holoRepr_sub_eq`. -/
theorem orderAtPoint_sub_eq_one_of_regular_fibrePoint (f₀ : MeromorphicFunction X) (a : ℂ) {y : X}
    (hyval : f₀.toRiemannSphere y = ((a : ℂ) : RiemannSphere))
    (hderiv : deriv ((chartAt ℂ (((a : ℂ) : RiemannSphere))) ∘ f₀.toRiemannSphere ∘
      (chartAt ℂ y).symm) ((chartAt ℂ y) y) ≠ 0) :
    (f₀ - a • (constOneMero (X := X))).orderAtPoint y = 1 := by
  have hnp : 0 ≤ f₀.orderAtPoint y := by
    by_contra hpole
    rw [f₀.toRiemannSphere_of_pole (not_le.mp hpole)] at hyval
    exact (OnePoint.coe_ne_infty a) hyval.symm
  set φ := chartAt (H := ℂ) y with hφ
  have hchart_a : chartAt ℂ (((a : ℂ) : RiemannSphere)) = chartCoe := chartAt_coe a
  have hholo_y : f₀.holoRepr y = a := by
    have := f₀.toRiemannSphere_of_nonneg hnp
    rw [hyval] at this
    exact (OnePoint.coe_injective this.symm)
  set g : ℂ → ℂ := fun w => f₀.holoRepr (φ.symm w) with hg
  have hg_an : AnalyticAt ℂ g (φ y) :=
    f₀.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  set G : ℂ → ℂ := chartCoe ∘ f₀.toRiemannSphere ∘ φ.symm with hG
  have hyt : φ y ∈ φ.target := φ.map_source (mem_chart_source ℂ y)
  have hGeq : G =ᶠ[𝓝 (φ y)] g := by
    have hsymm : Filter.Tendsto φ.symm (𝓝 (φ y)) (𝓝 y) := by
      have h := (φ.continuousAt_symm hyt).tendsto
      rwa [φ.left_inv (mem_chart_source ℂ y)] at h
    have hbase := (f₀.toRiemannSphere_eventuallyEq_coe_holoRepr hnp).comp_tendsto hsymm
    filter_upwards [hbase] with w hw
    show chartCoe (f₀.toRiemannSphere (φ.symm w)) = f₀.holoRepr (φ.symm w)
    rw [show f₀.toRiemannSphere (φ.symm w) = ((f₀.holoRepr (φ.symm w) : ℂ) : RiemannSphere) from hw,
      chartCoe_apply_coe]
  have hderiv_g : deriv g (φ y) ≠ 0 := by
    have heq : deriv G (φ y) = deriv g (φ y) := hGeq.deriv_eq
    rw [hchart_a] at hderiv
    rw [← heq]; exact hderiv
  have hg_y : g (φ y) = a := by
    show f₀.holoRepr (φ.symm (φ y)) = a
    rw [φ.left_inv (mem_chart_source ℂ y), hholo_y]
  have hga_an : AnalyticAt ℂ (fun w => g w - a) (φ y) := hg_an.sub analyticAt_const
  have hga0 : (fun w => g w - a) (φ y) = 0 := by simp [hg_y]
  have hgad : deriv (fun w => g w - a) (φ y) ≠ 0 := by
    have hd : HasDerivAt (fun w => g w - a) (deriv g (φ y)) (φ y) := by
      simpa using (hg_an.differentiableAt.hasDerivAt).sub_const a
    rw [hd.deriv]; exact hderiv_g
  have hord1 : analyticOrderAt (fun w => g w - a) (φ y) = 1 :=
    hga_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hga0 hgad
  have htoFun : (f₀ - a • (constOneMero (X := X))).orderAtPoint y
      = (meromorphicOrderAt (fun w => f₀.toFun (φ.symm w) - a) (φ y)).untop₀ := by
    show (meromorphicOrderAt ((f₀ - a • (constOneMero (X := X))).toFun ∘ φ.symm) (φ y)).untop₀ = _
    congr 1
    apply meromorphicOrderAt_congr
    filter_upwards with w
    show (f₀ - a • (constOneMero (X := X))).toFun (φ.symm w) = f₀.toFun (φ.symm w) - a
    simp [MeromorphicFunction.sub_toFun, MeromorphicFunction.smul_toFun, constOneMero]
  rw [htoFun, ← Jacobians.ProperMapDegreeSheets.meromorphicOrderAt_holoRepr_sub_eq f₀ y a hyt]
  show (meromorphicOrderAt (fun w => g w - a) (φ y)).untop₀ = 1
  rw [hga_an.meromorphicOrderAt_eq, hord1]
  rfl

/-! ## The `AdaptedFRamified` builder from a finite regular value -/

/-- **The cover `f := (f₀ − a·1)⁻¹` has all poles simple, given a finite regular value `a`.**  A pole
`y` of `f` (`f.orderAtPoint y < 0`) corresponds (via `orderAtPoint_inv`) to a zero of `f₀ − a·1`
(`(f₀ − a·1).orderAtPoint y > 0`), which is a preimage of `coe a` (`toRiemannSphere_eq_coe_of_sub_orderPos`);
since `coe a` is a regular value, that zero is simple
(`orderAtPoint_sub_eq_one_of_regular_fibrePoint`), so `f.orderAtPoint y = −1`. -/
theorem orderAtPoint_inv_eq_neg_one_of_regularValue (f₀ : MeromorphicFunction X)
    (hdiv : (f₀.div : Divisor X) ≠ 0) (a : ℂ)
    (ha : ((a : ℂ) : RiemannSphere) ∉
      Jacobians.Discharge.Manifold.criticalValuesGeneral f₀.toRiemannSphere)
    {y : X} (hy : ((f₀ - a • (constOneMero (X := X)))⁻¹).orderAtPoint y < 0) :
    ((f₀ - a • (constOneMero (X := X)))⁻¹).orderAtPoint y = -1 := by
  -- The zero of `f₀ − a·1` underlying the pole `y` of the reciprocal.
  have hzero : 0 < (f₀ - a • (constOneMero (X := X))).orderAtPoint y := by
    have heq := MeromorphicFunction.orderAtPoint_inv (f₀ - a • (constOneMero (X := X))) y
    rw [heq] at hy; omega
  -- `y` is a preimage of `coe a`.
  have hyval : f₀.toRiemannSphere y = ((a : ℂ) : RiemannSphere) :=
    toRiemannSphere_eq_coe_of_sub_orderPos f₀ a hzero
  -- The regularity-certified witness at the chosen value `coe a` (off the critical-value set).
  obtain ⟨w, hw⟩ := Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq
    f₀.toRiemannSphere f₀.contMDiff_toRiemannSphere
    (Jacobians.ProperMapDegreeSheets.toRiemannSphere_not_isConstant_of_div_ne_zero f₀ hdiv) ha
  -- The regularity certificate at the preimage `y` (the chart-pullback deriv ≠ 0).
  have hderiv : deriv ((chartAt ℂ (((a : ℂ) : RiemannSphere))) ∘ f₀.toRiemannSphere ∘
      (chartAt ℂ y).symm) ((chartAt ℂ y) y) ≠ 0 := by
    have hmem : y ∈ f₀.toRiemannSphere ⁻¹' {w.toWitness.value} := by
      rw [hw]; show f₀.toRiemannSphere y = ((a : ℂ) : RiemannSphere); exact hyval
    have hreg := w.is_regular y hmem
    rw [hw] at hreg
    exact hreg
  rw [MeromorphicFunction.orderAtPoint_inv,
    orderAtPoint_sub_eq_one_of_regular_fibrePoint f₀ a hyval hderiv]

/-! ## The `cs` enumeration of the finite pole-values -/

/-- **The pole-value enumeration of `α = ω₀·g` for a cover `f`.**  Enumerates the finite set
`(poles.image f.toRiemannSphere).erase ∞` (the finite pole-values) into `Fin m → ℂ` injectively, with
the image bookkeeping `hcenters_cs`.  The enumeration pulls each (non-`∞`) sphere value back along the
affine chart `chartCoe` (a section of `coe`). -/
theorem exists_cs_enumeration (f : MeromorphicFunction X) (poles : Finset X) :
    ∃ (m : ℕ) (cs : Fin m → ℂ), Function.Injective cs ∧
      (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
        = (poles.image f.toRiemannSphere).erase OnePoint.infty := by
  classical
  set S := (poles.image f.toRiemannSphere).erase OnePoint.infty with hSdef
  refine ⟨S.card, fun i => chartCoe (S.equivFin.symm i : RiemannSphere), ?_, ?_⟩
  · have hSne : ∀ y ∈ S, y ≠ OnePoint.infty := fun y hy => Finset.ne_of_mem_erase hy
    have hsec : ∀ y ∈ S, ((chartCoe y : ℂ) : RiemannSphere) = y := by
      intro y hy
      have hsrc : y ∈ chartCoe.source := by rw [chartCoe_source]; exact hSne y hy
      rw [← chartCoe_symm_apply (chartCoe y), chartCoe.left_inv hsrc]
    intro i j hij
    simp only at hij
    apply S.equivFin.symm.injective
    apply Subtype.ext
    have hi := hsec _ (S.equivFin.symm i).2
    have hj := hsec _ (S.equivFin.symm j).2
    rw [← hi, ← hj, hij]
  · have hSne : ∀ y ∈ S, y ≠ OnePoint.infty := fun y hy => Finset.ne_of_mem_erase hy
    have hsec : ∀ y ∈ S, ((chartCoe y : ℂ) : RiemannSphere) = y := by
      intro y hy
      have hsrc : y ∈ chartCoe.source := by rw [chartCoe_source]; exact hSne y hy
      rw [← chartCoe_symm_apply (chartCoe y), chartCoe.left_inv hsrc]
    rw [Finset.image_image]
    ext y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, _, rfl⟩
      show ((chartCoe (S.equivFin.symm i : RiemannSphere) : ℂ) : RiemannSphere) ∈ S
      rw [hsec _ (S.equivFin.symm i).2]; exact (S.equivFin.symm i).2
    · intro hy
      refine ⟨S.equivFin ⟨y, hy⟩, Finset.mem_univ _, ?_⟩
      show ((chartCoe ((S.equivFin.symm (S.equivFin ⟨y, hy⟩)) : RiemannSphere) : ℂ) : RiemannSphere) = y
      rw [Equiv.symm_apply_apply]; exact hsec y hy

/-! ## The `AdaptedFRamified` builder and TARGET 2 -/

/-- **The `AdaptedFRamified` cover from a finite regular value** (the genericity construction).  For a
nonconstant `f₀` (`hdiv₀`) and a finite regular value `a` of `f₀.toRiemannSphere` (`ha`), the reciprocal
`f := (f₀ − a·1)⁻¹` is an `AdaptedFRamified` datum for `α = ω₀·g` over `poles` (given `g` analytic off
`poles`).  All fields are discharged: `hdiv` (`div_sub_smul_ne_zero` + `orderAtPoint_inv`), `hsimpleInf`
(`orderAtPoint_inv_eq_neg_one_of_regularValue`), and the pole-value enumeration
(`exists_cs_enumeration`). -/
noncomputable def adaptedFRamified_of_regularValue {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X}
    (f₀ : MeromorphicFunction X) (hf₀ : ¬ IsGermConstant f₀) (a : ℂ)
    (ha : ((a : ℂ) : RiemannSphere) ∉
      Jacobians.Discharge.Manifold.criticalValuesGeneral f₀.toRiemannSphere)
    (hg_an : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) :
    AdaptedFRamified ω₀ g poles := by
  classical
  -- The cover and its nonconstancy.
  set fc : MeromorphicFunction X := (f₀ - a • (constOneMero (X := X)))⁻¹ with hfc
  have hdiv₀ : (f₀.div : Divisor X) ≠ 0 := div_ne_zero_of_not_isGermConstant f₀ hf₀
  have hdivc : (fc.div : Divisor X) ≠ 0 := by
    rw [hfc]
    -- `((f₀-a•1)⁻¹).div ≠ 0` from `(f₀-a•1).div ≠ 0` via `orderAtPoint_inv`.
    intro hd
    apply div_sub_smul_ne_zero_of_not_isGermConstant f₀ hf₀ a
    ext x
    simp only [Finsupp.coe_zero, Pi.zero_apply, div_apply]
    have hx := congrFun (congrArg (DFunLike.coe) hd) x
    simp only [Finsupp.coe_zero, Pi.zero_apply, div_apply] at hx
    have hinv := MeromorphicFunction.orderAtPoint_inv (f₀ - a • (constOneMero (X := X))) x
    rw [hx] at hinv
    omega
  -- The pole-value enumeration (via choice, since this is a data-bearing `def`).
  set m : ℕ := (exists_cs_enumeration fc poles).choose with hm
  set cs : Fin m → ℂ := (exists_cs_enumeration fc poles).choose_spec.choose with hcs
  have hcs_inj : Function.Injective cs := (exists_cs_enumeration fc poles).choose_spec.choose_spec.1
  have hcenters : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image fc.toRiemannSphere).erase OnePoint.infty :=
    (exists_cs_enumeration fc poles).choose_spec.choose_spec.2
  -- A radius bounding the centres (sum of norms + 1).
  set ρ : ℝ := (∑ i, ‖cs i‖) + 1 with hρ
  refine
    { f := fc
      hdiv := hdivc
      m := m
      cs := cs
      ρ := ρ
      hcs_ball := ?_
      hcs_inj := hcs_inj
      hcenters_cs := hcenters
      hsimpleInf := ?_
      hg_an_offpoles := hg_an }
  · -- each `cs i` lies in `ball 0 ρ`: `‖cs i‖ ≤ ∑ ‖cs ·‖ < ρ`.
    intro i
    rw [Metric.mem_ball, dist_zero_right]
    have hle : ‖cs i‖ ≤ ∑ j, ‖cs j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (cs j)) (Finset.mem_univ i)
    rw [hρ]; linarith
  · -- `hsimpleInf`: every `∞`-pole of `fc` is simple.
    intro i
    -- `inftyFibreEnum fc i` is a pole of `fc`, so `orderAtPoint fc · = -1` by the regular-value lemma
    -- (`fc = (f₀ - a•1)⁻¹` definitionally).
    have hpole : fc.orderAtPoint (inftyFibreEnum fc i) < 0 := inftyFibreEnum_lt fc i
    exact orderAtPoint_inv_eq_neg_one_of_regularValue f₀ hdiv₀ a ha hpole

/-- **TARGET 2 (Gate-A off-centre/∞ genericity selection), fully proven.**  The `hoff_cs`-free adapted
cover exists for `α = ω₀·g` over any finite `poles` off which `g` is analytic.  Construction: the
nonconstant `f₀` of `exists_nonconstant_meromorphic` (Riemann inequality, Serre-independent) and the
reciprocal `f := (f₀ − a·1)⁻¹` at a finite regular value `a` (`exists_finite_regularValue`); all
genericity fields are discharged by `adaptedFRamified_of_regularValue`.  Miranda §VIII.3, p. 254. -/
theorem existsAdaptedFRamified (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X) : ExistsAdaptedFRamified ω₀ g poles := by
  intro hg_an
  -- A nonconstant meromorphic `f₀`.
  obtain ⟨_D, f₀, _hmem, hf₀⟩ := exists_nonconstant_meromorphic (X := X)
  -- A finite regular value of `f₀.toRiemannSphere`.
  obtain ⟨a, ha⟩ := exists_finite_regularValue f₀ (div_ne_zero_of_not_isGermConstant f₀ hf₀)
  exact ⟨adaptedFRamified_of_regularValue f₀ hf₀ a ha hg_an⟩

end Jacobians.Dolbeault.SerreResidueTheorem
