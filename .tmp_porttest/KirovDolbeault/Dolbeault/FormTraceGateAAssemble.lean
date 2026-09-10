/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceBundleBridge
import KirovDolbeault.Dolbeault.FormTraceSphereSheetTranslate
import KirovDolbeault.Dolbeault.SerreOmega0
import KirovDolbeault.Discharge.Manifold.RegularValueExistsRegUnconditional

/-!
# Gate A `∑Res = 0`: global-cover selection assembly (Miranda §VIII.3)

`Jacobians.Dolbeault.FormTraceBundleBridge.residueSum_eq_zero_ofBundleBranchAgree` reduced the
1-form residue theorem `∑ₐ Resₐ(α) = 0` (for `α = ω₀·g`) to a *fixed* list of global-cover /
selection inputs (the adapted cover `hac`, the global fibre selection `Φ`, the finite-center data
`cs`/`ρ`/`Dinf`, the regular-value sphere data `Sreg` with its canonical-fibre conditions, the
per-branch local-form agreement `hαBrAgreeBr`, and the `∞`-rationality bookkeeping
`hglue_inf`/`hcont_int`/`R₀`).  The branch-value crux is already closed (monodromy-free).

This file builds the **directly-derivable** inputs from the already-proven nodes, so the surface of
genuinely-remaining obligations is exposed precisely:

* `hncF` — the cover is nonconstant — is *free* from `f.div ≠ 0`
  (`MeromorphicFunction.toRiemannSphere_not_isConstant_of_div_ne_zero`);
* the **regular-value sphere sheet family** `Sreg` is *constructed* (choice over the per-value
  `exists_sphereSheetSystem`) for every `z` off the finite branch locus, together with the
  canonical-fibre conditions `hsheetInjReg` (`LocalSheetSystem.sheet_inj`), `hsheetMemReg` (each sheet
  passes through its own chart source near the base), and `hderivReg` (each fibre point is a regular
  point of `f` — off-branch local injectivity ⟹ nonzero chart-pullback derivative, transferred from
  `f.toRiemannSphere` to `f.holoRepr` via the non-pole comparison);
* `hbrBr` — branch-locus membership of the `br` centers — holds *by construction* when `br` is taken
  to be the finite set of branch values.

What this does **not** discharge (the honest residual walls, each genuinely deep §VIII.3 analysis,
none currently scaffolded in the repo):

1. **AdaptedCover existence** (`∃ f, AdaptedCover ω₀ g f poles`): a nonconstant `f` *regular and a
   non-pole at every pole of `α`*.  Standard genericity (the finite pole set avoids `f`'s finite
   critical set + poles by perturbing `f` in a large linear system, Miranda §VIII.3), but it needs
   Riemann–Roch with *prescribed local jets* — not yet in Mathlib/this repo.
2. **The global coherent selection** `Φ` with `hΦrangeReg` (range `Φ b'` = the full fibre) and the
   per-pole moving-section consistency (`secFin`/`hselFin`): the moving-fibre coherence / monodromy
   content.
3. **Trace rationality at `∞`** (`hglue_inf`/`hcont_int`/`R₀`/`hR₀_eq`): the meromorphy of `Tr_F α` at
   `∞` with the correct principal part — the irreducible §VIII.3 wall already isolated as
   `TraceRationalityWitness` in `FormTraceGlobalConstruct`.

The clean reduction theorem `residueSum_eq_zero_of_globalCoverData` re-exports
`residueSum_eq_zero_ofBundleBranchAgree` with `hncF` and the sheet-intrinsic `Sreg` conditions
discharged, leaving the three walls above as its hypotheses.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; rationality
  on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### `hncF` — the cover is nonconstant (free from `f.div ≠ 0`) -/

/-- **The sphere cover of a nonconstant `f` is nonconstant** (in the `¬ ∃ y₀, ∀ x, F x = y₀` form the
bundle close consumes).  Direct from `toRiemannSphere_not_isConstant_of_div_ne_zero` (which gives the
`Discharge.IsConstantMap` negation), unfolding `IsConstantMap`. -/
theorem hncF_of_div_ne_zero (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀ :=
  Jacobians.ProperMapDegreeSheets.toRiemannSphere_not_isConstant_of_div_ne_zero f hdiv

/-- A meromorphic `f` with `f.div ≠ 0` has a point of nonzero order
(`f.div x = f.orderAtPoint x` via `div_apply`).  The `∃ x, orderAtPoint x ≠ 0` form that
`exists_sphereSheetSystem` consumes. -/
theorem exists_orderAtPoint_ne_zero (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∃ x, f.orderAtPoint x ≠ 0 := by
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hdiv
  refine ⟨x, ?_⟩
  rw [Finsupp.coe_zero, Pi.zero_apply] at hx
  -- `(f.div) x = f.orderAtPoint x` definitionally (`div_apply` is `rfl`).
  exact hx

/-! ### The finite branch-value set and the regular-value sphere sheet family

For a nonconstant `f`, the branch locus of the *compact* sphere map `f.toRiemannSphere` is finite
(`finite_branchLocus_of_nonconstant`).  Its preimage under `coe : ℂ → RiemannSphere` (the *finite*
branch values) is a finite set of complex numbers `branchValues f`.  Off `branchValues f`, a finite
value `coe z` lies off the branch locus, so `exists_sphereSheetSystem` gives a sheet system at `coe z`;
choosing one for each such `z` yields the `Sreg` family. -/

/-- The finite set of **finite branch values** of `f` — the complex numbers `z` with `coe z` in the
branch locus of the sphere cover `f.toRiemannSphere`.  Finite because the branch locus is finite (for a
nonconstant `f`) and `coe` is injective. -/
def branchValues (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) : Finset ℂ :=
  ((finite_branchLocus_of_nonconstant f.toRiemannSphere f.contMDiff_toRiemannSphere
      (hncF_of_div_ne_zero f hdiv)).preimage
    ((OnePoint.coe_injective (X := ℂ)).injOn)).toFinset

@[simp] theorem mem_branchValues (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {z : ℂ} :
    z ∈ branchValues f hdiv ↔ ((z : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere := by
  rw [branchValues, Set.Finite.mem_toFinset, Set.mem_preimage]

/-- **A finite value off `branchValues f` is off the branch locus.**  If `z ∉ branchValues f`, then
`coe z ∉ branchLocus f.toRiemannSphere` (the very definition of `branchValues`). -/
theorem coe_notMem_branchLocus_of_notMem_branchValues (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ} (hz : z ∉ branchValues f hdiv) :
    ((z : ℂ) : RiemannSphere) ∉ branchLocus f.toRiemannSphere := by
  rwa [mem_branchValues] at hz

/-- **The regular-value sphere sheet family.**  For a nonconstant `f` and any finite center set `cs`,
choosing a sheet system at every `coe z` with `z ∉ image cs ∪ branchValues f` (such `z` are off the
branch locus, so `exists_sphereSheetSystem` applies) yields the `Sreg` family that
`residueSum_eq_zero_ofBundleBranchAgree` consumes with `br := branchValues f`. -/
noncomputable def sregFamily (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {m : ℕ} (cs : Fin m → ℂ) :
    ∀ z, z ∉ Finset.univ.image cs ∪ branchValues f hdiv →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)) := by
  intro z hz
  have hzbr : z ∉ branchValues f hdiv := fun h => hz (Finset.mem_union_right _ h)
  exact (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv)
    (coe_notMem_branchLocus_of_notMem_branchValues f hdiv hzbr)).some

/-! ### Sheet-intrinsic canonical-fibre conditions for `sregFamily`

Two of the canonical-fibre conditions `residueSum_eq_zero_ofBundleBranchAgree` requires of `Sreg` are
*intrinsic to any `LocalSheetSystem`*, hence hold for `sregFamily` with no extra hypothesis:

* `hsheetInjReg` — the sheets are eventually injective in the value (from `LocalSheetSystem.sheet_inj`
  over the open base neighbourhood `S.V`, pulled back along the continuous `coe`);
* `hsheetMemReg` — each sheet eventually passes through *its own* chart source (continuity of the sheet
  at the base + `mem_chart_source`).
-/

/-- `hsheetInjReg` for `sregFamily`: near each regular `z`, the sheets `i ↦ S.sheet i (coe b')` are
injective — from `LocalSheetSystem.sheet_inj` over the open sphere base neighbourhood `S.V`, valid for
`coe b'` near `coe z` (continuity of `coe` + openness of `S.V`). -/
theorem sregFamily_hsheetInjReg (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {m : ℕ} (cs : Fin m → ℂ) (z : ℂ) (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv) :
    ∀ᶠ b' in 𝓝 z,
      Function.Injective (fun i => (sregFamily f hdiv cs z hz).sheet i (((b' : ℂ) : RiemannSphere))) := by
  set S := sregFamily f hdiv cs z hz with hS
  have hmem : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) ∈ 𝓝 z :=
    (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (S.isOpen_V.mem_nhds S.mem_V)
  filter_upwards [hmem] with b' hb'
  exact S.sheet_inj (((b' : ℂ) : RiemannSphere)) hb'

/-- `hsheetMemReg` for `sregFamily`: near each regular `z`, each sheet `S.sheet i (coe b')` lies in the
chart source of its base point `S.sheet i (coe z)`.  Each `holoReprSheet S i = b' ↦ S.sheet i (coe b')`
is continuous at `z` (`holoReprSheet_contMDiffAt`) with value `S.sheet i (coe z)` at `z`, so it
eventually stays in the open chart source. -/
theorem sregFamily_hsheetMemReg (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {m : ℕ} (cs : Fin m → ℂ) (z : ℂ) (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv) :
    ∀ᶠ b' in 𝓝 z, ∀ i, (sregFamily f hdiv cs z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
      (chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).source := by
  set S := sregFamily f hdiv cs z hz with hS
  -- For each sheet `i`: `holoReprSheet S i` is continuous at `z` and `= S.sheet i (coe z)` there.
  have hev : ∀ i : Fin S.n, ∀ᶠ b' in 𝓝 z, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
      (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).source := by
    intro i
    have hcont : ContinuousAt (S.holoReprSheet i) z :=
      (S.holoReprSheet_contMDiffAt i).continuousAt
    have hbase : S.holoReprSheet i z = S.sheet i (((z : ℂ) : RiemannSphere)) := rfl
    have hsrc : (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).source ∈
        𝓝 (S.sheet i (((z : ℂ) : RiemannSphere))) :=
      (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).open_source.mem_nhds
        (mem_chart_source ℂ _)
    have := hcont.preimage_mem_nhds (by rw [hbase]; exact hsrc)
    filter_upwards [this] with b' hb'
    exact hb'
  -- Combine over the finitely many sheets.
  rw [eventually_all]
  exact hev

/-! ### `hderivReg` — regular-value derivative nonvanishing (from off-branch local injectivity)

At a regular value `z` (off the branch locus), every fibre point `p` is a *regular point of `f`*: the
chart-pullback derivative of `f.holoRepr` is nonzero.  This is intrinsic to being off the branch locus
(local injectivity of the sphere cover `f.toRiemannSphere` ⟹ nonzero pullback derivative,
`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`), transferred from `f.toRiemannSphere` to
`f.holoRepr` via the non-pole chart comparison `toRiemannSphere =ᶠ coe ∘ holoRepr`. -/

/-- **Chart-pullback derivative comparison at a non-pole.**  At a non-pole `p` (`0 ≤ orderAtPoint p`),
the derivative of `f.holoRepr`'s chart pullback equals that of `chartAt(F p) ∘ F`'s chart pullback
(`F = f.toRiemannSphere`): near `chart p p`, `F ∘ chart⁻¹ = coe ∘ holoRepr ∘ chart⁻¹`
(`toRiemannSphere_eventuallyEq_coe_holoRepr`) and `chartCoe ∘ coe = id` at the finite value. -/
theorem holoRepr_deriv_eq_toRiemannSphere_deriv (f : MeromorphicFunction X) {p : X}
    (hp : 0 ≤ f.orderAtPoint p) :
    deriv (fun w => f.holoRepr ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p)
    = deriv (fun w => (chartAt ℂ (f.toRiemannSphere p)) (f.toRiemannSphere ((chartAt ℂ p).symm w)))
        ((chartAt ℂ p) p) := by
  have hval : f.toRiemannSphere p = ((f.holoRepr p : ℂ) : RiemannSphere) :=
    f.toRiemannSphere_of_nonneg hp
  apply Filter.EventuallyEq.deriv_eq
  symm
  have hTS : f.toRiemannSphere =ᶠ[𝓝 p] (fun y => ((f.holoRepr y : ℂ) : RiemannSphere)) :=
    f.toRiemannSphere_eventuallyEq_coe_holoRepr hp
  have hcont : ContinuousAt (chartAt ℂ p).symm ((chartAt ℂ p) p) :=
    (chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have hsymm0 : (chartAt ℂ p).symm ((chartAt ℂ p) p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hpull : (fun w => f.toRiemannSphere ((chartAt ℂ p).symm w))
      =ᶠ[𝓝 ((chartAt ℂ p) p)]
        (fun w => ((f.holoRepr ((chartAt ℂ p).symm w) : ℂ) : RiemannSphere)) :=
    hcont.eventually
      (p := fun y => f.toRiemannSphere y = ((f.holoRepr y : ℂ) : RiemannSphere))
      (by rw [hsymm0]; exact hTS)
  filter_upwards [hpull] with w hw
  show (chartAt ℂ (f.toRiemannSphere p)) (f.toRiemannSphere ((chartAt ℂ p).symm w))
      = f.holoRepr ((chartAt ℂ p).symm w)
  rw [hw, hval, RiemannSphere.chartAt_coe, RiemannSphere.chartCoe_apply_coe]

/-- **A fibre point of a non-branch value is a regular point of `f`.**  If `coe z ∉ branchLocus
f.toRiemannSphere` and `f.toRiemannSphere p = coe z`, then `p` is a non-pole (finite value) and the
chart-pullback derivative of `f.holoRepr` at `chart p p` is nonzero.  Off-branch ⟹ `f.toRiemannSphere`
locally injective at `p` (`branchLocus = criticalValuesGeneral`) ⟹ nonzero pullback derivative
(`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`) ⟹ (comparison) nonzero `holoRepr` pullback
derivative. -/
theorem sheet_holoRepr_deriv_ne_zero (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {z : ℂ} {p : X} (hz : ((z : ℂ) : RiemannSphere) ∉ branchLocus f.toRiemannSphere)
    (hpz : f.toRiemannSphere p = ((z : ℂ) : RiemannSphere)) :
    deriv (fun w => f.holoRepr ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) ≠ 0 := by
  have hnpval := f.nonpole_of_toRiemannSphere_eq_coe hpz
  have h_inj : ∃ U ∈ 𝓝 p, Set.InjOn f.toRiemannSphere U := by
    have hpcrit : p ∉ Jacobians.Discharge.Manifold.criticalSetGeneral f.toRiemannSphere := by
      intro hcrit; exact hz ⟨p, hcrit, hpz⟩
    by_contra h; exact hpcrit h
  have htool :=
    Jacobians.Discharge.ContMDiff.Degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
      f.contMDiff_toRiemannSphere (hncF_of_div_ne_zero f hdiv) p h_inj
  rw [holoRepr_deriv_eq_toRiemannSphere_deriv f hnpval.1]
  convert htool using 2

/-- `hderivReg` for `sregFamily`: at every regular value `z` off `branchValues f`, each fibre point
`S.sheet i (coe z)` is a regular point of `f`.  The sheet point has sphere value `coe z`
(`sheet_section` at the base `coe z ∈ S.V`), which is off the branch locus, so
`sheet_holoRepr_deriv_ne_zero` applies. -/
theorem sregFamily_hderivReg (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {m : ℕ} (cs : Fin m → ℂ) (z : ℂ) (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv) :
    ∀ i, deriv (fun w => f.holoRepr
        ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
        ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0 := by
  set S := sregFamily f hdiv cs z hz with hS
  intro i
  have hzbr : z ∉ branchValues f hdiv := fun h => hz (Finset.mem_union_right _ h)
  have hoff : ((z : ℂ) : RiemannSphere) ∉ branchLocus f.toRiemannSphere :=
    coe_notMem_branchLocus_of_notMem_branchValues f hdiv hzbr
  have hpz : f.toRiemannSphere (S.sheet i (((z : ℂ) : RiemannSphere))) = ((z : ℂ) : RiemannSphere) :=
    S.sheet_section i (((z : ℂ) : RiemannSphere)) S.mem_V
  exact sheet_holoRepr_deriv_ne_zero f hdiv hoff hpz

/-! ### The clean reduction: Gate A `∑Res = 0` with the directly-derivable fields discharged

We now wire `residueSum_eq_zero_ofBundleBranchAgree` with the **canonical** regular-value sphere
family `Sreg := sregFamily` and branch set `br := branchValues f`, so that the five fields
`hncF` (cover nonconstant), `hbrBr` (branch-locus membership), `hderivReg` (regular-value derivative
nonvanishing, from off-branch local injectivity), `hsheetInjReg`, `hsheetMemReg` are *discharged* from
the constructions above.  The remaining hypotheses are exactly the three honest §VIII.3 walls:

* the **adapted cover** `hac` and its finite-center fibre data `cs`/`ρ`/`Dinf` + the per-center moving
  sections `secFin`/`hselFin` (the cover genericity + moving-fibre coherence);
* the **regular-value `g`-data** `hmeroReg`/`hCreg_g` (`g`-meromorphy/holomorphy at the regular fibres —
  automatic once `α` is a genuine global meromorphic form on the unramified locus) and the **selection
  range/injectivity** `hΦinjReg`/`hΦrangeReg`;
* the **branch agreement** `hαBrAgreeBr` and the **`∞`-rationality** `hglue_inf`/`hcont_int`/`R₀`/`hR₀_eq`
  (the irreducible trace-rationality wall, `TraceRationalityWitness`).

The boundedness heart (the bundle trace SUM) and the entire descent are already proven; this is the
faithful narrowing of the global-cover assembly to those walls. -/
theorem residueSum_eq_zero_of_globalCoverData (hdiv : (f.div : Divisor X) ≠ 0)
    (hac : AdaptedCover ω₀ g f poles)
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (secFin : ∀ i, (fibreReg hac (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (fibreReg hac (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hselFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∃ e : (Φ b').ι ≃ (fibreReg hac (cs i)).ι,
      (∀ i', (Φ b').xs i' = secFin i (e i') b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((fibreReg hac (cs i)).xs j)).source))
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinjReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv),
      ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrangeReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv),
      ∀ᶠ b' in 𝓝 z, Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
      AnalyticAt ℂ
        (fun w => g ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (αBr : ℂ → HolomorphicOneForms X)
    (hαBrAgreeBr : ∀ b₀ ∈ branchValues f hdiv, b₀ ∉ Finset.univ.image cs →
      ∀ᶠ z in 𝓝[≠] b₀, ∀ (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
        (αBr b₀).toFun ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))
          = g ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))
            • ω₀.toFun ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
    (hglue_inf : recipCoeff (valueChartTracePatched ω₀ f Φ (branchValues f hdiv))
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ (branchValues f hdiv) - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a,
        ContinuousAt (valueChartTracePatched ω₀ f Φ (branchValues f hdiv) - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ (branchValues f hdiv) - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_ofBundleBranchAgree hac Φ m cs ρ hcs_ball hcs_inj hcenters_cs Dinf hxs_inj
    hxs_mem hxs_surj secFin hsecFin_base hsecFin_smooth hsecFin_sec hselFin
    (branchValues f hdiv) (sregFamily f hdiv cs)
    (fun z hz => sregFamily_hderivReg f hdiv cs z hz) hmeroReg hΦinjReg hΦrangeReg
    (fun z hz => sregFamily_hsheetInjReg f hdiv cs z hz)
    (fun z hz => sregFamily_hsheetMemReg f hdiv cs z hz)
    hCreg_g (hncF_of_div_ne_zero f hdiv) αBr
    (fun _b₀ hb₀ _ => (mem_branchValues f hdiv).mp hb₀)
    hαBrAgreeBr hglue_inf hcont_int R₀ hR₀_an hR₀0 hR₀_eq

end Jacobians.Dolbeault.FormTraceGlobal
