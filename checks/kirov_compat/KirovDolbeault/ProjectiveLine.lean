/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Field.Lemmas
import KirovDolbeault.Genus
import KirovDolbeault.SmoothPathCore

/-!
# The complex Riemann sphere `ℂℙ¹` as a compact complex 1-manifold

We model `ℂℙ¹` as the Alexandroff one-point compactification `OnePoint ℂ = ℂ ∪ {∞}`
(`RiemannSphere`). Mathlib provides the topology and all the point-set instances
(`CompactSpace`, `T2Space`, `ConnectedSpace`) for free, since `ℂ` is a proper —
hence weakly-locally-compact — Hausdorff, preconnected, noncompact space.

On top of that we build, by hand, the structure required by the Jacobians challenge
vocabulary (mirroring `Jacobians.Roadmap`):

* `ChartedSpace ℂ RiemannSphere` from the two standard charts
  `U₀` (the `ℂ`-affine chart, identity on `ℂ`, source `{∞}ᶜ`) and
  `U∞` (the chart at `∞`, the inversion `z ↦ 1/z`, source `{0}ᶜ`);
* `IsManifold 𝓘(ℂ) ω RiemannSphere` — the transition map between the two charts is
  the holomorphic inversion `z ↦ 1/z` on `ℂˣ`;
* a homeomorphism `RiemannSphere ≃ₜ S²` to the Euclidean 2-sphere (via Mathlib's
  `onePointEquivSphereOfFinrankEq`, since `ℂ ≃ ℝ²` has real dimension `2`);
* `kirovGenus RiemannSphere = 0` (the space of global holomorphic 1-forms is `⊥`), by
  Liouville: a global holomorphic 1-form pulls back to an entire function on the
  affine chart that extends holomorphically over `∞`, hence is bounded, hence
  constant, and the value at `∞` forces it to vanish.

## References

Forster, *Lectures on Riemann Surfaces*, §1, §5, §10 (`ℂℙ¹`, charts, `Ω(ℂℙ¹) = 0`).
Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. I.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open OnePoint Complex

namespace Jacobians

/-- The **Riemann sphere** `ℂℙ¹`, modelled as the one-point compactification
`OnePoint ℂ = ℂ ∪ {∞}`. -/
abbrev RiemannSphere : Type := OnePoint ℂ

namespace RiemannSphere

/-! ### Milestone 1 — the free point-set instances

All of these are found by `inferInstance` from Mathlib's `OnePoint` development;
we record them explicitly so the manifold vocabulary downstream can rely on them
being present (and to document that the model has them). -/

instance : TopologicalSpace RiemannSphere := inferInstance
instance : CompactSpace RiemannSphere := inferInstance
instance : T2Space RiemannSphere := inferInstance
instance : ConnectedSpace RiemannSphere := inferInstance
instance : Nonempty RiemannSphere := inferInstance

/-! ### Milestone 2a — the inversion homeomorphism `z ↦ z⁻¹`

The chart at `∞` is built from the inversion `z ↦ 1/z`, which we first package as a
self-homeomorphism of `OnePoint ℂ` swapping `0 ↔ ∞`. Continuity is checked via
`OnePoint.continuous_iff`:

* at `∞` (i.e. along `coclosedCompact ℂ = cobounded ℂ`), `z⁻¹ → 0` (`tendsto_inv₀_cobounded`);
* on the affine part, `z ↦ z⁻¹` is continuous away from `0`, and at `0` the value `∞` is the
  limit because `z⁻¹ → ∞` as `z → 0` (`tendsto_inv₀_nhdsNE_zero` + `tendsto_coe_infty`).

It is an involution, so the same proof serves for both `toFun` and `invFun`. -/

open Filter Bornology in
/-- The underlying point map of the inversion: `∞ ↦ 0`, `0 ↦ ∞`, and `z ↦ z⁻¹` otherwise. -/
def invMap : RiemannSphere → RiemannSphere :=
  fun p => p.elim (((0 : ℂ)) : RiemannSphere)
    (fun z => if z = 0 then (OnePoint.infty) else ((z⁻¹ : ℂ) : RiemannSphere))

@[simp] lemma invMap_infty : invMap OnePoint.infty = (((0 : ℂ)) : RiemannSphere) := rfl

lemma invMap_coe (z : ℂ) :
    invMap (z : RiemannSphere) =
      if z = 0 then (OnePoint.infty) else ((z⁻¹ : ℂ) : RiemannSphere) := rfl

@[simp] lemma invMap_coe_zero : invMap ((0 : ℂ) : RiemannSphere) = OnePoint.infty := by
  simp [invMap_coe]

lemma invMap_coe_of_ne {z : ℂ} (hz : z ≠ 0) :
    invMap (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [invMap_coe, hz]

lemma involutive_invMap : Function.Involutive invMap := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp [invMap]
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp [invMap]
    · have hz' : (z⁻¹ : ℂ) ≠ 0 := inv_ne_zero hz
      simp only [invMap, OnePoint.elim_some, hz, if_false, hz', inv_inv]

open Filter Bornology Topology in
/-- The coercion `ℂ → OnePoint ℂ` tends to `∞` along `cobounded ℂ` (i.e. as `|z| → ∞`). -/
lemma tendsto_coe_cobounded_infty :
    Tendsto ((↑) : ℂ → RiemannSphere) (cobounded ℂ) (𝓝 OnePoint.infty) := by
  have := @OnePoint.tendsto_coe_infty ℂ _
  rwa [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at this

open Filter Bornology Topology in
lemma tendsto_invMap_infty :
    Tendsto (fun z : ℂ => invMap (z : RiemannSphere)) (coclosedCompact ℂ) (𝓝 (invMap OnePoint.infty)) := by
  rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact, invMap_infty]
  have hcoe : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : RiemannSphere)) (cobounded ℂ)
      (𝓝 ((0 : ℂ) : RiemannSphere)) :=
    (OnePoint.continuous_coe.tendsto _).comp tendsto_inv₀_cobounded
  refine hcoe.congr' ?_
  filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
  simp [invMap_coe, hz]

open Filter Bornology Topology in
/-- The affine restriction `z ↦ invMap z : ℂ → OnePoint ℂ` is continuous. -/
lemma continuous_invMap_coe : Continuous (fun z : ℂ => invMap (z : RiemannSphere)) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [continuousAt_iff_punctured_nhds, invMap_coe_zero]
    have key : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : RiemannSphere)) (𝓝[≠] (0 : ℂ))
        (𝓝 OnePoint.infty) :=
      tendsto_coe_cobounded_infty.comp tendsto_inv₀_nhdsNE_zero
    refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp [invMap_coe, hz]
  · have hev : (fun w : ℂ => invMap (w : RiemannSphere)) =ᶠ[𝓝 z]
        (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere)) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [invMap_coe, hw]
    refine ContinuousAt.congr ?_ hev.symm
    exact OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)

lemma continuous_invMap : Continuous invMap := by
  rw [OnePoint.continuous_iff]
  exact ⟨tendsto_invMap_infty, continuous_invMap_coe⟩

/-- Inversion `z ↦ z⁻¹` as a self-homeomorphism of the Riemann sphere, swapping `0 ↔ ∞`.
This is the change of coordinates between the two standard charts. -/
def inversionHomeomorph : RiemannSphere ≃ₜ RiemannSphere where
  toFun := invMap
  invFun := invMap
  left_inv := involutive_invMap
  right_inv := involutive_invMap
  continuous_toFun := continuous_invMap
  continuous_invFun := continuous_invMap

@[simp] lemma inversionHomeomorph_apply (p : RiemannSphere) : inversionHomeomorph p = invMap p := rfl

@[simp] lemma inversionHomeomorph_symm_apply (p : RiemannSphere) :
    inversionHomeomorph.symm p = invMap p := rfl

/-! ### Milestone 2b — the two charts and the `ChartedSpace ℂ` structure

* `chartCoe : OpenPartialHomeomorph RiemannSphere ℂ` is the affine chart, the inverse of the
  open embedding `ℂ ↪ OnePoint ℂ`. Its source is `{∞}ᶜ` and it is the identity on `ℂ`.
* `chartInfty : OpenPartialHomeomorph RiemannSphere ℂ` is the chart at `∞`, obtained by
  pre-composing `chartCoe` with the inversion. Its source is `{0}ᶜ`, it sends `∞ ↦ 0` and
  `w ↦ w⁻¹` for finite `w ≠ 0`.

`chartAt` chooses `chartInfty` at `∞` and `chartCoe` everywhere else. -/

/-- The affine chart `ℂℙ¹ ⊇ {∞}ᶜ ≃ ℂ`: the inverse of the open embedding `ℂ ↪ OnePoint ℂ`. -/
def chartCoe : OpenPartialHomeomorph RiemannSphere ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → RiemannSphere)).symm

@[simp] lemma chartCoe_source : chartCoe.source = {OnePoint.infty}ᶜ := by
  simp only [chartCoe, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact OnePoint.compl_infty.symm

@[simp] lemma chartCoe_target : chartCoe.target = Set.univ := by
  simp only [chartCoe, OpenPartialHomeomorph.symm_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]

lemma chartCoe_apply_coe (z : ℂ) : chartCoe (z : RiemannSphere) = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv _

@[simp] lemma chartCoe_symm_apply (z : ℂ) : chartCoe.symm z = (z : RiemannSphere) := rfl

/-- The chart at `∞`: pre-compose the affine chart with the inversion `z ↦ z⁻¹`. -/
def chartInfty : OpenPartialHomeomorph RiemannSphere ℂ :=
  inversionHomeomorph.toOpenPartialHomeomorph.trans chartCoe

@[simp] lemma chartInfty_source : chartInfty.source = {((0 : ℂ) : RiemannSphere)}ᶜ := by
  rw [chartInfty, OpenPartialHomeomorph.trans_source]
  simp only [Homeomorph.toOpenPartialHomeomorph_source, Set.univ_inter,
    Homeomorph.toOpenPartialHomeomorph_apply, chartCoe_source]
  ext p
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
    inversionHomeomorph_apply]
  constructor
  · intro h hp; apply h; rw [hp]; simp
  · intro h hp
    apply h
    have := congrArg invMap hp
    rwa [involutive_invMap, invMap_infty] at this

lemma chartInfty_apply_infty : chartInfty OnePoint.infty = 0 := by
  rw [chartInfty, OpenPartialHomeomorph.trans_apply]
  simp only [Homeomorph.toOpenPartialHomeomorph_apply, inversionHomeomorph_apply, invMap_infty]
  exact chartCoe_apply_coe 0

lemma chartInfty_apply_coe {z : ℂ} (hz : z ≠ 0) :
    chartInfty (z : RiemannSphere) = z⁻¹ := by
  rw [chartInfty, OpenPartialHomeomorph.trans_apply]
  simp only [Homeomorph.toOpenPartialHomeomorph_apply, inversionHomeomorph_apply,
    invMap_coe_of_ne hz]
  exact chartCoe_apply_coe _

/-- `chartAt` for the Riemann sphere: the chart at `∞` for the point `∞`, the affine chart
on every finite point. Defined by the `OnePoint` eliminator to avoid a decidability instance. -/
def chartAtRS (p : RiemannSphere) : OpenPartialHomeomorph RiemannSphere ℂ :=
  p.elim chartInfty (fun _ => chartCoe)

@[simp] lemma chartAtRS_infty : chartAtRS OnePoint.infty = chartInfty := rfl

@[simp] lemma chartAtRS_coe (z : ℂ) : chartAtRS (z : RiemannSphere) = chartCoe := rfl

lemma mem_chartAtRS_source (p : RiemannSphere) : p ∈ (chartAtRS p).source := by
  induction p using OnePoint.rec with
  | infty =>
    rw [chartAtRS_infty, chartInfty_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact OnePoint.infty_ne_coe 0
  | coe z =>
    rw [chartAtRS_coe, chartCoe_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact OnePoint.coe_ne_infty z

/-- The two standard charts make the Riemann sphere a `ChartedSpace ℂ`. -/
instance : ChartedSpace ℂ RiemannSphere where
  atlas := {chartCoe, chartInfty}
  chartAt := chartAtRS
  mem_chart_source := mem_chartAtRS_source
  chart_mem_atlas p := by
    induction p using OnePoint.rec with
    | infty => exact Set.mem_insert_of_mem _ rfl
    | coe z => exact Set.mem_insert _ _

/-- `chartInfty.symm z = invMap (z : RiemannSphere)`: on the affine part it is `z ↦ z⁻¹`,
matching the inversion. -/
lemma chartInfty_symm_apply (z : ℂ) :
    chartInfty.symm z = invMap (z : RiemannSphere) := by
  rw [chartInfty, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply, chartCoe_symm_apply]
  simp only [Homeomorph.toOpenPartialHomeomorph_symm_apply, inversionHomeomorph_symm_apply]

/-! ### Milestone 3 — the analytic manifold structure

The four transition maps between `chartCoe` and `chartInfty` are either the identity or the
inversion `z ↦ z⁻¹`, both of which are analytic (`contDiffOn_id`, `contDiffOn_inv`). We use
`isManifold_of_contDiffOn`. -/

instance : IsManifold 𝓘(ℂ) ω RiemannSphere := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rw [show atlas ℂ RiemannSphere = ({chartCoe, chartInfty} : Set _) from rfl] at he he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he he'
  obtain rfl | rfl := he <;> obtain rfl | rfl := he'
  -- chartCoe ↝ chartCoe : the identity
  · refine contDiffOn_id.congr (fun z hz => ?_)
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chartCoe_symm_apply,
      chartCoe_apply_coe, id_eq]
  -- chartCoe ↝ chartInfty : the inversion z ↦ z⁻¹ on {0}ᶜ
  · have hsrc : (chartCoe.symm ≫ₕ chartInfty).source ⊆ {(0 : ℂ)}ᶜ := by
      intro z hz
      rw [OpenPartialHomeomorph.trans_source] at hz
      simp only [Set.mem_inter_iff, Set.mem_preimage, chartCoe_symm_apply, chartInfty_source,
        Set.mem_compl_iff, Set.mem_singleton_iff] at hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h; exact hz.2 (by rw [h])
    refine ((contDiffOn_inv (𝕜 := ℂ)).mono hsrc).congr (fun z hz => ?_)
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chartCoe_symm_apply,
      chartInfty_apply_coe (by simpa using hsrc hz)]
  -- chartInfty ↝ chartCoe : the inversion z ↦ z⁻¹ on {0}ᶜ
  · have hsrc : (chartInfty.symm ≫ₕ chartCoe).source ⊆ {(0 : ℂ)}ᶜ := by
      intro z hz
      rw [OpenPartialHomeomorph.trans_source] at hz
      simp only [Set.mem_inter_iff, Set.mem_preimage, chartCoe_source, Set.mem_compl_iff,
        Set.mem_singleton_iff, chartInfty_symm_apply] at hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h; exact hz.2 (by rw [h]; simp)
    refine ((contDiffOn_inv (𝕜 := ℂ)).mono hsrc).congr (fun z hz => ?_)
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chartInfty_symm_apply,
      invMap_coe_of_ne (by simpa using hsrc hz), chartCoe_apply_coe]
  -- chartInfty ↝ chartInfty : the identity (z ↦ z⁻¹⁻¹ = z, with ∞ handled at z = 0)
  · refine contDiffOn_id.congr (fun z hz => ?_)
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chartInfty_symm_apply, id_eq]
    by_cases hz0 : z = 0
    · subst hz0
      rw [invMap_coe_zero, chartInfty_apply_infty]
    · rw [invMap_coe_of_ne hz0, chartInfty_apply_coe (inv_ne_zero hz0), inv_inv]

/-! ### Milestone 4 — homeomorphism with the Euclidean 2-sphere

Since `ℂ` has real dimension `2`, its one-point compactification is homeomorphic to the unit
sphere in `ℝ³`. This is `onePointEquivSphereOfFinrankEq` with `V = ℂ`, `ι = Fin 3`
(`finrank ℝ ℂ + 1 = 2 + 1 = 3 = Fintype.card (Fin 3)`), the stereographic projection. -/

/-- The Riemann sphere is homeomorphic to the unit `2`-sphere `S² ⊆ ℝ³` (stereographic
projection). -/
def homeoSphere : RiemannSphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by
    simp [Complex.finrank_real_complex])

/-! ### Milestone 5 — kirovGenus zero

`ℂℙ¹` carries no nonzero global holomorphic 1-form, so its space of such forms is a
subsingleton and `kirovGenus = 0` (`Module.finrank_zero_of_subsingleton`).

The structural reduction below is complete:

```
kirovGenus = finrank ℂ (HolomorphicOneForms ℂℙ¹)
      = 0                              -- finrank_zero_of_subsingleton
  ⇐  Subsingleton (HolomorphicOneForms ℂℙ¹)
  ⇐  ∀ ω : HolomorphicOneForms ℂℙ¹, ω = 0          -- subsingleton_of_forall_eq 0
  ⇐  ∀ ω x, ω x = 0                                 -- ContMDiffSection.ext
```

The remaining content is the **Liouville vanishing** `holomorphicOneForm_eq_zero` (**PROVEN
below, axiom-clean**): a global holomorphic 1-form `s` reads, in the affine chart `chartCoe`,
as the entire coefficient `affineCoeff s : ℂ → ℂ` of `dz` (`localRep` based at `0`; entire via
`Montel.localRep_analyticOn_chartTarget` since `chartCoe.target = univ`). Compatibility with
`chartInfty` gives the **transition law** `inftyCoeff_eq_transition`: on the overlap (finite
`z ≠ 0`, `w = z⁻¹`) `g(z⁻¹) = -z² f(z)`, equivalently `f(z) = -z⁻² g(z⁻¹)`, where the factor
`-z²` is the tangent-frame derivative `(trivAt ∞).symmL/(trivAt 0).symmL` computed from
`fderiv(w ↦ w⁻¹) = -w⁻²`. Since `g = inftyCoeff s` is analytic at `w = 0`,
`f(z) = O(z⁻²) → 0` as `z → ∞` (`affineCoeff_tendsto_cobounded`); a complex-differentiable
function with a finite limit at infinity is constant (`Differentiable.eq_const_of_tendsto_cocompact`),
and the limit `0` forces `f ≡ 0` (`affineCoeff_eq_zero`). Then `f(z) = s.toFun (z:ℂℙ¹) 1 = 0`
pins `s.toFun (z:ℂℙ¹) = 0` at every finite point (`ext_ring`; the affine-unit `1` spans the
`1`-dimensional fibre), and `g ≡ 0` near `0` with continuity gives `s.toFun ∞ = 0` too; by
`ContMDiffSection.ext`, `s = 0`.

The supporting "cotangent section ↔ entire chart-coefficient with the `dz`-transformation law"
bridge is assembled here from the existing `Montel.localRep` analyticity and the
`trivAt_symmL_one_eq_fderiv` tangent-frame identity — a bounded computation, not the
Dolbeault/Riemann–Roch infrastructure that gates the kirovGenus goals elsewhere. -/

section LiouvilleVanishing

set_option linter.unusedSectionVars false

variable (s : HolomorphicOneForms RiemannSphere)

/-- The **affine coefficient** `f(z)` of the form `s`: the `dz`-coefficient read in the
affine chart `chartCoe`, i.e. the local representative based at the finite point `0`,
evaluated at the finite point `z`. By `localRep_analyticOn_chartTarget` (with
`chartCoe.target = univ`) this is **entire**. -/
noncomputable def affineCoeff (z : ℂ) : ℂ :=
  Jacobians.Montel.localRep s ((0 : ℂ) : RiemannSphere) (z : RiemannSphere)

/-- The **coefficient at `∞`**, `g(w)`: the local representative based at `∞`, read in the
`∞`-chart `chartInfty`. Analytic on `chartInfty.target` (a neighbourhood of `0`), in
particular continuous at `0`. -/
noncomputable def inftyCoeff (w : ℂ) : ℂ :=
  Jacobians.Montel.localRep s OnePoint.infty (chartInfty.symm w)

lemma chartAt_coe (z : ℂ) : chartAt ℂ (z : RiemannSphere) = chartCoe := rfl

lemma chartAt_infty : chartAt ℂ (OnePoint.infty : RiemannSphere) = chartInfty := rfl

/-- `affineCoeff s` is **entire** (analytic on all of `ℂ`). -/
lemma affineCoeff_analyticOnNhd : AnalyticOnNhd ℂ (affineCoeff s) Set.univ := by
  have h := Jacobians.Montel.localRep_analyticOn_chartTarget s ((0 : ℂ) : RiemannSphere)
  rw [chartAt_coe, chartCoe_target] at h
  -- h : AnalyticOn ℂ (fun z => localRep s 0 (chartCoe.symm z)) univ
  have hfun : (fun z : ℂ => Jacobians.Montel.localRep s ((0 : ℂ) : RiemannSphere)
      (chartCoe.symm z)) = affineCoeff s := by
    funext z; simp only [affineCoeff, chartCoe_symm_apply]
  rw [hfun] at h
  exact analyticOn_univ.mp h

lemma affineCoeff_differentiable : Differentiable ℂ (affineCoeff s) := fun z =>
  ((affineCoeff_analyticOnNhd s z (Set.mem_univ z)).differentiableAt)

/-- `inftyCoeff s` is analytic on `chartInfty.target`, hence **continuous at `0`**
(since `0 = chartInfty ∞ ∈ chartInfty.target`). -/
lemma inftyCoeff_continuousAt_zero : ContinuousAt (inftyCoeff s) 0 := by
  have h := Jacobians.Montel.localRep_analyticOn_chartTarget s (OnePoint.infty : RiemannSphere)
  rw [chartAt_infty] at h
  -- h : AnalyticOn ℂ (fun w => localRep s ∞ (chartInfty.symm w)) chartInfty.target
  have h0 : (0 : ℂ) ∈ chartInfty.target := by
    rw [← chartInfty_apply_infty]
    exact chartInfty.map_source (by rw [chartInfty_source]; simp [OnePoint.infty_ne_coe])
  have hnhd := (chartInfty.open_target.analyticOn_iff_analyticOnNhd.mp h)
  exact (hnhd 0 h0).continuousAt

/-- The **affine-frame unit tangent** at a finite point `z` is just `1 ∈ ℂ`: the chart
transition `chartCoe ∘ chartCoe.symm` is the identity, so its derivative is `1`. -/
lemma trivAt_zero_symmL_one (z : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := RiemannSphere)) ((0 : ℂ) : RiemannSphere)).symmL
        ℂ (z : RiemannSphere) (1 : ℂ) = (1 : ℂ) := by
  have hmem : (z : RiemannSphere) ∈ (chartAt ℂ ((0 : ℂ) : RiemannSphere)).source := by
    rw [chartAt_coe, chartCoe_source]; simp [OnePoint.coe_ne_infty]
  rw [Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C ((0 : ℂ) : RiemannSphere) (z : RiemannSphere) hmem]
  -- The composition `chartAt (z:RS) ∘ (chartAt 0).symm` is the identity near `chartCoe (z:RS) = z`.
  have hcong : ((chartAt (H := ℂ) (z : RiemannSphere)) ∘
      (chartAt (H := ℂ) ((0 : ℂ) : RiemannSphere)).symm) =ᶠ[nhds ((chartAt ℂ ((0:ℂ):RiemannSphere)) (z : RiemannSphere))]
      (id : ℂ → ℂ) := by
    filter_upwards [Filter.univ_mem] with w _
    simp only [chartAt_coe, Function.comp_apply, chartCoe_symm_apply, chartCoe_apply_coe, id_eq]
  rw [hcong.fderiv_eq, fderiv_id]
  rfl

/-- The **`∞`-frame unit tangent** at a finite point `z ≠ 0` is `-z²`: the chart transition
`chartCoe ∘ chartInfty.symm` is `w ↦ w⁻¹` near `chartInfty (z:RS) = z⁻¹`, with derivative
`-(z⁻¹)⁻² = -z²`. This is the `dz = -w⁻² dw` Jacobian of the inversion. -/
lemma trivAt_infty_symmL_one {z : ℂ} (hz : z ≠ 0) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := RiemannSphere)) (OnePoint.infty)).symmL
        ℂ (z : RiemannSphere) (1 : ℂ) = -z ^ 2 := by
  have hmem : (z : RiemannSphere) ∈ (chartAt ℂ (OnePoint.infty : RiemannSphere)).source := by
    rw [chartAt_infty, chartInfty_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hz (by exact_mod_cast (OnePoint.coe_eq_coe.mp h))
  rw [Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C (OnePoint.infty : RiemannSphere) (z : RiemannSphere) hmem]
  have hpt : (chartAt ℂ (OnePoint.infty : RiemannSphere)) (z : RiemannSphere) = z⁻¹ := by
    rw [chartAt_infty]; exact chartInfty_apply_coe hz
  rw [hpt]
  -- The composition `chartAt (z:RS) ∘ chartInfty.symm` is `w ↦ w⁻¹` near `w = z⁻¹`.
  have hcong : ((chartAt (H := ℂ) (z : RiemannSphere)) ∘
      (chartAt (H := ℂ) (OnePoint.infty : RiemannSphere)).symm) =ᶠ[nhds (z⁻¹)]
      (fun w : ℂ => w⁻¹) := by
    have hz' : z⁻¹ ≠ 0 := inv_ne_zero hz
    filter_upwards [eventually_ne_nhds hz'] with w hw
    simp only [chartAt_infty, chartAt_coe, Function.comp_apply, chartInfty_symm_apply,
      invMap_coe_of_ne hw, chartCoe_apply_coe]
  rw [hcong.fderiv_eq, fderiv_inv, ContinuousLinearMap.toSpanSingleton_apply_one]
  rw [inv_pow, inv_inv]
  rfl

/-- **The transition law (`dz` ↦ `-w⁻² dw`).** For a finite point `z ≠ 0`, the affine
coefficient and the `∞`-coefficient (read at the *same* sphere point `z`, i.e. at chart
coordinate `w = z⁻¹` in the `∞`-chart) satisfy `g(z⁻¹) = -z² · f(z)`. Equivalently
`f(z) = -z⁻² · g(z⁻¹)`. -/
lemma inftyCoeff_eq_transition {z : ℂ} (hz : z ≠ 0) :
    inftyCoeff s z⁻¹ = -z ^ 2 * affineCoeff s z := by
  -- Unfold both `localRep`s; they share the sphere point `(z : RiemannSphere)`.
  have hsymm : chartInfty.symm z⁻¹ = (z : RiemannSphere) := by
    rw [chartInfty_symm_apply, invMap_coe_of_ne (inv_ne_zero hz), inv_inv]
  have hg : inftyCoeff s z⁻¹ =
      s.toFun (z : RiemannSphere)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := RiemannSphere)) OnePoint.infty).symmL
          ℂ (z : RiemannSphere) (1 : ℂ)) := by
    rw [inftyCoeff, hsymm]; rfl
  have hf : affineCoeff s z =
      s.toFun (z : RiemannSphere)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := RiemannSphere)) ((0 : ℂ) : RiemannSphere)).symmL
          ℂ (z : RiemannSphere) (1 : ℂ)) := rfl
  rw [hg, hf, trivAt_infty_symmL_one hz, trivAt_zero_symmL_one]
  -- View `s.toFun (z:RS) : ℂ →L[ℂ] ℂ` (defeq) and pull the scalar `-z²` out by ℂ-linearity.
  set T : ℂ →L[ℂ] ℂ := s.toFun (z : RiemannSphere)
  show T (-z ^ 2) = -z ^ 2 * T 1
  rw [← smul_eq_mul, ← map_smul]; congr 1; rw [smul_eq_mul, mul_one]

open Filter Bornology Topology in
/-- **`O(z⁻²)` decay at `∞`.** The affine coefficient tends to `0` along `cobounded`
(`|z| → ∞`): `f(z) = -z⁻² g(z⁻¹)` with `g(z⁻¹) → g(0)` bounded and `z⁻² → 0`. -/
lemma affineCoeff_tendsto_cobounded :
    Filter.Tendsto (affineCoeff s) (Bornology.cobounded ℂ) (𝓝 0) := by
  -- The decay representative: `-(z⁻¹)² · g(z⁻¹)`, which equals `f(z)` for `z ≠ 0`.
  have hg : Filter.Tendsto (fun z : ℂ => inftyCoeff s z⁻¹) (Bornology.cobounded ℂ)
      (𝓝 (inftyCoeff s 0)) :=
    (inftyCoeff_continuousAt_zero s).tendsto.comp tendsto_inv₀_cobounded
  have hz2 : Filter.Tendsto (fun z : ℂ => -(z⁻¹) ^ 2) (Bornology.cobounded ℂ) (𝓝 0) := by
    have := (tendsto_inv₀_cobounded (α := ℂ)).pow 2
    simpa using this.neg
  have hprod : Filter.Tendsto (fun z : ℂ => -(z⁻¹) ^ 2 * inftyCoeff s z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 0) := by
    have := hz2.mul hg
    simpa using this
  refine hprod.congr' ?_
  filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
  -- `-(z⁻¹)² g(z⁻¹) = -(z⁻¹)² · (-z² f(z)) = (z⁻¹ z)² f(z) = f(z)`.
  rw [inftyCoeff_eq_transition s hz]
  have hzz : (z⁻¹) ^ 2 * z ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  have hrw : -(z⁻¹) ^ 2 * (-z ^ 2 * affineCoeff s z)
      = (z⁻¹ ^ 2 * z ^ 2) * affineCoeff s z := by ring
  rw [hrw, hzz, one_mul]

/-- **The affine coefficient vanishes identically.** `f` is entire and tends to `0` at `∞`
(Liouville: a bounded entire function tending to a limit at infinity is that constant). -/
lemma affineCoeff_eq_zero : affineCoeff s = 0 := by
  have hcocompact : Filter.Tendsto (affineCoeff s) (Filter.cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact affineCoeff_tendsto_cobounded s
  have h := (affineCoeff_differentiable s).eq_const_of_tendsto_cocompact hcocompact
  rw [h]; rfl

/-- At a finite point `z`, the affine coefficient is `s.toFun (z:RS)` applied to the
affine-frame unit `1`. -/
lemma affineCoeff_eq_toFun_one (z : ℂ) :
    affineCoeff s z = s.toFun (z : RiemannSphere) (1 : ℂ) := by
  rw [affineCoeff]
  show s.toFun (z : RiemannSphere)
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := RiemannSphere)) ((0 : ℂ) : RiemannSphere)).symmL
      ℂ (z : RiemannSphere) (1 : ℂ)) = _
  rw [trivAt_zero_symmL_one]

/-- The section vanishes at every **finite** point: `s.toFun (z:RS) = 0`. The affine-frame
unit `1` spans the `1`-dimensional fibre `ℂ`, and `s.toFun (z:RS) 1 = f(z) = 0`. -/
lemma section_apply_eq_zero_coe (z : ℂ) : s.toFun (z : RiemannSphere) = 0 := by
  have h0 : s.toFun (z : RiemannSphere) (1 : ℂ) = 0 := by
    rw [← affineCoeff_eq_toFun_one s z, show affineCoeff s = 0 from affineCoeff_eq_zero s]; rfl
  -- `s.toFun (z:RS) : ℂ →L[ℂ] ℂ` (via defeq) vanishes at `1`, hence is `0` (`ext_ring`).
  set T : ℂ →L[ℂ] ℂ := s.toFun (z : RiemannSphere) with hT
  show T = 0
  have hT1 : T 1 = 0 := by show s.toFun (z : RiemannSphere) (1 : ℂ) = 0; exact h0
  exact ContinuousLinearMap.ext_ring (hT1.trans (ContinuousLinearMap.zero_apply 1).symm)

/-- The **`∞`-frame unit tangent** at the point `∞` is `1 ∈ ℂ`: the chart transition
`chartInfty ∘ chartInfty.symm` is the identity, so its derivative is `1`. -/
lemma trivAt_infty_symmL_one_at_infty :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := RiemannSphere)) (OnePoint.infty)).symmL
        ℂ (OnePoint.infty : RiemannSphere) (1 : ℂ) = (1 : ℂ) := by
  have hmem : (OnePoint.infty : RiemannSphere) ∈ (chartAt ℂ (OnePoint.infty : RiemannSphere)).source :=
    mem_chartAtRS_source OnePoint.infty
  rw [Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C (OnePoint.infty : RiemannSphere)
    (OnePoint.infty : RiemannSphere) hmem]
  have hcong : ((chartAt (H := ℂ) (OnePoint.infty : RiemannSphere)) ∘
      (chartAt (H := ℂ) (OnePoint.infty : RiemannSphere)).symm) =ᶠ[nhds ((chartAt ℂ (OnePoint.infty : RiemannSphere)) (OnePoint.infty : RiemannSphere))]
      (id : ℂ → ℂ) := by
    have htgt : (chartAt ℂ (OnePoint.infty : RiemannSphere)).target ∈
        nhds ((chartAt ℂ (OnePoint.infty : RiemannSphere)) (OnePoint.infty : RiemannSphere)) :=
      (chartAt ℂ (OnePoint.infty : RiemannSphere)).open_target.mem_nhds
        ((chartAt ℂ (OnePoint.infty : RiemannSphere)).map_source hmem)
    filter_upwards [htgt] with w hw
    simp only [Function.comp_apply, id_eq]
    exact (chartAt ℂ (OnePoint.infty : RiemannSphere)).right_inv hw
  rw [hcong.fderiv_eq, fderiv_id]
  rfl

/-- `inftyCoeff s` vanishes on the **punctured** chart target: for `w ≠ 0`,
`chartInfty.symm w = (w⁻¹ : RS)` is a finite point, where `s.toFun` is `0`. -/
lemma inftyCoeff_eq_zero_of_ne {w : ℂ} (hw : w ≠ 0) : inftyCoeff s w = 0 := by
  rw [inftyCoeff, chartInfty_symm_apply, invMap_coe_of_ne hw, Jacobians.Montel.localRep,
    show s.toFun ((w⁻¹ : ℂ) : RiemannSphere) = 0 from section_apply_eq_zero_coe s w⁻¹]
  rfl

/-- `inftyCoeff s 0 = 0`: continuity at `0` plus vanishing on the punctured neighbourhood. -/
lemma inftyCoeff_zero_eq_zero : inftyCoeff s 0 = 0 := by
  have hcont := inftyCoeff_continuousAt_zero s
  -- `inftyCoeff s` is eventually `0` near `0` (punctured), so its limit / value at `0` is `0`.
  have heq : inftyCoeff s =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact inftyCoeff_eq_zero_of_ne s (by simpa using hw)
  have hlim : Filter.Tendsto (inftyCoeff s) (𝓝[≠] (0 : ℂ)) (𝓝 (inftyCoeff s 0)) :=
    hcont.continuousWithinAt
  have hlim0 : Filter.Tendsto (inftyCoeff s) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    (tendsto_const_nhds (x := (0 : ℂ)) (f := 𝓝[≠] (0 : ℂ))).congr' heq.symm
  exact tendsto_nhds_unique hlim hlim0

/-- The section vanishes at `∞`: `s.toFun ∞ = 0`. The `∞`-frame unit at `∞` is `1`, and
`s.toFun ∞ 1 = inftyCoeff s 0 = 0`; then `ext_ring`. -/
lemma section_apply_eq_zero_infty : s.toFun (OnePoint.infty : RiemannSphere) = 0 := by
  have h0 : s.toFun (OnePoint.infty : RiemannSphere) (1 : ℂ) = 0 := by
    have hval : inftyCoeff s 0 = s.toFun (OnePoint.infty : RiemannSphere) (1 : ℂ) := by
      rw [inftyCoeff]
      have hsymm0 : chartInfty.symm 0 = (OnePoint.infty : RiemannSphere) := by
        rw [chartInfty_symm_apply, invMap_coe_zero]
      rw [hsymm0]
      show s.toFun (OnePoint.infty : RiemannSphere)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := RiemannSphere)) OnePoint.infty).symmL
          ℂ (OnePoint.infty : RiemannSphere) (1 : ℂ)) = _
      rw [trivAt_infty_symmL_one_at_infty]
    rw [← hval, show inftyCoeff s 0 = 0 from inftyCoeff_zero_eq_zero s]
  set T : ℂ →L[ℂ] ℂ := s.toFun (OnePoint.infty : RiemannSphere) with hT
  show T = 0
  exact ContinuousLinearMap.ext_ring (by
    rw [show T 1 = s.toFun (OnePoint.infty : RiemannSphere) (1 : ℂ) from rfl, h0]; rfl)

end LiouvilleVanishing

/-- **Liouville vanishing.** Every global holomorphic 1-form on `ℂℙ¹` is zero.

See the section docstring for the proof outline (chart pull-back → entire coefficient →
`O(z⁻²)` decay at `∞` → bounded → constant by Liouville → constant `= 0`). -/
theorem holomorphicOneForm_eq_zero (s : HolomorphicOneForms RiemannSphere) : s = 0 := by
  apply ContMDiffSection.ext
  intro x
  have hsx : s.toFun x = 0 := by
    induction x using OnePoint.rec with
    | coe z => exact section_apply_eq_zero_coe s z
    | infty => exact section_apply_eq_zero_infty s
  show s.toFun x = (0 : HolomorphicOneForms RiemannSphere).toFun x
  rw [hsx]; rfl

instance : Subsingleton (HolomorphicOneForms RiemannSphere) :=
  subsingleton_of_forall_eq 0 holomorphicOneForm_eq_zero

/-- The Riemann sphere `ℂℙ¹` has kirovGenus `0`. -/
theorem genus_eq_zero : kirovGenus RiemannSphere = 0 :=
  Module.finrank_zero_of_subsingleton

end RiemannSphere

end Jacobians
