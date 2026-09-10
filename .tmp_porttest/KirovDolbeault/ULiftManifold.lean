/-
A `ULift` of a complex manifold is a complex manifold (with the *same* model `E`).

Mathlib equips `ULift X` with the transported topology, T2 / compact / topological-group
structure, but not with a charted-space / `IsManifold` structure.  This file fills that gap:
given `M` a `C^ω` manifold modelled on a normed `ℂ`-space `E`, we relabel each chart of `M`
through the homeomorphism `Homeomorph.ulift : ULift M ≃ₜ M` to obtain a `ChartedSpace E (ULift M)`
whose transition maps are *literally* those of `M` (the `ULift` relabel and its inverse cancel),
hence land in `contDiffGroupoid ω 𝓘(ℂ, E)`.

The two coordinate maps `ULift.up` and `ULift.down` are then `C^ω`, because in these charts they
are the identity.  Finally, if `M` is a `LieAddGroup`, so is `ULift M`.

This file imports only Mathlib.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Algebra.LieGroup

open scoped Manifold ContDiff
open Set Topology IsManifold

namespace Jacobians.ULiftManifold

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The chart of `ULift M` at `z`: relabel `M`'s chart through `ULift M ≃ₜ M`.
As a function it is `(chartAt E z.down) ∘ ULift.down`. -/
noncomputable def chart (z : ULift.{u} M) : OpenPartialHomeomorph (ULift.{u} M) E :=
  Homeomorph.ulift.transOpenPartialHomeomorph (chartAt E z.down)

/-- `ULift M` is a charted space over `E`, with charts the relabelled charts of `M`. -/
noncomputable instance instChartedSpace : ChartedSpace E (ULift.{u} M) where
  atlas := (fun c => Homeomorph.ulift.transOpenPartialHomeomorph c) '' atlas E M
  chartAt z := chart z
  mem_chart_source z := by
    simp only [chart, Homeomorph.transOpenPartialHomeomorph_source, mem_preimage]
    exact mem_chart_source E z.down
  chart_mem_atlas z := ⟨chartAt E z.down, chart_mem_atlas E z.down, rfl⟩

omit [NormedSpace ℂ E] in
@[simp]
theorem chartAt_eq (z : ULift.{u} M) :
    (chartAt E z : OpenPartialHomeomorph (ULift.{u} M) E) = chart z := rfl

omit [NormedSpace ℂ E] in
theorem chart_apply (z w : ULift.{u} M) :
    chart (E := E) z w = chartAt E z.down w.down := rfl

omit [NormedSpace ℂ E] in
theorem chart_source (z : ULift.{u} M) :
    (chart (E := E) z).source = ULift.down ⁻¹' (chartAt E z.down).source := by
  rw [chart, Homeomorph.transOpenPartialHomeomorph_source]; rfl

omit [NormedSpace ℂ E] [ChartedSpace E M] in
/-- The transition map between two relabelled charts equals the transition map of `M` between the
underlying charts: the `ULift` relabel and its inverse cancel. This is the crux that lands the
transition maps of `ULift M` in `contDiffGroupoid`. -/
theorem trans_relabel (c c' : OpenPartialHomeomorph M E) :
    (Homeomorph.ulift.transOpenPartialHomeomorph c).symm ≫ₕ
        (Homeomorph.ulift.transOpenPartialHomeomorph c')
      = c.symm ≫ₕ c' := by
  -- Rewrite the relabel `U ≫ c` as the genuine `trans` with `U := ulift.toOpenPartialHomeomorph`,
  -- then associate so that `U.symm ≫ U` appears in the middle and collapses to `refl`.
  rw [Homeomorph.transOpenPartialHomeomorph_eq_trans,
    Homeomorph.transOpenPartialHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc, ← OpenPartialHomeomorph.trans_assoc _ _ c',
    ← Homeomorph.symm_toOpenPartialHomeomorph,
    ← Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.symm_trans_self,
    Homeomorph.refl_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]

/-- `ULift M` is a `C^ω` manifold modelled on `E`: its transition maps are those of `M`,
hence lie in `contDiffGroupoid ω 𝓘(ℂ, E)`. -/
instance instIsManifold [IsManifold 𝓘(ℂ, E) ω M] :
    IsManifold 𝓘(ℂ, E) ω (ULift.{u} M) := by
  refine IsManifold.mk' (gr := ⟨?_⟩)
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  rw [trans_relabel]
  exact StructureGroupoid.compatible _ hc hc'

section Smooth

variable [IsManifold 𝓘(ℂ, E) ω M]

/-- `ULift.down : ULift M → M` is `C^ω`.

Near `x`, on the chart source, it factors as `(M-chart at x.down).symm ∘ (ULift-chart at x)`,
both of which are `C^ω`: the relabelled charts make `down` the identity in coordinates. -/
theorem contMDiff_uliftDown :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (ULift.down : ULift.{u} M → M) := by
  intro x
  -- The two `C^ω` factors at `x`.
  have hchart : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E x) x :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (mem_chart_source E x)
  have hsymm : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E x.down).symm (chartAt E x x) := by
    refine contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas x.down) ?_
    simp only [chartAt_eq, chart_apply]
    exact (chartAt E x.down).map_source (mem_chart_source E x.down)
  -- `down` agrees with the composite on a neighbourhood of `x`.
  refine ((hsymm.comp x hchart).congr_of_eventuallyEq ?_)
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with w hw
  simp only [chartAt_eq, chart_source, mem_preimage] at hw
  show w.down = (chartAt E x.down).symm (chartAt E x w)
  simp only [chartAt_eq, chart_apply, (chartAt E x.down).left_inv hw]

/-- `ULift.up : M → ULift M` is `C^ω`.

Near `m`, on the chart source, it factors as `(ULift-chart at up m).symm ∘ (M-chart at m)`. -/
theorem contMDiff_uliftUp :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (ULift.up : M → ULift.{u} M) := by
  intro m
  have hchart : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E m) m :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas m) (mem_chart_source E m)
  have hsymm : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω
      (chartAt E (ULift.up.{u} m)).symm (chartAt E m m) := by
    refine contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (ULift.up.{u} m)) ?_
    simp only [chartAt_eq]
    exact (chartAt E m).map_source (mem_chart_source E m)
  refine ((hsymm.comp m hchart).congr_of_eventuallyEq ?_)
  filter_upwards [(chartAt E m).open_source.mem_nhds (mem_chart_source E m)] with w hw
  show ULift.up.{u} w = (chartAt E (ULift.up.{u} m)).symm (chartAt E m w)
  simp only [chartAt_eq]
  exact congrArg ULift.up ((chartAt E m).left_inv hw).symm

end Smooth

section Transported

/-- `ULift M` is Hausdorff if `M` is. (Mathlib already provides `ULift.instT2Space`; we restate
it here so that the manifold-level facts of this file form a self-contained package.) -/
example [T2Space M] : T2Space (ULift.{u} M) := inferInstance

/-- `ULift M` is compact if `M` is. (Mathlib already provides `ULift.compactSpace`.) -/
example [CompactSpace M] : CompactSpace (ULift.{u} M) := inferInstance

section LieGroup

variable [AddCommGroup M] [IsTopologicalAddGroup M] [LieAddGroup 𝓘(ℂ, E) ω M]

/-- If `M` is an additive Lie group, so is `ULift M`: addition and negation are conjugates, via
`ULift.up`/`ULift.down`, of the smooth operations on `M`, hence smooth.

`ULift M` already carries `AddCommGroup` and `IsTopologicalAddGroup` instances from Mathlib. -/
instance instLieAddGroup : LieAddGroup 𝓘(ℂ, E) ω (ULift.{u} M) where
  contMDiff_add := by
    -- `(p.1 + p.2) = up ((down p.1) + (down p.2))`: conjugate `M`'s smooth addition.
    have h : (fun p : ULift.{u} M × ULift.{u} M => p.1 + p.2)
        = ULift.up ∘ (fun q : M × M => q.1 + q.2) ∘ Prod.map ULift.down ULift.down := by
      funext p; exact ULift.ext _ _ ULift.add_down
    rw [h]
    exact contMDiff_uliftUp.comp
      ((contMDiff_add 𝓘(ℂ, E) ω).comp (contMDiff_uliftDown.prodMap contMDiff_uliftDown))
  contMDiff_neg := by
    -- `(-a) = up (-(down a))`: conjugate `M`'s smooth negation.
    have h : (fun a : ULift.{u} M => -a) = ULift.up ∘ (fun b : M => -b) ∘ ULift.down := by
      funext a; exact ULift.ext _ _ ULift.neg_down
    rw [h]
    exact contMDiff_uliftUp.comp ((contMDiff_neg 𝓘(ℂ, E) ω).comp contMDiff_uliftDown)

end LieGroup

end Transported

end Jacobians.ULiftManifold
