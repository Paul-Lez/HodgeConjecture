import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import KirovDolbeault.ChartedSpaceOfLocalHomeomorph

/-!
# Quotient of a finite-dimensional normed space by a `ZLattice`

Supporting theory for the `Jacobian X` construction.
Given `Λ : Submodule ℤ E` with `[DiscreteTopology Λ]` and `[IsZLattice ℝ Λ]`:

* `AddCommGroup (E ⧸ Λ.toAddSubgroup)` — automatic.
* `TopologicalSpace`, `T2Space`, `T3Space`, `IsTopologicalAddGroup` — automatic
  (via `AddSubgroup.isClosed_of_discrete` and `QuotientAddGroup.instT3Space`).
* `CompactSpace (E ⧸ Λ.toAddSubgroup)` — proven via
  `IsZLattice.isCompact_range_of_periodic`.
* `QuotientAddGroup.mk : E → E ⧸ Λ` is a covering map / local homeomorphism,
  which will be the foundation for the (still-to-come) `ChartedSpace E (E ⧸ Λ)`
  and `LieAddGroup` instances.

## References

Lee, *Introduction to Smooth Manifolds*, Ch. 21 (quotient Lie groups).
-/

set_option linter.unusedSectionVars false

namespace Jacobians.ZLatticeQuotient

/-! ### Covering-map structure

Works for any commutative topological group `E` with a discrete subgroup `Λ` —
no normed / finite-dim assumption needed. -/
section CoveringMap

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  (Λ : AddSubgroup E) [DiscreteTopology Λ]

/-- The quotient map `E → E ⧸ Λ` is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap (QuotientAddGroup.mk : E → E ⧸ Λ) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm _
    DiscreteTopology.isDiscrete).isCoveringMap

/-- The quotient map `E → E ⧸ Λ` is a local homeomorphism. -/
theorem isLocalHomeomorph_mk :
    IsLocalHomeomorph (QuotientAddGroup.mk : E → E ⧸ Λ) :=
  (isCoveringMap_mk Λ).isLocalHomeomorph

/-- The quotient map `E → E ⧸ Λ` is an open map. -/
theorem isOpenMap_mk : IsOpenMap (QuotientAddGroup.mk : E → E ⧸ Λ) :=
  (isLocalHomeomorph_mk Λ).isOpenMap

/-- Charted space structure on `E ⧸ Λ` modelled on `E`, coming from the fact
that the quotient map is a surjective local homeomorphism. -/
noncomputable instance chartedSpaceQuotient : ChartedSpace E (E ⧸ Λ) :=
  (isLocalHomeomorph_mk Λ).chartedSpaceOfAtPreimage QuotientAddGroup.mk_surjective

end CoveringMap

/-! ### Lie-group scaffolding instances on `E ⧸ Λ`

For `E` a finite-dim normed real space and `Λ` a `ZLattice`. -/
section ZLatticeInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- `DiscreteTopology` transfers from `Λ : Submodule ℤ E` to `Λ.toAddSubgroup`. -/
instance : DiscreteTopology Λ.toAddSubgroup := ‹DiscreteTopology Λ›

/-- The quotient `E ⧸ Λ` is compact. The quotient map is continuous,
periodic with respect to `Λ`, and surjective, so its range (the whole
quotient) is compact by `IsZLattice.isCompact_range_of_periodic`. -/
instance instCompactSpaceQuotient : CompactSpace (E ⧸ Λ.toAddSubgroup) := by
  rw [← isCompact_univ_iff,
      ← Set.range_eq_univ.mpr (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup))]
  refine IsZLattice.isCompact_range_of_periodic Λ _
    QuotientAddGroup.continuous_mk ?_
  intro z w hw
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hw)

example : AddCommGroup (E ⧸ Λ.toAddSubgroup) := inferInstance
example : TopologicalSpace (E ⧸ Λ.toAddSubgroup) := inferInstance
example : IsTopologicalAddGroup (E ⧸ Λ.toAddSubgroup) := inferInstance
example : T2Space (E ⧸ Λ.toAddSubgroup) := inferInstance
example : T3Space (E ⧸ Λ.toAddSubgroup) := inferInstance
example : CompactSpace (E ⧸ Λ.toAddSubgroup) := inferInstance
noncomputable example : ChartedSpace E (E ⧸ Λ.toAddSubgroup) := inferInstance

end ZLatticeInstances

/-! ### Manifold and Lie-group instances (sorried, proof-sketch documented)

The `IsManifold` and `LieAddGroup` instances on `E ⧸ Λ` are not yet closed;
they reduce to "transition maps between quotient charts are analytic",
which requires a locally-constant-lattice-translation argument that is a
substantial formalization step. Sketched below and left as TODO.

## Proof sketch for `IsManifold 𝓘(𝕜, E) n (E ⧸ Λ)`

Apply `isManifold_of_contDiffOn`. Charts `e, e'` in the atlas come from
`IsLocalHomeomorph.chartedSpace`, so each is `P.symm` for some
`P : OpenPartialHomeomorph E (E ⧸ Λ)` agreeing with `QuotientAddGroup.mk`
on its source. The transition `e.symm ≫ₕ e' = P ≫ₕ P'.symm : E → E`
sends `x ∈ P.source` with `mk x ∈ P'.target` to the unique `y ∈ P'.source`
with `mk y = mk x`, i.e. `y = x + λ` for some `λ ∈ Λ`.

Since `Λ` is discrete and the transition is continuous, the map `x ↦ λ`
is locally constant — on each connected component of the overlap, the
transition is literally `x ↦ x + λ₀` for a fixed `λ₀ ∈ Λ`. Translations
are analytic, so the transition is `ContDiffOn 𝕜 ω`.

## Proof sketch for `LieAddGroup`

`LieAddGroup` extends `ContMDiffAdd` and requires `ContMDiff_neg`. Both
reduce to the analyticity of addition / negation on `E ⧸ Λ`. These lift
from the analyticity of addition / negation on `E` via the quotient map,
using the fact that `QuotientAddGroup.mk` is a local homeomorphism. -/

section Manifold

open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {n : WithTop ℕ∞}

/-! ### Transitions between `mk`-matching partial homs are locally translations

Any two `OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup)` whose `toFun`s
equal `QuotientAddGroup.mk` have a composition `P ≫ₕ P'.symm : E → E`
that satisfies `(P ≫ₕ P'.symm) y - y ∈ Λ`. Since `Λ` is discrete and
the composition is continuous, the difference is locally constant,
hence the composition is locally a translation. -/

/-- Step 1: transition displacement lies in the lattice. -/
theorem transition_sub_mem_lattice
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup))
    (hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    (hP' : (P' : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    {y : E} (hy : y ∈ (P ≫ₕ P'.symm).source) :
    (P ≫ₕ P'.symm) y - y ∈ Λ.toAddSubgroup := by
  rw [← QuotientAddGroup.eq_iff_sub_mem]
  -- Goal: (mk ((P ≫ₕ P'.symm) y) : E⧸Λ) = mk y.
  rw [OpenPartialHomeomorph.trans_apply]
  -- Goal: (mk (P'.symm (P y)) : _) = mk y.
  rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source] at hy
  -- hy : y ∈ P.source ∧ P y ∈ P'.target.
  have hPy : P y ∈ P'.target := hy.2
  have key : (P' (P'.symm (P y)) : E ⧸ Λ.toAddSubgroup) = P y :=
    P'.right_inv hPy
  calc (QuotientAddGroup.mk (P'.symm (P y)) : E ⧸ Λ.toAddSubgroup)
      = P' (P'.symm (P y)) := by rw [← hP']
    _ = P y               := key
    _ = QuotientAddGroup.mk y := by rw [hP]

/-- Step 2 + 3: the displacement `y ↦ transition y - y` is continuous. -/
theorem transition_displacement_continuousOn
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup)) :
    ContinuousOn (fun y : E => (P ≫ₕ P'.symm) y - y) (P ≫ₕ P'.symm).source :=
  ((P ≫ₕ P'.symm).continuousOn).sub continuousOn_id

/-- Step 4: near any point of the source, the displacement is constant.

Proof: displacement `d` is continuous on `T.source` (open) into `E`,
with values in `Λ`. `Λ` is discrete in `E`, so near `y₀` the value
`d y` must equal `d y₀`. -/
theorem transition_displacement_eventuallyEq
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup))
    (hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    (hP' : (P' : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    {y₀ : E} (hy₀ : y₀ ∈ (P ≫ₕ P'.symm).source) :
    ∀ᶠ y in 𝓝 y₀, (P ≫ₕ P'.symm) y - y = (P ≫ₕ P'.symm) y₀ - y₀ := by
  set T := P ≫ₕ P'.symm
  set d : E → E := fun y => T y - y
  -- The restriction of `d` to `T.source` is a continuous map into `Λ.toAddSubgroup`
  -- (a subtype with the discrete topology).
  let drestr : T.source → (Λ.toAddSubgroup : Set E) :=
    fun ⟨y, hy⟩ => ⟨d y, transition_sub_mem_lattice Λ P P' hP hP' hy⟩
  have hd_cont : ContinuousOn d T.source :=
    transition_displacement_continuousOn Λ P P'
  have hdrestr_cont : Continuous drestr := by
    refine continuous_induced_rng.mpr ?_
    exact hd_cont.comp_continuous continuous_subtype_val Subtype.property
  -- Target has the discrete topology (as a subspace of E via the Λ coercion).
  -- So `drestr` is locally constant.
  have hlc : IsLocallyConstant drestr :=
    (IsLocallyConstant.iff_continuous drestr).mpr hdrestr_cont
  -- From local constancy on the subtype we get eventual equality within 𝓝 ⟨y₀, hy₀⟩.
  have hsub := hlc.eventually_eq ⟨y₀, hy₀⟩
  -- Transport to 𝓝 y₀ via the open-embedding `Subtype.val : T.source → E`.
  have hopen : IsOpen (T.source : Set E) := T.open_source
  have hemb : Topology.IsOpenEmbedding (Subtype.val : T.source → E) :=
    hopen.isOpenEmbedding_subtypeVal
  -- The filter `𝓝 y₀` on E, restricted to the image, corresponds to the
  -- subtype filter at ⟨y₀, hy₀⟩.
  -- Specifically, `𝓝 (⟨y₀, hy₀⟩ : T.source) = Filter.comap Subtype.val (𝓝 y₀)`.
  rw [hemb.nhds_eq_comap ⟨y₀, hy₀⟩] at hsub
  -- Push through via `Filter.eventually_comap` to get the result on E.
  filter_upwards [hopen.mem_nhds hy₀, Filter.eventually_comap.mp hsub] with y hy_src hy_eq
  have := hy_eq ⟨y, hy_src⟩ rfl
  exact congrArg Subtype.val this

/-- Step 5: the transition between `mk`-matching partial homs is
`ContDiffOn 𝕜 n` on its source. Near any point of the source, the
transition equals a translation by a fixed lattice element (step 4),
and translations are `ContDiff`. -/
theorem transition_contDiffOn_of_agrees_with_mk
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup))
    (hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    (hP' : (P' : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk) :
    ContDiffOn 𝕜 n (P ≫ₕ P'.symm : E → E) (P ≫ₕ P'.symm).source := by
  intro y₀ hy₀
  set T := P ≫ₕ P'.symm
  -- The transition equals a translation in a neighborhood of y₀
  have heq : (fun y : E => T y) =ᶠ[𝓝 y₀] (fun y : E => y + (T y₀ - y₀)) := by
    filter_upwards [transition_displacement_eventuallyEq Λ P P' hP hP' hy₀] with y hy
    -- hy : T y - y = T y₀ - y₀.  Rearranging: T y = y + (T y₀ - y₀).
    have : T y = y + (T y - y) := by abel
    rw [this, hy]
  -- Translation is ContDiff
  have htrans : ContDiff 𝕜 n (fun y : E => y + (T y₀ - y₀)) :=
    contDiff_id.add contDiff_const
  -- Combine
  exact (htrans.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The analytic manifold structure on `E ⧸ Λ`. -/
noncomputable instance instIsManifoldQuotient :
    IsManifold 𝓘(𝕜, E) n (E ⧸ Λ.toAddSubgroup) := by
  refine isManifold_of_contDiffOn _ _ _ ?_
  intro e e' he he'
  obtain ⟨q₁, rfl⟩ := he
  obtain ⟨q₂, rfl⟩ := he'
  set x₁ := Classical.choose (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₁)
  set x₂ := Classical.choose (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₂)
  set P₁ := IsLocalHomeomorph.chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x₁
  set P₂ := IsLocalHomeomorph.chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x₂
  have hP₁ : (P₁ : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x₁).symm
  have hP₂ : (P₂ : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x₂).symm
  -- Simplify away the trivial model / range-of-model
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Set.range_id, Set.preimage_id,
    Set.inter_univ, OpenPartialHomeomorph.symm_symm]
  exact transition_contDiffOn_of_agrees_with_mk Λ P₁ P₂ hP₁ hP₂

/-! ### Section lemma: `P.symm ∘ mk` is analytic on `mk ⁻¹ P.target`

Given any `P : OpenPartialHomeomorph E (E ⧸ Λ)` agreeing with `mk`, the
composition `y ↦ P.symm (mk y)` is `ContDiffOn 𝕜 n` on the preimage of
`P.target`. This is the core ingredient for `LieAddGroup`: chart pullbacks
of the group operations on `E ⧸ Λ` factor through this map composed with
operations on `E`. -/

theorem contDiffOn_symm_mk
    (P : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup))
    (hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk) :
    ContDiffOn 𝕜 n
      (fun y : E => P.symm (QuotientAddGroup.mk y : E ⧸ Λ.toAddSubgroup))
      ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' P.target) := by
  intro y₀ hy₀
  -- Choose a local chart P₀ around y₀ agreeing with mk
  set P₀ := IsLocalHomeomorph.chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) y₀
  have hP₀ : (P₀ : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) y₀).symm
  -- y₀ is in the transition's source
  have hy₀_P₀ : y₀ ∈ P₀.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  have hy₀_src : y₀ ∈ (P₀ ≫ₕ P.symm).source := by
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
        OpenPartialHomeomorph.symm_source]
    refine ⟨hy₀_P₀, ?_⟩
    show P₀ y₀ ∈ P.target
    rw [hP₀]; exact hy₀
  -- Transition is ContDiffOn
  have htrans : ContDiffOn 𝕜 n (P₀ ≫ₕ P.symm : E → E) (P₀ ≫ₕ P.symm).source :=
    transition_contDiffOn_of_agrees_with_mk Λ P₀ P hP₀ hP
  -- On that source, `P.symm ∘ mk` agrees with the transition
  have hcongr :
      Set.EqOn (fun y : E => P.symm (QuotientAddGroup.mk y : E ⧸ Λ.toAddSubgroup))
        (P₀ ≫ₕ P.symm : E → E) (P₀ ≫ₕ P.symm).source := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff] at hy
    -- Goal: P.symm (mk y) = (P₀ ≫ₕ P.symm) y = P.symm (P₀ y)
    rw [OpenPartialHomeomorph.trans_apply]
    have : P₀ y = QuotientAddGroup.mk y := by rw [← hP₀]
    rw [this]
  -- So the map is ContDiffAt y₀ via the open set (P₀ ≫ₕ P.symm).source
  have hopen : IsOpen ((P₀ ≫ₕ P.symm).source : Set E) := (P₀ ≫ₕ P.symm).open_source
  have hOn : ContDiffOn 𝕜 n
      (fun y : E => P.symm (QuotientAddGroup.mk y : E ⧸ Λ.toAddSubgroup))
      (P₀ ≫ₕ P.symm).source :=
    htrans.congr (fun y hy => hcongr hy)
  have hAt : ContDiffAt 𝕜 n
      (fun y : E => P.symm (QuotientAddGroup.mk y : E ⧸ Λ.toAddSubgroup)) y₀ :=
    hOn.contDiffAt (hopen.mem_nhds hy₀_src)
  exact hAt.contDiffWithinAt

/-! ### Smoothness of the group operations on `E ⧸ Λ`

The approach: each chart `chartAt q` on `E ⧸ Λ` unfolds (via
`IsLocalHomeomorph.chartedSpace`) to the inverse of an
`OpenPartialHomeomorph E (E ⧸ Λ)` agreeing with `mk`. So chart pullbacks
of `add` and `neg` become expressions of the form `P.symm ∘ mk ∘ f`
for a `ContDiff` `f : E → E` (or `f : E × E → E`). By `contDiffOn_symm_mk`
the outer factor is `ContDiff` on its natural domain, and the composite
is then `ContDiff`. -/


/-- The **quotient projection** `mk : E → E ⧸ Λ.toAddSubgroup` is `ContMDiff`.

The chart on `E ⧸ Λ` at `mk x` is essentially `mk⁻¹` on a neighborhood
(via `IsLocalHomeomorph.chartedSpace`), so the chart-pullback of `mk`
along the trivial chart on `E` and this inverse chart is locally the
identity, hence `ContDiff`. The proof mirrors the structure of
`contMDiff_neg` but with `id` in place of the `neg` ambient map. -/
theorem contMDiff_mk : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n
    (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) := by
  intro x₀
  -- Set up the local chart structure at mk x₀.
  set q := (QuotientAddGroup.mk x₀ : E ⧸ Λ.toAddSubgroup) with hq_def
  set x_c := Classical.choose
    (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q) with hxc_def
  have hqc : QuotientAddGroup.mk x_c = q :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q)
  set P := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk Λ.toAddSubgroup) x_c with hP_def
  have hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x_c).symm
  have hxc_mem : x_c ∈ P.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  -- mk x₀ ∈ P.target: P x_c = mk x_c = q = mk x₀, and P maps source to target.
  have hq_in_P : q ∈ P.target := by
    have : P x_c = q := by rw [hP]; exact hqc
    rw [← this]; exact P.map_source hxc_mem
  have hx_pre : x₀ ∈ (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' P.target := by
    show QuotientAddGroup.mk x₀ ∈ P.target
    rw [show QuotientAddGroup.mk x₀ = q from rfl]; exact hq_in_P
  -- Now derive ContMDiffAt.
  rw [contMDiffAt_iff]
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  simp only [modelWithCornersSelf_coe, Set.range_id]
  rw [contDiffWithinAt_univ]
  -- The required ContDiffAt is for the chart pullback.
  -- chartAt at mk x₀ is P.symm; chartAt at x₀ on E is identity.
  -- So pullback is fun y ↦ P.symm (mk y), which is ContDiffAt at x₀ by
  -- `contDiffOn_symm_mk` since x₀ ∈ mk⁻¹ P.target.
  have h_at : ContDiffAt 𝕜 n
      (fun y : E => P.symm (QuotientAddGroup.mk y : E ⧸ Λ.toAddSubgroup)) x₀ := by
    apply (contDiffOn_symm_mk Λ P hP).contDiffAt
    exact (QuotientAddGroup.continuous_mk.isOpen_preimage _ P.open_target).mem_nhds hx_pre
  -- extChartAt 𝓘(𝕜, E) x₀ x₀ = x₀ (trivial chart on E).
  have hpoint : extChartAt 𝓘(𝕜, E) x₀ x₀ = x₀ := by
    show (chartAt E x₀) x₀ = x₀
    rfl
  rw [hpoint]
  -- The required pullback eventually equals fun y ↦ P.symm (mk y) near x₀.
  apply h_at.congr_of_eventuallyEq
  filter_upwards with y
  -- extChartAt _ q (mk y) = chartAt q (mk y) = P.symm (mk y) by definition.
  rfl

/-- The negation map `q ↦ -q` on `E ⧸ Λ` is `ContMDiff`. -/
theorem contMDiff_neg :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n
      (fun q : E ⧸ Λ.toAddSubgroup => -q) := by
  intro q₀
  -- Extract chart data from our ChartedSpace instance
  set x_c := Classical.choose
    (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₀) with hxc_def
  have hqc : QuotientAddGroup.mk x_c = q₀ :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₀)
  set y_c := Classical.choose
    (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) (-q₀)) with hyc_def
  have hync : QuotientAddGroup.mk y_c = -q₀ :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) (-q₀))
  -- Chart P around x_c, chart Q around y_c
  set P := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk Λ.toAddSubgroup) x_c with hP_def
  set Q := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk Λ.toAddSubgroup) y_c with hQ_def
  have hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x_c).symm
  have hQ : (Q : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) y_c).symm
  have hxc_mem : x_c ∈ P.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  have hyc_mem : y_c ∈ Q.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  -- Apply contMDiffAt_iff to reduce to chart pullback smoothness
  rw [contMDiffAt_iff]
  refine ⟨continuous_neg.continuousAt, ?_⟩
  -- chartAt on our ChartedSpace: chartAt q₀ = P.symm (since P := chartAtPreimageKirov x_c
  -- and x_c = Classical.choose (mk_surjective q₀))
  -- extChartAt with trivial model coincides with chartAt as a function.
  -- Range 𝓘(𝕜, E) = univ.
  simp only [modelWithCornersSelf_coe, Set.range_id]
  -- Show: ContDiffWithinAt 𝕜 n (extChartAt 𝓘(𝕜,E) (-q₀) ∘ neg ∘ (extChartAt 𝓘(𝕜,E) q₀).symm)
  --         univ (extChartAt 𝓘(𝕜,E) q₀ q₀)
  -- Since range I = univ, ContDiffWithinAt univ = ContDiffAt.
  rw [contDiffWithinAt_univ]
  -- Show: ContDiffAt 𝕜 n (extChartAt _ (-q₀) ∘ neg ∘ (extChartAt _ q₀).symm) (extChartAt _ q₀ q₀)
  -- Now the chart pullback should equal (fun y => Q.symm (mk (-y))) on P.source, and
  -- extChartAt _ q₀ q₀ = x_c.
  -- mk(-x_c) = mk y_c since both reduce to -q₀
  have hmx : QuotientAddGroup.mk (-x_c) =
      (QuotientAddGroup.mk y_c : E ⧸ Λ.toAddSubgroup) := by
    rw [QuotientAddGroup.mk_neg, hqc, hync]
  -- (-x_c) ∈ mk ⁻¹ Q.target
  have hmem_neg : (-x_c) ∈
      (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' Q.target := by
    show QuotientAddGroup.mk (-x_c) ∈ Q.target
    rw [hmx]
    have hQy : Q y_c = QuotientAddGroup.mk y_c := by rw [← hQ]
    rw [← hQy]
    exact Q.map_source hyc_mem
  have hopen_Q : IsOpen
      ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' Q.target) :=
    QuotientAddGroup.continuous_mk.isOpen_preimage _ Q.open_target
  have hneg_E : ContDiff 𝕜 n (fun y : E => -y) := contDiff_neg
  have hcomp_on : ContDiffOn 𝕜 n
      (fun y : E => Q.symm (QuotientAddGroup.mk (-y) : E ⧸ Λ.toAddSubgroup))
      ((fun y : E => -y) ⁻¹'
        ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' Q.target)) := by
    apply (contDiffOn_symm_mk Λ Q hQ).comp hneg_E.contDiffOn
    intro y hy; exact hy
  have hmem_neg_pre :
      x_c ∈ (fun y : E => -y) ⁻¹'
        ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' Q.target) := hmem_neg
  have hopen_neg_pre : IsOpen
      ((fun y : E => -y) ⁻¹'
        ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' Q.target)) :=
    continuous_neg.isOpen_preimage _ hopen_Q
  have hkey : ContDiffAt 𝕜 n
      (fun y : E => Q.symm (QuotientAddGroup.mk (-y) : E ⧸ Λ.toAddSubgroup)) x_c :=
    hcomp_on.contDiffAt (hopen_neg_pre.mem_nhds hmem_neg_pre)
  -- Use that the pullback equals this expression near x_c.
  -- ⇑(extChartAt _ q₀) = chartAt q₀ = P.symm (for trivial model)
  -- ⇑(extChartAt _ (-q₀)) = Q.symm
  -- At extChartAt _ q₀ q₀ = P.symm q₀ = x_c
  -- Pullback(y) = Q.symm (neg (P.symm.symm y)) = Q.symm (neg (P y)) = Q.symm (neg (mk y))
  --            = Q.symm (mk (-y)) on P.source
  have hpoint : extChartAt 𝓘(𝕜, E) q₀ q₀ = x_c := by
    show (chartAt E q₀) q₀ = x_c
    -- chartAt q₀ = P.symm, (P.symm) q₀ = x_c since P x_c = mk x_c = q₀ and x_c ∈ P.source
    show P.symm q₀ = x_c
    have : P x_c = q₀ := by rw [hP]; exact hqc
    rw [← this]
    exact P.left_inv hxc_mem
  rw [hpoint]
  apply hkey.congr_of_eventuallyEq
  -- Eventually equal near x_c
  have hP_source_open : IsOpen (P.source : Set E) := P.open_source
  filter_upwards [hP_source_open.mem_nhds hxc_mem] with y hy
  -- Reduce via defeq: extChartAt with trivial model = chartAt as functions.
  change Q.symm (- (P y)) = Q.symm (QuotientAddGroup.mk (-y) : E ⧸ Λ.toAddSubgroup)
  -- Now rewrite P y = mk y (since y ∈ P.source and P agrees with mk)
  have h3 : P y = QuotientAddGroup.mk y := by rw [← hP]
  rw [h3]
  rw [QuotientAddGroup.mk_neg]


/-- Addition on `E ⧸ Λ` is `ContMDiff`. -/
theorem contMDiff_add :
    ContMDiff (𝓘(𝕜, E).prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n
      (fun p : (E ⧸ Λ.toAddSubgroup) × (E ⧸ Λ.toAddSubgroup) => p.1 + p.2) := by
  intro ⟨q₁, q₂⟩
  -- Preimages for source charts
  set x₁ := Classical.choose
    (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₁)
  have hq₁ : QuotientAddGroup.mk x₁ = q₁ :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₁)
  set x₂ := Classical.choose
    (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₂)
  have hq₂ : QuotientAddGroup.mk x₂ = q₂ :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₂)
  -- Preimage for target chart
  set x₃ := Classical.choose
    (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) (q₁ + q₂))
  have hq₃ : QuotientAddGroup.mk x₃ = q₁ + q₂ :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) (q₁ + q₂))
  -- Charts
  set P₁ := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk Λ.toAddSubgroup) x₁
  set P₂ := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk Λ.toAddSubgroup) x₂
  set R := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk Λ.toAddSubgroup) x₃
  have hP₁ : (P₁ : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x₁).symm
  have hP₂ : (P₂ : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x₂).symm
  have hR : (R : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov (isLocalHomeomorph_mk Λ.toAddSubgroup) x₃).symm
  have hx₁_mem : x₁ ∈ P₁.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  have hx₂_mem : x₂ ∈ P₂.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  have hx₃_mem : x₃ ∈ R.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  -- Reduce to chart pullback ContDiffAt
  rw [contMDiffAt_iff]
  refine ⟨continuous_add.continuousAt, ?_⟩
  -- Set.range (I.prod I) = univ for trivial models
  have hrange : (Set.range ((𝓘(𝕜, E)).prod (𝓘(𝕜, E)) :
      ModelWithCorners 𝕜 (E × E) (E × E))) = Set.univ := by
    rw [ModelWithCorners.range_prod]
    simp [Set.range_id]
  rw [hrange, contDiffWithinAt_univ]
  have hmem_sum : (x₁ + x₂) ∈
      (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' R.target := by
    show QuotientAddGroup.mk (x₁ + x₂) ∈ R.target
    have hmksum : (QuotientAddGroup.mk (x₁ + x₂) : E ⧸ Λ.toAddSubgroup) =
        QuotientAddGroup.mk x₃ := by
      rw [QuotientAddGroup.mk_add, hq₁, hq₂, hq₃]
    rw [hmksum]
    have hRy : R x₃ = QuotientAddGroup.mk x₃ := by rw [← hR]
    rw [← hRy]
    exact R.map_source hx₃_mem
  have hopen_R : IsOpen
      ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' R.target) :=
    QuotientAddGroup.continuous_mk.isOpen_preimage _ R.open_target
  -- Use ContDiffOn.comp directly at the ContDiffOn level to avoid unification issues
  have hadd_E : ContDiff 𝕜 n (fun p : E × E => p.1 + p.2) := contDiff_add
  have hcomp_on : ContDiffOn 𝕜 n
      (fun p : E × E => R.symm (QuotientAddGroup.mk (p.1 + p.2) : E ⧸ Λ.toAddSubgroup))
      ((fun p : E × E => p.1 + p.2) ⁻¹'
        ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' R.target)) := by
    apply (contDiffOn_symm_mk Λ R hR).comp hadd_E.contDiffOn
    intro p hp; exact hp
  have hmem_prod :
      ((x₁, x₂) : E × E) ∈
      (fun p : E × E => p.1 + p.2) ⁻¹'
        ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' R.target) := hmem_sum
  have hopen_prod : IsOpen
      ((fun p : E × E => p.1 + p.2) ⁻¹'
        ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' R.target)) :=
    continuous_add.isOpen_preimage _ hopen_R
  have hkey : ContDiffAt 𝕜 n
      (fun p : E × E => R.symm (QuotientAddGroup.mk (p.1 + p.2) : E ⧸ Λ.toAddSubgroup))
      (x₁, x₂) :=
    hcomp_on.contDiffAt (hopen_prod.mem_nhds hmem_prod)
  have hpoint : extChartAt (𝓘(𝕜, E).prod 𝓘(𝕜, E)) (q₁, q₂) (q₁, q₂) = (x₁, x₂) := by
    show (P₁.symm q₁, P₂.symm q₂) = (x₁, x₂)
    ext
    · have hpq : P₁ x₁ = q₁ := by rw [hP₁]; exact hq₁
      rw [← hpq]; exact P₁.left_inv hx₁_mem
    · have hpq : P₂ x₂ = q₂ := by rw [hP₂]; exact hq₂
      rw [← hpq]; exact P₂.left_inv hx₂_mem
  rw [hpoint]
  apply hkey.congr_of_eventuallyEq
  -- Eventually equal near (x₁, x₂)
  have hP₁_open : IsOpen (P₁.source : Set E) := P₁.open_source
  have hP₂_open : IsOpen (P₂.source : Set E) := P₂.open_source
  have hprod_mem : ((x₁, x₂) : E × E) ∈ P₁.source ×ˢ P₂.source :=
    ⟨hx₁_mem, hx₂_mem⟩
  have hprod_open : IsOpen (P₁.source ×ˢ P₂.source : Set (E × E)) :=
    hP₁_open.prod hP₂_open
  filter_upwards [hprod_open.mem_nhds hprod_mem] with p hp
  obtain ⟨hy₁, hy₂⟩ := hp
  -- Goal: chart pullback = fun p => R.symm (mk (p.1 + p.2))
  -- extChartAt on product is product of extChartAts, so the pullback through
  -- (extChartAt (q₁, q₂)).symm = (P₁, P₂), and extChartAt at q₁+q₂ = R.symm.
  change R.symm (P₁ p.1 + P₂ p.2) = R.symm (QuotientAddGroup.mk (p.1 + p.2) :
      E ⧸ Λ.toAddSubgroup)
  have h4 : P₁ p.1 = QuotientAddGroup.mk p.1 := by rw [← hP₁]
  have h5 : P₂ p.2 = QuotientAddGroup.mk p.2 := by rw [← hP₂]
  rw [h4, h5]
  congr 1

/-- The analytic Lie-group structure on `E ⧸ Λ`. -/
noncomputable instance instLieAddGroupQuotient :
    LieAddGroup 𝓘(𝕜, E) n (E ⧸ Λ.toAddSubgroup) where
  contMDiff_add := contMDiff_add Λ
  contMDiff_neg := contMDiff_neg Λ

end Manifold

/-! ### Descent of linear maps to morphisms between ZLattice quotients

Given a lattice-respecting continuous ℝ-linear map between ambient spaces,
this section builds the induced group morphism between the corresponding
quotient tori and proves functoriality + the descent of the "degree
identity" `Φ ∘ Ψ = d • id` from the ambient to the quotient.

This is what makes the challenge's `pushforward_pullback = deg • id`
tractable once we have the ambient linear maps with the right degree
identity — the quotient side is structurally automatic. -/

section LatticeMorphisms

open scoped Manifold ContDiff

noncomputable section

/-- The descended pushforward map on quotient tori, from a lattice-respecting
ambient ℂ-linear map. (The body uses only `Φ.toAddMonoidHom` and
`Φ.continuous`, so `→L[ℂ]` vs `→L[ℝ]` doesn't matter for the
construction; we take `→L[ℂ]` here because the downstream
`pushforward_contMDiff_of_ambient` needs the ℂ-linearity for
`ContDiff ℂ ω Φ`.) -/
def pushforward {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Φ : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom) :
    ((Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) →ₜ+ ((Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) where
  toFun := QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ
  map_zero' := (QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ).map_zero
  map_add' := (QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ).map_add
  continuous_toFun :=
    continuous_quot_lift _ (QuotientAddGroup.continuous_mk.comp Φ.continuous)

/-- The descended pullback map (dual direction). Defined via `pushforward`. -/
def pullback {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Ψ : (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ))
    (hΨ : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Ψ.toAddMonoidHom) :
    ((Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) →ₜ+ ((Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) :=
  pushforward ΛY ΛX Ψ hΨ

/-- Headline: the degree identity `Φ ∘ Ψ = d • id` on the ambient
descends to `pushforward ∘ pullback = d • id` on the quotient. -/
theorem pushforward_pullback_of_ambient
    {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Φ : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ))
    (Ψ : (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom)
    (hΨ : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Ψ.toAddMonoidHom)
    (d : ℕ)
    (hΦΨ : ∀ y : (Fin gY → ℂ), Φ (Ψ y) = (d : ℕ) • y)
    (P : (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) :
    pushforward ΛX ΛY Φ hΦ (pullback ΛX ΛY Ψ hΨ P) = d • P := by
  induction P using QuotientAddGroup.induction_on with
  | H y =>
    show (QuotientAddGroup.mk (Φ (Ψ y)) : _) = d • (QuotientAddGroup.mk y : _)
    rw [hΦΨ y]
    simp

/-- Functoriality: ambient identity descends to quotient identity. -/
theorem pushforward_id_of_ambient
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hΦΛ : Λ.toAddSubgroup ≤ Λ.toAddSubgroup.comap Φ.toAddMonoidHom)
    (hΦid : ∀ x : (Fin g → ℂ), Φ x = x)
    (P : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) :
    pushforward Λ Λ Φ hΦΛ P = P := by
  induction P using QuotientAddGroup.induction_on with
  | H x =>
    show (QuotientAddGroup.mk (Φ x) : _) = _
    rw [hΦid]

/-- Functoriality: ambient composition descends to quotient composition. -/
theorem pushforward_comp_of_ambient
    {gX gY gZ : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (ΛZ : Submodule ℤ (Fin gZ → ℂ))
    (Φ₁ : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ))
    (Φ₂ : (Fin gY → ℂ) →L[ℂ] (Fin gZ → ℂ))
    (hΦ₁ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ₁.toAddMonoidHom)
    (hΦ₂ : ΛY.toAddSubgroup ≤ ΛZ.toAddSubgroup.comap Φ₂.toAddMonoidHom)
    (hΦ₁₂ : ΛX.toAddSubgroup ≤ ΛZ.toAddSubgroup.comap (Φ₂.comp Φ₁).toAddMonoidHom)
    (P : (Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) :
    pushforward ΛX ΛZ (Φ₂.comp Φ₁) hΦ₁₂ P =
      pushforward ΛY ΛZ Φ₂ hΦ₂ (pushforward ΛX ΛY Φ₁ hΦ₁ P) := by
  induction P using QuotientAddGroup.induction_on with
  | H x => rfl

/-- **Smoothness**: a ℂ-linear continuous ambient map descends to a
`ContMDiff` map on the quotient tori. Uses chart-pullback +
`contDiffOn_symm_mk` + ContDiff ℂ of the ambient linear map. -/
theorem pushforward_contMDiff_of_ambient {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ))
    [DiscreteTopology ΛX] [IsZLattice ℝ ΛX]
    (ΛY : Submodule ℤ (Fin gY → ℂ))
    [DiscreteTopology ΛY] [IsZLattice ℝ ΛY]
    (Φ : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom) :
    ContMDiff 𝓘(ℂ, Fin gX → ℂ) 𝓘(ℂ, Fin gY → ℂ) ω
      (pushforward ΛX ΛY Φ hΦ : _ → _) := by
  intro qX
  set x_c := Classical.choose
    (QuotientAddGroup.mk_surjective (s := ΛX.toAddSubgroup) qX)
  have hqc : QuotientAddGroup.mk x_c = qX :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := ΛX.toAddSubgroup) qX)
  set target_q := (pushforward ΛX ΛY Φ hΦ qX :
    (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) with htgt_def
  set y_c := Classical.choose
    (QuotientAddGroup.mk_surjective (s := ΛY.toAddSubgroup) target_q)
  have hyc : QuotientAddGroup.mk y_c = target_q :=
    Classical.choose_spec
      (QuotientAddGroup.mk_surjective (s := ΛY.toAddSubgroup) target_q)
  set P := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk ΛX.toAddSubgroup) x_c
  set R := IsLocalHomeomorph.chartAtPreimageKirov
    (isLocalHomeomorph_mk ΛY.toAddSubgroup) y_c
  have hP : (P : (Fin gX → ℂ) → (Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) =
      QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov
      (isLocalHomeomorph_mk ΛX.toAddSubgroup) x_c).symm
  have hR : (R : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) =
      QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimageKirov
      (isLocalHomeomorph_mk ΛY.toAddSubgroup) y_c).symm
  have hxc_mem : x_c ∈ P.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  have hyc_mem : y_c ∈ R.source :=
    IsLocalHomeomorph.mem_source_chartAtPreimageKirov _ _
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · exact (continuous_quot_lift _
      (QuotientAddGroup.continuous_mk.comp Φ.continuous)).continuousAt
  have hΦ_diff : ContDiff ℂ ω (Φ : (Fin gX → ℂ) → (Fin gY → ℂ)) := Φ.contDiff
  have hR_sec := contDiffOn_symm_mk (𝕜 := ℂ) (n := ω) ΛY R hR
  have hmem_img : Φ x_c ∈
      (QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
        R.target := by
    show QuotientAddGroup.mk (Φ x_c) ∈ R.target
    have hmk : (QuotientAddGroup.mk (Φ x_c) :
        (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) = target_q := by
      rw [htgt_def, ← hqc]
      rfl
    rw [hmk, ← hyc]
    have hRy : R y_c = QuotientAddGroup.mk y_c := by rw [← hR]
    rw [← hRy]
    exact R.map_source hyc_mem
  have hopen_R : IsOpen
      ((QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
        R.target) :=
    QuotientAddGroup.continuous_mk.isOpen_preimage _ R.open_target
  have hcomp_on : ContDiffOn ℂ ω
      (fun x : Fin gX → ℂ => R.symm (QuotientAddGroup.mk (Φ x) :
        (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup))
      (Φ ⁻¹'
        ((QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
          R.target)) := by
    apply hR_sec.comp hΦ_diff.contDiffOn
    intro x hx; exact hx
  have hopen_pre : IsOpen (Φ ⁻¹'
      ((QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
        R.target)) :=
    Φ.continuous.isOpen_preimage _ hopen_R
  have hkey : ContDiffAt ℂ ω
      (fun x : Fin gX → ℂ => R.symm (QuotientAddGroup.mk (Φ x) :
        (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup)) x_c :=
    hcomp_on.contDiffAt (hopen_pre.mem_nhds hmem_img)
  simp only [modelWithCornersSelf_coe, Set.range_id]
  rw [contDiffWithinAt_univ]
  have hpoint : extChartAt 𝓘(ℂ, Fin gX → ℂ) qX qX = x_c := by
    show P.symm qX = x_c
    have : P x_c = qX := by rw [hP]; exact hqc
    rw [← this]
    exact P.left_inv hxc_mem
  rw [hpoint]
  apply hkey.congr_of_eventuallyEq
  have hxc_src_preimg : x_c ∈ Φ ⁻¹'
      ((QuotientAddGroup.mk : (Fin gY → ℂ) → (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) ⁻¹'
        R.target) := hmem_img
  have hP_open : IsOpen (P.source : Set (Fin gX → ℂ)) := P.open_source
  filter_upwards [hP_open.mem_nhds hxc_mem, hopen_pre.mem_nhds hxc_src_preimg]
    with x hx_src _hx_phi
  simp only [Function.comp_apply]
  change R.symm (QuotientAddGroup.map ΛX.toAddSubgroup ΛY.toAddSubgroup Φ.toAddMonoidHom
      hΦ (P x)) =
    R.symm (QuotientAddGroup.mk (Φ x) : (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup)
  have hPx : P x = QuotientAddGroup.mk x := by rw [← hP]
  rw [hPx]
  rfl

/-- Pullback smoothness, via pushforward. -/
theorem pullback_contMDiff_of_ambient {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ))
    [DiscreteTopology ΛX] [IsZLattice ℝ ΛX]
    (ΛY : Submodule ℤ (Fin gY → ℂ))
    [DiscreteTopology ΛY] [IsZLattice ℝ ΛY]
    (Ψ : (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ))
    (hΨ : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Ψ.toAddMonoidHom) :
    ContMDiff 𝓘(ℂ, Fin gY → ℂ) 𝓘(ℂ, Fin gX → ℂ) ω
      (pullback ΛX ΛY Ψ hΨ : _ → _) :=
  pushforward_contMDiff_of_ambient ΛY ΛX Ψ hΨ

end

end LatticeMorphisms

end Jacobians.ZLatticeQuotient
