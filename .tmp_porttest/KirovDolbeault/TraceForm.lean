/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.PeriodLattice
import KirovDolbeault.Discharge.Manifold.IsPathConnectedBallMinusCountable

/-!
# Trace (pushforward) of a holomorphic 1-form along a branched cover

The global assembly of `f₊ : Ω¹(X) → Ω¹(Y)` for a non-constant holomorphic map
`f : X → Y` of compact Riemann surfaces.

This file builds the trace as a **fibre sum** off the branch locus, proves it is
holomorphic there, assembles it into a global form via the branch-point
extension, and proves the projection formula at the period level.

## Design

For `ω : HolomorphicOneForms X` and `y ∉ branchLocus f`, the fibre `f⁻¹{y}` is
finite (`fiber_finite_off_branchLocus`) and every `x` in it is off `criticalSet f`,
so `mfderiv f x : T_x X →L[ℂ] T_y Y` is invertible and `(ω x) ∘ (mfderiv f x)⁻¹`
is a cotangent covector at `y`. Summing over the fibre gives the trace covector.

Holomorphicity off the branch locus is local: over a `properNbhd`-shrunk open
`V ∋ y₀` the cover splits into finitely many sheets, each carrying a holomorphic
section `s : V → X`, and on `V` the fibre sum equals `∑_k pullbackForm s_k ω`, a
finite sum of holomorphic 1-forms.

## References

Forster §§4, 10; Griffiths–Harris Ch. 2 §2.7 (the trace map for forms).
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter Set

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The covector at `y = f x` obtained by pulling back `α x` through the inverse of
`mfderiv f x`. The summand of the fibre-sum trace.

Typed in the model fibre `ℂ →L[ℂ] ℂ` (definitionally equal to `T_{f x} Y →L[ℂ] ℂ`
and to `T_y Y →L[ℂ] ℂ`, since `TangentSpace 𝓘(ℂ) _ = ℂ` reduces to `ℂ`). Working in
the model fibre means the fibre sum requires **no transport** between cotangent
spaces of different fibre points.

(NB: the form variable is `α`, not `ω` — in this codebase `ω` is the analytic
smoothness exponent `IsManifold 𝓘(ℂ) ω X`.) -/
noncomputable def traceSummand (f : X → Y) (α : HolomorphicOneForms X) (x : X) :
    ℂ →L[ℂ] ℂ :=
  (α.toFun x).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f x).inverse)

/-- Value of the single-section pullback covector `(α (g y)) ∘ mfderiv g y` at a
point `y`, in the cotangent fibre at `y`. The per-sheet term of the local
representation of the fibre-sum trace over a base neighborhood. -/
noncomputable def sheetPullback (α : HolomorphicOneForms X) (g : Y → X) (y : Y) :
    TangentSpace 𝓘(ℂ) y →L[ℂ] ℂ :=
  (α.toFun (g y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g y)

/-! ### Local pullback smoothness (`ContMDiffAt`-only)

The smoothness core of `pullbackForm`, weakened from a *global* `ContMDiff`
hypothesis on the map to a *pointwise* `ContMDiffAt`. This is what lets us pull a
form back along a local holomorphic section (`exists_holo_localInverse_…`), which
is only `ContMDiffOn` its domain. Apart from the hypothesis it is a verbatim copy
of the `pullbackForm.contMDiff_toFun` argument. -/

/-- The hom-bundle section `y ↦ (α (s y)) ∘ mfderiv s y` is `ContMDiffAt` at `y₀`
(as a section into the cotangent bundle of `Y`) whenever `s` is `ContMDiffAt` at
`y₀`. Pointwise version of `pullbackForm`'s `contMDiff_toFun` proof: the global
`ContMDiff` hypothesis there is only ever used at the single point `x₀`, so it
weakens to `ContMDiffAt`. This is what allows pulling a form back along a *local*
holomorphic section, which is only `ContMDiffOn` its domain. -/
theorem contMDiffAt_pullback_section (α : HolomorphicOneForms X) {s : Y → X} {y₀ : Y}
    (hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s y₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        ((α.toFun (s y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y))) y₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hA : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
          (s y₀) (s y) (s y₀) (s y) (α.toFun (s y))) y₀ := by
    have hα := α.contMDiff_toFun (s y₀)
    rw [contMDiffAt_hom_bundle] at hα
    obtain ⟨_, h⟩ := hα
    exact h.comp y₀ hs
  have hB : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X))
          y₀ y (s y₀) (s y) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) s y)) y₀ :=
    hs.mfderiv_const (le_refl _)
  have hcomp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => (ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
          (s y₀) (s y) (s y₀) (s y) (α.toFun (s y))).comp
        (ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X))
          y₀ y (s y₀) (s y) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) s y))) y₀ :=
    hA.clm_comp hB
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) y₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt ℂ _ y₀)),
    (hs.continuousAt.preimage_mem_nhds
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) (s y₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ℂ _ (s y₀))))
    ] with y hy_TS_Y hy_TS_X
  ext
  simp only [ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hy_TS_X]

/-- `sheetPullback α g` is `ContMDiffAt` at `y₀` whenever `g` is `ContMDiffAt`
there. Restatement of `contMDiffAt_pullback_section` in terms of `sheetPullback`
(as a section into the cotangent bundle of `Y`). -/
theorem contMDiffAt_sheetPullback (α : HolomorphicOneForms X) {g : Y → X} {y₀ : Y}
    (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g y₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (sheetPullback α g y)) y₀ :=
  contMDiffAt_pullback_section α hg

/-! ### The section's derivative is the inverse of `mfderiv f` -/

/-- For a two-sided local inverse pair `(f, s)` around `(x₀, y₀)` (i.e. `f ∘ s = id`
near `y₀` and `s ∘ f = id` near `x₀`, with `s y₀ = x₀` and `f x₀ = y₀`), the
derivative of the section is the `ContinuousLinearMap.inverse` of `mfderiv f x₀`.
Chain rule (`mfderiv_comp`) on both local identities + `mfderiv_id` +
`ContinuousLinearMap.inverse_eq`. -/
theorem mfderiv_section_eq_inverse {f : X → Y} {s : Y → X} {x₀ : X} {y₀ : Y}
    (hsx : s y₀ = x₀) (hfx : f x₀ = y₀)
    (hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x₀)
    (hs_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s y₀)
    (hfs : (f ∘ s) =ᶠ[𝓝 y₀] id) (hsf : (s ∘ f) =ᶠ[𝓝 x₀] id) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) s y₀ = (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).inverse := by
  -- f ∘ s = id near y₀  ⟹  mfderiv f x₀ ∘SL mfderiv s y₀ = id on T_{y₀} Y.
  have hcomp_fs : (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y₀) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) y₀) := by
    have h1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (f ∘ s) y₀ = mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : Y → Y) y₀ :=
      hfs.mfderiv_eq
    rw [mfderiv_id] at h1
    rw [← h1, mfderiv_comp y₀ (hsx ▸ hf_diff) hs_diff, hsx]
  -- s ∘ f = id near x₀  ⟹  mfderiv s y₀ ∘ mfderiv f x₀ = id on T_{x₀} X.
  have hcomp_sf : (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y₀).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) x₀) := by
    have h1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (s ∘ f) x₀ = mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) x₀ :=
      hsf.mfderiv_eq
    rw [mfderiv_id] at h1
    rw [← h1, mfderiv_comp x₀ (hfx ▸ hs_diff) hf_diff, hfx]
  exact (ContinuousLinearMap.inverse_eq hcomp_fs hcomp_sf).symm

/-! ### Two-sided local section at a non-critical point

Strengthens `exists_holo_localInverse_of_notMem_criticalSet` to a genuine
two-sided local inverse: combining the section `g` (a right inverse, `f ∘ g = id`
on `V`) with the local injectivity of `f` off the critical set
(`isLocalHomeoOffCritical`) gives `g ∘ f = id` on a neighborhood of `x₀` as well.
This is exactly the data `mfderiv_section_eq_inverse` and
`contMDiffAt_pullback_section` consume. -/

/-- A `C^ω` two-sided local inverse `g` at a non-critical point `x₀`: an open
`V ∋ f x₀` with `g (f x₀) = x₀`, `f ∘ g = id` on `V`, `g ∘ f = id` near `x₀`, and
`g` smooth on `V`. -/
theorem exists_twoSided_localInverse (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {x₀ : X} (hxcrit : x₀ ∉ criticalSet f) :
    ∃ (g : Y → X) (V : Set Y), IsOpen V ∧ f x₀ ∈ V ∧ g (f x₀) = x₀ ∧
      (∀ y ∈ V, f (g y) = y) ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V ∧
      ((g ∘ f) =ᶠ[𝓝 x₀] id) := by
  obtain ⟨g, V, hVopen, hfxV, hgfx, hsec, hgsmooth⟩ :=
    exists_holo_localInverse_of_notMem_criticalSet f hf hnonconst hxcrit
  obtain ⟨U, hUopen, hxU, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst hxcrit
  refine ⟨g, V, hVopen, hfxV, hgfx, hsec, hgsmooth, ?_⟩
  -- `g` is continuous at `f x₀` (open domain `V`), with `g (f x₀) = x₀ ∈ U`.
  have hg_contAt : ContinuousAt g (f x₀) :=
    (hgsmooth.continuousOn.continuousAt (hVopen.mem_nhds hfxV))
  have hgU : ∀ᶠ y in 𝓝 (f x₀), g y ∈ U :=
    hg_contAt.eventually_mem (by rw [hgfx]; exact hUopen.mem_nhds hxU)
  -- Pull the two `Y`-side neighborhoods of `f x₀` back along `f` (continuous at `x₀`).
  have hf_contAt : ContinuousAt f x₀ := hf.continuous.continuousAt
  have hxV : ∀ᶠ x in 𝓝 x₀, f x ∈ V := hf_contAt.eventually_mem (hVopen.mem_nhds hfxV)
  have hxgU : ∀ᶠ x in 𝓝 x₀, g (f x) ∈ U := hf_contAt.eventually (p := fun y => g y ∈ U) hgU
  have hxinU : ∀ᶠ x in 𝓝 x₀, x ∈ U := hUopen.eventually_mem hxU
  filter_upwards [hxV, hxgU, hxinU] with x hxVmem hxgUmem hxinUmem
  show g (f x) = x
  -- `f (g (f x)) = f x` (right inverse on `V`); inject on `U` (`g (f x), x ∈ U`).
  exact hinj hxgUmem hxinUmem (hsec (f x) hxVmem)

/-! ### Value identity: the fibre summand is a section pullback -/

/-- **Key value identity.** At `y₀ = f x₀`, the trace summand `traceSummand f α x₀`
equals `sheetPullback α g y₀` for any two-sided local section `g` through `x₀`.
Combines `g (f x₀) = x₀` with `mfderiv g (f x₀) = (mfderiv f x₀).inverse`
(`mfderiv_section_eq_inverse`), so the off-branch fibre sum is, sheet by sheet, a
holomorphic pullback. -/
theorem traceSummand_eq_sheetPullback {f : X → Y} {g : Y → X} {x₀ : X}
    (α : HolomorphicOneForms X) (hgfx : g (f x₀) = x₀)
    (hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x₀)
    (hg_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (f x₀))
    (hfs : (f ∘ g) =ᶠ[𝓝 (f x₀)] id) (hsf : (g ∘ f) =ᶠ[𝓝 x₀] id) :
    traceSummand f α x₀ = sheetPullback α g (f x₀) := by
  have hinv : mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x₀) = (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).inverse :=
    mfderiv_section_eq_inverse hgfx rfl hf_diff hg_diff hfs hsf
  show (α.toFun x₀).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).inverse) =
    (α.toFun (g (f x₀))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x₀))
  rw [hinv, hgfx]

/-- `traceSummand` is additive in the form. -/
theorem traceSummand_add (f : X → Y) (α β : HolomorphicOneForms X) (x : X) :
    traceSummand f (α + β) x = traceSummand f α x + traceSummand f β x := by
  show ((α + β).toFun x).comp _ = (α.toFun x).comp _ + (β.toFun x).comp _
  rw [show (α + β).toFun x = α.toFun x + β.toFun x from rfl, ContinuousLinearMap.add_comp]

/-- `traceSummand` is ℂ-homogeneous in the form. -/
theorem traceSummand_smul (f : X → Y) (c : ℂ) (α : HolomorphicOneForms X) (x : X) :
    traceSummand f (c • α) x = c • traceSummand f α x := by
  show ((c • α).toFun x).comp _ = c • (α.toFun x).comp _
  rw [show (c • α).toFun x = c • α.toFun x from rfl, ContinuousLinearMap.smul_comp]

/-! ## The off-branch fibre-sum, holomorphic

We package the trace value at `y` as a `finsum` over the fibre `f⁻¹{y}` (total:
`= 0` when the fibre is infinite, which never happens off the branch locus). Off
branch, the cover splits into finitely many holomorphic sheets over a common base
neighborhood `V`, and on `V` the fibre sum is `∑ᵢ sheetPullback α (gᵢ)`, a finite
sum of holomorphic one-forms — hence holomorphic. -/

/-- Retyping of the trace summand to the cotangent fibre at `y`, given `f x = y`.
Since `TangentSpace 𝓘(ℂ) (f x) = TangentSpace 𝓘(ℂ) y` definitionally collapses to
`ℂ`, this is a transport along `f x = y`. -/
noncomputable def traceSummandAt (f : X → Y) (α : HolomorphicOneForms X) (_y : Y) (x : X) :
    ℂ →L[ℂ] ℂ :=
  traceSummand f α x

/-- **Trace value (fibre sum).** The covector at `y` obtained by summing
`traceSummand f α x` over the fibre `f⁻¹{y}`. Total via `finsum` (`= 0` when the
fibre is infinite); off the branch locus the fibre is finite and this is the
genuine finite sum. Typed in the model fibre `ℂ →L[ℂ] ℂ`, which is definitionally
the cotangent fibre `T_y Y →L[ℂ] ℂ`. -/
noncomputable def traceFun (f : X → Y) (α : HolomorphicOneForms X) (y : Y) :
    ℂ →L[ℂ] ℂ :=
  ∑ᶠ (x : X) (_ : x ∈ f ⁻¹' {y}), traceSummandAt f α y x

/-- **Local sheet system** of a branched cover `f` over a base neighborhood `V` of
`y₀` (off the branch locus). Bundles the finitely many holomorphic sections whose
images sweep out the entire fibre at each point of `V`. This is precisely the
trivialization data of the covering `isCoveringMapOn_compl_branchLocus`, repackaged
as sections (Forster §4.22). -/
structure LocalSheetSystem (f : X → Y) (y₀ : Y) where
  /-- Number of sheets (classically `= deg f`). -/
  n : ℕ
  /-- The base neighborhood over which the cover trivializes. -/
  V : Set Y
  isOpen_V : IsOpen V
  mem_V : y₀ ∈ V
  /-- The `n` holomorphic sheet sections. -/
  sheet : Fin n → Y → X
  /-- Each sheet is `C^ω` on `V`. -/
  sheet_smooth : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (sheet i) V
  /-- Each sheet is a section of `f` on `V`: `f ∘ sheet i = id` on `V`. -/
  sheet_section : ∀ i, ∀ y ∈ V, f (sheet i y) = y
  /-- Each sheet is a *local two-sided* inverse: `sheet i ∘ f = id` near `sheet i y`.
  (True of genuine covering sections, which are local homeomorphisms.) -/
  sheet_leftInv : ∀ i, ∀ y ∈ V, (sheet i ∘ f) =ᶠ[𝓝 (sheet i y)] id
  /-- The sheets are everywhere distinct over `V` (different sheets, different points). -/
  sheet_inj : ∀ y ∈ V, Function.Injective (fun i => sheet i y)
  /-- The sheets sweep out the **entire** fibre over each `y ∈ V`. -/
  fibre_eq : ∀ y ∈ V, f ⁻¹' {y} = Set.range (fun i => sheet i y)

namespace LocalSheetSystem

variable {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)

/-- Each sheet is `MDifferentiableAt` at every point of `V`. -/
theorem sheet_mdifferentiableAt (i : Fin S.n) {y : Y} (hy : y ∈ S.V) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (S.sheet i) y :=
  ((S.sheet_smooth i).contMDiffAt (S.isOpen_V.mem_nhds hy)).mdifferentiableAt (by decide)

/-- **Per-sheet value identity.** On `V`, the retyped fibre summand at the sheet
point `sheet i y` equals `sheetPullback α (sheet i) y`. -/
theorem traceSummandAt_sheet_eq {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (α : HolomorphicOneForms X) (i : Fin S.n) {y : Y} (hy : y ∈ S.V) :
    traceSummandAt f α y (S.sheet i y) = sheetPullback α (S.sheet i) y := by
  have hfsy : f (S.sheet i y) = y := S.sheet_section i y hy
  have hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (S.sheet i y) :=
    hf.mdifferentiableAt (by decide)
  have hg_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (S.sheet i) (f (S.sheet i y)) := by
    rw [hfsy]; exact S.sheet_mdifferentiableAt i hy
  have hfs : (f ∘ S.sheet i) =ᶠ[𝓝 (f (S.sheet i y))] id := by
    rw [hfsy]
    filter_upwards [S.isOpen_V.mem_nhds hy] with y' hy'
    show f (S.sheet i y') = y'; exact S.sheet_section i y' hy'
  have hsf : (S.sheet i ∘ f) =ᶠ[𝓝 (S.sheet i y)] id := S.sheet_leftInv i y hy
  have hgfx : S.sheet i (f (S.sheet i y)) = S.sheet i y := by rw [hfsy]
  have hval := traceSummand_eq_sheetPullback (f := f) (g := S.sheet i)
    (x₀ := S.sheet i y) α hgfx hf_diff hg_diff hfs hsf
  -- `traceSummandAt f α y (sheet i y)` is just `traceSummand f α (sheet i y)` (no
  -- transport now that summands live in the model fibre `ℂ →L ℂ`).
  rw [traceSummandAt, hval, hfsy]

/-- **Local representation of the trace (off-branch core).** Over the base
neighborhood `V`, the fibre-sum trace is the finite sum of the per-sheet pullbacks:
`traceFun f α y = ∑ᵢ sheetPullback α (sheet i) y`. The fibre `f⁻¹{y}` is the range
of the injective sheet map (`fibre_eq` + `sheet_inj`), so the `finsum` over the
fibre collapses to the finite sum over the `n` sheets (`finsum_mem_range`), each
term identified by `traceSummandAt_sheet_eq`. -/
theorem traceFun_eq_sum_sheetPullback {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (α : HolomorphicOneForms X) {y : Y} (hy : y ∈ S.V) :
    traceFun f α y = ∑ i, sheetPullback α (S.sheet i) y := by
  rw [traceFun, S.fibre_eq y hy,
    finsum_mem_range (S.sheet_inj y hy), finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => S.traceSummandAt_sheet_eq hf α i hy

/-- **Off-branch holomorphicity.** Given a local sheet system at `y₀`,
the trace section `y ↦ traceFun f α y` is `ContMDiffAt` (analytic) at `y₀` — i.e.
the fibre-sum trace is a holomorphic one-form near `y₀`. Reduces, via the local
representation `traceFun = ∑ᵢ sheetPullback (sheet i)` on `V`, to the per-sheet
smoothness `contMDiffAt_sheetPullback` summed over the (finitely many) sheets
(`ContMDiffAt.sum_section`). -/
theorem contMDiffAt_traceFun {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (α : HolomorphicOneForms X) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (traceFun f α y)) y₀ := by
  -- On `V` (a neighborhood of `y₀`), `traceFun = ∑ᵢ sheetPullback (sheet i)`.
  have hrep : (fun y : Y => Bundle.TotalSpace.mk'
      (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
      (traceFun f α y)) =ᶠ[𝓝 y₀]
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (∑ i, sheetPullback α (S.sheet i) y)) := by
    filter_upwards [S.isOpen_V.mem_nhds S.mem_V] with y hy
    rw [S.traceFun_eq_sum_sheetPullback hf α hy]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hrep
  -- Finite sum of per-sheet pullback sections, each `ContMDiffAt` at `y₀ ∈ V`.
  refine ContMDiffAt.sum_section (fun i _ => ?_)
  exact contMDiffAt_sheetPullback α
    ((S.sheet_smooth i).contMDiffAt (S.isOpen_V.mem_nhds S.mem_V))

end LocalSheetSystem

/-! ### Linearity of the fibre-sum trace (off the branch locus)

The fibre sum is ℂ-linear in the form. Over a finite fibre this is termwise
linearity of `traceSummand` plus additivity/homogeneity of `finsum` over a finite
set. (At a branch point the naive `finsum` is `0`; the genuine trace there is the
removable-singularity extension, handled in the assembly below.) -/

/-- Additivity of the fibre-sum trace off the branch locus. -/
theorem traceFun_add_of_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α β : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    traceFun f (α + β) y = traceFun f α y + traceFun f β y := by
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hy
  unfold traceFun
  simp only [traceSummandAt, traceSummand_add f α β]
  rw [finsum_mem_add_distrib hfin]

/-- ℂ-homogeneity of the fibre-sum trace off the branch locus. -/
theorem traceFun_smul_of_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (c : ℂ) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    traceFun f (c • α) y = c • traceFun f α y := by
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hy
  unfold traceFun
  simp only [traceSummandAt, traceSummand_smul f c α]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.smul_sum]

/-! ### Existence of the local sheet system (covering unpacking) -/

/-- **[PROVEN]** Off the branch locus a local sheet system exists (Forster §4.22).

Construction (no covering trivialization needed — assembled directly from the proven
local pieces): the fibre `f⁻¹{y₀}` is finite (`fiber_finite_off_branchLocus`),
enumerated as `pt : Fin n → X` via `Fintype.equivFin`. The `pt i` are pairwise
distinct points off `criticalSet`, separated by pairwise-disjoint opens `Sep i`
(`X` is T2, `Set.Finite.t2_separation`). At each `pt i`, `exists_twoSided_localInverse`
gives a `C^ω` two-sided section `g i` on an open `Vsec i ∋ y₀`
(supplying `sheet_smooth`, `sheet_section`, and the `sheet_leftInv` content), and
`isLocalHomeoOffCritical` gives an open injective neighborhood, shrunk into `Sep i`
to make the sheets disjoint. Properness (`properNbhd` of `isProperMap_of_contMDiff`)
shrinks the fibre's open cover `⋃ Uinj` to a base `Ubase ∋ y₀` with `f⁻¹ Ubase ⊆ ⋃ Uinj`.
Over `V := Ubase ∩ ⋂ i (Vsec i ∩ g i⁻¹ (Uinj i))` every preimage of `y ∈ V` lands in
some `Uinj j`, where `g j y` is its unique preimage — giving `fibre_eq`; the disjoint
`Sep i` give `sheet_inj`. With this, `contMDiffAt_traceFun_of_notMem_branchLocus`
(off-branch holomorphicity of the trace) is **unconditional**. -/
theorem exists_localSheetSystem (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    Nonempty (LocalSheetSystem f y₀) := by
  classical
  -- The fibre over `y₀` is finite; enumerate it as `Fin n`.
  have hfin : (f ⁻¹' {y₀}).Finite := fiber_finite_off_branchLocus f hf hnonconst hy₀
  let _ffib : Fintype (f ⁻¹' {y₀}) := hfin.fintype
  set n : ℕ := Fintype.card (f ⁻¹' {y₀}) with hn_def
  set e : (f ⁻¹' {y₀}) ≃ Fin n := Fintype.equivFin _ with he_def
  -- The `i`-th fibre point, as a term of `X`.
  set pt : Fin n → X := fun i => (e.symm i : X) with hpt_def
  have hpt_fib : ∀ i, f (pt i) = y₀ := fun i => (e.symm i).2
  have hpt_crit : ∀ i, pt i ∉ criticalSet f := fun i hmem =>
    hy₀ ⟨pt i, hmem, hpt_fib i⟩
  have hpt_inj : Function.Injective pt := fun i j hij => by
    have : e.symm i = e.symm j := Subtype.ext hij
    exact e.symm.injective this
  -- Separate the finitely many distinct fibre points by pairwise-disjoint open
  -- neighborhoods (`X` is T2). `Sep i ∋ pt i`, open, and disjoint for distinct
  -- `pt i`. This makes the sheets provably distinct over the base (sheet `i`
  -- lands in `Sep i`, sheet `j` in the disjoint `Sep j`).
  obtain ⟨Sep₀, hSep₀_mem, hSep₀_disj⟩ :
      ∃ U : X → Set X, (∀ x, x ∈ U x ∧ IsOpen (U x)) ∧ (Set.range pt).PairwiseDisjoint U :=
    (Set.finite_range pt).t2_separation
  set Sep : Fin n → Set X := fun i => Sep₀ (pt i) with hSep_def
  have hSep_mem : ∀ i, pt i ∈ Sep i := fun i => (hSep₀_mem (pt i)).1
  have hSep_open : ∀ i, IsOpen (Sep i) := fun i => (hSep₀_mem (pt i)).2
  have hSep_disj : ∀ i j, i ≠ j → Disjoint (Sep i) (Sep j) := fun i j hij =>
    hSep₀_disj (Set.mem_range_self i) (Set.mem_range_self j)
      (fun h => hij (hpt_inj h))
  -- For each fibre point, a `C^ω` two-sided local section `g i` on an open
  -- `Vsec i ∋ y₀` (with `g i y₀ = pt i`, `f ∘ g i = id` on `Vsec i`,
  -- `g i ∘ f = id` near `pt i`) together with an open injective neighborhood
  -- `Uinj i ∋ pt i` of `pt i` in `X` (`isLocalHomeoOffCritical`), shrunk into
  -- the separating window `Sep i` so the sheets are pairwise disjoint.
  have hpkg : ∀ i : Fin n, ∃ (g : Y → X) (Vsec : Set Y) (Uinj : Set X),
      IsOpen Vsec ∧ y₀ ∈ Vsec ∧ g y₀ = pt i ∧
        (∀ y ∈ Vsec, f (g y) = y) ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g Vsec ∧
        ((g ∘ f) =ᶠ[𝓝 (pt i)] id) ∧
        IsOpen Uinj ∧ pt i ∈ Uinj ∧ Set.InjOn f Uinj ∧ Uinj ⊆ Sep i := by
    intro i
    obtain ⟨g, Vsec, hVo, hfxV, hgfx, hsec, hgsm, hgf⟩ :=
      exists_twoSided_localInverse f hf hnonconst (hpt_crit i)
    obtain ⟨Uinj, hUo, hxU, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst (hpt_crit i)
    -- `exists_twoSided_localInverse` lives over `f (pt i) = y₀`; rewrite to `y₀`.
    rw [hpt_fib i] at hfxV hgfx
    -- Intersect the injective neighborhood with the separating window `Sep i`.
    refine ⟨g, Vsec, Uinj ∩ Sep i, hVo, hfxV, hgfx, hsec, hgsm, hgf,
      hUo.inter (hSep_open i), ⟨hxU, hSep_mem i⟩, hinj.mono Set.inter_subset_left,
      Set.inter_subset_right⟩
  choose g Vsec Uinj hVo hy₀V hgfx hsec hgsm hgf hUo hxU hinj hUsep using hpkg
  -- The fibre `f⁻¹{y₀} = pt '' univ` is contained in the open `⋃ⱼ Uinj j`.
  set Ubig : Set X := ⋃ j, Uinj j with hUbig_def
  have hUbig_open : IsOpen Ubig := isOpen_iUnion hUo
  have hfib_sub : f ⁻¹' {y₀} ⊆ Ubig := by
    intro x hx
    have hxfib : x ∈ f ⁻¹' {y₀} := hx
    -- `x` is the `e`-image of itself; it equals `pt (e ⟨x, _⟩)`.
    set j : Fin n := e ⟨x, hxfib⟩ with hj_def
    have hpt_eq : pt j = x := by simp only [hpt_def, hj_def, Equiv.symm_apply_apply]
    exact Set.mem_iUnion.mpr ⟨j, hpt_eq ▸ hxU j⟩
  -- Properness: shrink to an open base `Ubase ∋ y₀` with `f⁻¹ Ubase ⊆ Ubig`.
  obtain ⟨Ubase, hUbase_open, hy₀Ubase, hUbase_sub⟩ :=
    properNbhd (isProperMap_of_contMDiff f hf) y₀ hUbig_open hfib_sub
  -- Each `Wsheet i := Vsec i ∩ (g i)⁻¹ (Uinj i)` is open (continuity of the
  -- section on its open domain) and contains `y₀` (`g i y₀ = pt i ∈ Uinj i`).
  set Wsheet : Fin n → Set Y := fun i => Vsec i ∩ g i ⁻¹' Uinj i with hWsheet_def
  have hWsheet_open : ∀ i, IsOpen (Wsheet i) := fun i =>
    (hgsm i).continuousOn.isOpen_inter_preimage (hVo i) (hUo i)
  have hy₀Wsheet : ∀ i, y₀ ∈ Wsheet i := fun i =>
    ⟨hy₀V i, by rw [Set.mem_preimage, hgfx i]; exact hxU i⟩
  -- The base neighborhood: properness ∩ all sheet windows.
  set V : Set Y := Ubase ∩ ⋂ i, Wsheet i with hV_def
  have hV_open : IsOpen V :=
    hUbase_open.inter (isOpen_iInter_of_finite (fun i => hWsheet_open i))
  have hy₀V_mem : y₀ ∈ V := ⟨hy₀Ubase, Set.mem_iInter.mpr hy₀Wsheet⟩
  have hV_sub_Ubase : ∀ {y}, y ∈ V → y ∈ Ubase := fun {_} hy => hy.1
  have hV_sub_Wsheet : ∀ i {y}, y ∈ V → y ∈ Wsheet i :=
    fun i {_} hy => (Set.mem_iInter.mp hy.2) i
  have hV_sub_Vsec : ∀ i {y}, y ∈ V → y ∈ Vsec i := fun i {_} hy => (hV_sub_Wsheet i hy).1
  have hVsub_Vsec : ∀ i, V ⊆ Vsec i := fun i _ hy => (hV_sub_Wsheet i hy).1
  -- `f (g i y) = y` for `y ∈ V` (section on `V ⊆ Vsec i`).
  have hsec_V : ∀ i, ∀ y ∈ V, f (g i y) = y := fun i y hy =>
    hsec i y (hV_sub_Vsec i hy)
  -- `g i y ∈ Uinj i` for `y ∈ V` (from the `g i ⁻¹ Uinj i` window).
  have hgmem_V : ∀ i, ∀ y ∈ V, g i y ∈ Uinj i := fun i y hy =>
    (hV_sub_Wsheet i hy).2
  refine ⟨{
    n := n
    V := V
    isOpen_V := hV_open
    mem_V := hy₀V_mem
    sheet := g
    sheet_smooth := fun i => (hgsm i).mono (hVsub_Vsec i)
    sheet_section := hsec_V
    sheet_leftInv := ?_
    sheet_inj := ?_
    fibre_eq := ?_ }⟩
  · -- `sheet_leftInv`: `g i ∘ f = id` near `g i y` for `y ∈ V`.
    -- The two-sided inverse gives this near `pt i = g i y₀`. For general `y ∈ V`,
    -- `g i y ∈ Uinj i` where `f` is injective, and `g i ∘ f = id` near it follows
    -- from the section identity + injectivity, via the same argument as
    -- `exists_twoSided_localInverse`.
    intro i y hy
    -- `g i` is continuous at `y` (open domain `Vsec i ⊇ V ∋ y`).
    have hgi_contAt : ContinuousAt (g i) y :=
      (hgsm i).continuousOn.continuousAt ((hVo i).mem_nhds (hV_sub_Vsec i hy))
    -- Near `g i y`, points land in `Uinj i`.
    have hpre_U : ∀ᶠ x in 𝓝 (g i y), x ∈ Uinj i :=
      (hUo i).eventually_mem (hgmem_V i y hy)
    -- `f` is continuous at `g i y`.
    have hf_contAt : ContinuousAt f (g i y) := hf.continuous.continuousAt
    -- Near `g i y`: `f x ∈ V` (since `f (g i y) = y ∈ V`, `V` open).
    have hfx_V : ∀ᶠ x in 𝓝 (g i y), f x ∈ V :=
      hf_contAt.eventually_mem (by rw [hsec_V i y hy]; exact hV_open.mem_nhds hy)
    -- Near `g i y`: `g i (f x) ∈ Uinj i`.
    have hgfx_U : ∀ᶠ x in 𝓝 (g i y), g i (f x) ∈ Uinj i := by
      filter_upwards [hfx_V] with x hx
      exact hgmem_V i (f x) hx
    filter_upwards [hpre_U, hfx_V, hgfx_U] with x hxU' hxV' hgfxU'
    show g i (f x) = x
    -- `f (g i (f x)) = f x` (section at `f x ∈ V`); inject on `Uinj i`.
    exact hinj i hgfxU' hxU' (hsec_V i (f x) hxV')
  · -- `sheet_inj`: the sheets are distinct over `V`. For `y ∈ V`,
    -- `g i y ∈ Uinj i ⊆ Sep i` and `g j y ∈ Uinj j ⊆ Sep j`, and the `Sep`'s
    -- are pairwise disjoint for distinct indices — so equal sheet values force
    -- equal indices.
    intro y hy i j hij
    by_contra hne
    have hxSi : g i y ∈ Sep i := hUsep i (hgmem_V i y hy)
    have hxSj : g j y ∈ Sep j := hUsep j (hgmem_V j y hy)
    have hgij : g i y = g j y := hij
    -- `g i y = g j y` lies in `Sep i ∩ Sep j`, which is empty for `i ≠ j`.
    exact (hSep_disj i j hne).le_bot ⟨hxSi, hgij ▸ hxSj⟩
  · -- `fibre_eq`: the sheets exhaust the fibre over each `y ∈ V`.
    intro y hy
    apply Set.eq_of_subset_of_subset
    · -- `⊆`: any `x ∈ f⁻¹{y}` lies in some `Uinj j` (properness), and there
      -- `g j y` is the unique preimage of `y`, so `x = g j y`.
      intro x hx
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      -- `x ∈ f⁻¹ Ubase ⊆ Ubig = ⋃ Uinj`.
      have hxUbase : x ∈ f ⁻¹' Ubase := by
        rw [Set.mem_preimage, hx]; exact hV_sub_Ubase hy
      have hxUbig : x ∈ Ubig := hUbase_sub hxUbase
      obtain ⟨j, hxUj⟩ := Set.mem_iUnion.mp hxUbig
      -- `g j y ∈ Uinj j` and `f (g j y) = y = f x`; inject on `Uinj j`.
      have hgjy_U : g j y ∈ Uinj j := hgmem_V j y hy
      have hfgjy : f (g j y) = y := hsec_V j y hy
      have : x = g j y := hinj j hxUj hgjy_U (by rw [hx, hfgjy])
      exact Set.mem_range.mpr ⟨j, this.symm⟩
    · -- `⊇`: each `g i y` is in the fibre (`f (g i y) = y`).
      rintro x ⟨i, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact hsec_V i y hy

/-- **Off-branch holomorphicity of the trace, top-level form.** For `y₀` off the
branch locus, the fibre-sum trace `y ↦ traceFun f α y` is `ContMDiffAt` (a
holomorphic one-form) at `y₀`. Combines `exists_localSheetSystem` (the isolated
covering step) with the fully-proven `LocalSheetSystem.contMDiffAt_traceFun`. -/
theorem contMDiffAt_traceFun_of_notMem_branchLocus (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (α : HolomorphicOneForms X) {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (traceFun f α y)) y₀ := by
  obtain ⟨S⟩ := exists_localSheetSystem f hf hnonconst hy₀
  exact S.contMDiffAt_traceFun hf α

/-! ### The trace as a bundle section, and its canonical branch extension

We package the covector-valued trace as a map into the cotangent-bundle total space
(`traceTotalSpaceMk`) so we can speak of its `ContMDiff`ness directly, and we define the
*canonical extension* `traceFunExt` that overwrites the (wrong) `finsum = 0` value at each
branch point with the geometrically-correct **fixed-frame branch value** `traceBranchValue`
(the removable-singularity limit of the *local coefficient*, read in the fixed `y₀`-chart —
NOT the raw-operator limit, which is discontinuous for a non-trivial tangent bundle).

Off the branch locus `traceFunExt = traceFun`; on a *punctured* neighborhood of a
branch point they also agree (the branch locus is finite, so a punctured nhd avoids
it). These two agreements are all the reduction lemma below needs.

The **local coefficient** `traceLocalCoeff` and the **center-frame identities** are placed
first, since both `traceBranchValue` and `traceFunExt` are defined in terms of them. -/

/-- The trace, packaged as a map into the **total space** of the cotangent bundle of
`Y` (the shape consumed by `ContMDiffAt`/`ContMDiffSection`). `coeff` is the covector
to place in the fibre at `y` — either the raw fibre sum `traceFun f α y` or its branch
extension `traceFunExt f α y`. -/
noncomputable abbrev traceTotalSpaceMk (coeff : Y → (ℂ →L[ℂ] ℂ)) (y : Y) :
    Bundle.TotalSpace (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) :=
  Bundle.TotalSpace.mk'
    (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
    (coeff y)

/-- **Local coefficient of the trace.** The coordinate of the (extended) trace section
`coeff` read in the *fixed* hom-bundle trivialization at `y₀`, evaluated on the model basis
vector `1 : ℂ`. Concretely `inCoordinates … y₀ y y₀ y (coeff y) (1 : ℂ) : ℂ`. This is the
continuous/holomorphic object (unlike the raw `(coeff y) 1`); the trace section is
`ContMDiffAt`/`ContinuousAt` at `y₀` **iff** this scalar is, by `contMDiffAt_hom_bundle`. We
define it for an arbitrary coefficient so it can be applied to both `traceFun` and
`traceFunExt`. -/
noncomputable def traceLocalCoeff (coeff : Y → (ℂ →L[ℂ] ℂ)) (y₀ y : Y) : ℂ :=
  ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
    y₀ y y₀ y (coeff y) (1 : ℂ)

/-- A `ℂ →L[ℂ] ℂ` operator is its value-at-`1` times the identity: `φ = (φ 1) • id`. The
elementary fact underlying the reconstruction of an operator-valued chart coordinate from
its scalar coordinate. -/
theorem clm_eq_apply_one_smul_id (φ : ℂ →L[ℂ] ℂ) :
    φ = (φ (1 : ℂ)) • ContinuousLinearMap.id ℂ ℂ := by
  apply ContinuousLinearMap.ext_ring
  simp

/-- **Tangent trivialization is the identity at its own center.** The fixed `y₀`-tangent
trivialization's fiber coordinate map `continuousLinearMapAt … y₀` is `id` (the chart-transition
derivative `D(chart ∘ chart.symm)` at the center is `D id = id`). This is the precise sense in
which the *fixed* trivialization removes the chart-frame discontinuity at `y₀`. -/
theorem tangent_continuousLinearMapAt_center (y₀ : Y) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) y₀).continuousLinearMapAt ℂ y₀
      = ContinuousLinearMap.id ℂ ℂ := by
  apply ContinuousLinearMap.ext_ring
  change (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) y₀).continuousLinearMapAt ℂ y₀ _ = _
  rw [(trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) y₀).continuousLinearMapAt_apply_of_mem ℂ
    (mem_baseSet_trivializationAt ℂ _ y₀), TangentBundle.trivializationAt_apply]
  -- The fiber map at the center is `fderivWithin (e ∘ e.symm) (range I) (e y₀) 1`,
  -- with `e := extChartAt 𝓘(ℂ) y₀`; and `e ∘ e.symm = id` on `e.target ∈ 𝓝 (e y₀)`.
  show (fderivWithin ℂ (extChartAt 𝓘(ℂ) y₀ ∘ (extChartAt 𝓘(ℂ) y₀).symm)
      (Set.range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ)) (extChartAt 𝓘(ℂ) y₀ y₀)) 1 = (1 : ℂ)
  rw [ModelWithCorners.range_eq_univ]
  have hev : ((extChartAt 𝓘(ℂ) y₀) ∘ (extChartAt 𝓘(ℂ) y₀).symm : ℂ → ℂ)
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ) y₀ y₀)] id := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℂ)) y₀] with z hz
    simp only [Function.comp_apply, id_eq]; exact (extChartAt 𝓘(ℂ) y₀).right_inv hz
  rw [fderivWithin_univ, hev.fderiv_eq, fderiv_id, ContinuousLinearMap.id_apply]

/-- The inverse tangent trivialization `symmL … y₀` is also `id` at the center (inverse of
`tangent_continuousLinearMapAt_center`). -/
theorem tangent_symmL_center (y₀ : Y) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) y₀).symmL ℂ y₀
      = ContinuousLinearMap.id ℂ ℂ := by
  have h := (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) y₀).symmL_continuousLinearMapAt
    (R := ℂ) (mem_baseSet_trivializationAt ℂ _ y₀)
  rw [tangent_continuousLinearMapAt_center] at h
  -- `h : ∀ y, symmL(…) (id y) = y`, i.e. `symmL(…) v = v`; conclude the operator equals `id`.
  refine ContinuousLinearMap.ext (fun v => ?_)
  simpa using h v

/-- **The fixed-frame coordinate change is the identity AT the center `y₀`.** For the cotangent
hom-bundle, `inCoordinates … y₀ y₀ y₀ y₀ φ = φ`: at the center both the source (tangent) and
target (trivial) coordinate changes are `id`. Consequently the *local coefficient* read at the
center recovers the raw value, `traceLocalCoeff coeff y₀ y₀ = (coeff y₀) 1`
(`traceLocalCoeff_center`). This is what makes the branch value `L • id` self-consistent: its
local coefficient at `y₀` is exactly `L`. -/
theorem inCoordinates_center_self (φ : ℂ →L[ℂ] ℂ) (y₀ : Y) :
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
      y₀ y₀ y₀ y₀ φ = φ := by
  simp only [ContinuousLinearMap.inCoordinates, Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    tangent_symmL_center]
  exact ContinuousLinearMap.comp_id φ

/-- **Local coefficient at the center recovers the raw value-at-`1`.** Immediate from
`inCoordinates_center_self`. -/
theorem traceLocalCoeff_center (coeff : Y → (ℂ →L[ℂ] ℂ)) (y₀ : Y) :
    traceLocalCoeff coeff y₀ y₀ = (coeff y₀) (1 : ℂ) := by
  rw [traceLocalCoeff, inCoordinates_center_self]

/-- **`inCoordinates` of the cotangent hom-bundle, value-at-`1`, is additive in the operator.**
The target trivial-bundle coordinate `continuousLinearMapAt` is `id`, so `inCoordinates … φ 1`
reduces to `φ (symmL … 1)`, additive in `φ`. -/
theorem inCoordinates_apply_one_add (φ ψ : ℂ →L[ℂ] ℂ) (y₀ y : Y) :
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
        y₀ y y₀ y (φ + ψ) (1 : ℂ)
      = ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
          y₀ y y₀ y φ (1 : ℂ)
        + ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
          y₀ y y₀ y ψ (1 : ℂ) := by
  simp only [ContinuousLinearMap.inCoordinates, Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.add_apply φ ψ _

/-- **`inCoordinates` value-at-`1` is ℂ-homogeneous in the operator.** Companion to
`inCoordinates_apply_one_add`. -/
theorem inCoordinates_apply_one_smul (a : ℂ) (φ : ℂ →L[ℂ] ℂ) (y₀ y : Y) :
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
        y₀ y y₀ y (a • φ) (1 : ℂ)
      = a • ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
          y₀ y y₀ y φ (1 : ℂ) := by
  simp only [ContinuousLinearMap.inCoordinates, Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.smul_apply a φ _

/-- **The local coefficient is additive in the operator value.** The local coefficient of a
pointwise sum of coefficient functions splits (from `inCoordinates_apply_one_add`). Used for
ℂ-linearity of the trace at branch points, read in the fixed frame. -/
theorem traceLocalCoeff_add (g h : Y → (ℂ →L[ℂ] ℂ)) (y₀ y : Y) :
    traceLocalCoeff (fun y => g y + h y) y₀ y
      = traceLocalCoeff g y₀ y + traceLocalCoeff h y₀ y :=
  inCoordinates_apply_one_add (g y) (h y) y₀ y

/-- **The local coefficient is ℂ-homogeneous in the operator value.** Companion to
`traceLocalCoeff_add`. -/
theorem traceLocalCoeff_smul (a : ℂ) (g : Y → (ℂ →L[ℂ] ℂ)) (y₀ y : Y) :
    traceLocalCoeff (fun y => a • g y) y₀ y = a • traceLocalCoeff g y₀ y :=
  inCoordinates_apply_one_smul a (g y) y₀ y

/-- **Branch value of the trace, in the fixed `y₀`-frame.** At a branch point `y₀` the operator
`traceFun f α y` (read in the *varying* chart at `y`) is genuinely discontinuous as `y → y₀` for a
non-trivial tangent bundle (kirovGenus ≥ 2; the `CotangentCoeff.lean` obstruction), so the naive
operator `limUnder` is junk. The geometrically-correct value is built from the **local
coefficient** read in the FIXED `y₀`-chart: take its removable-singularity limit `L` (a scalar in
`ℂ`, the chart-pullback `limUnder` of `z ↦ traceLocalCoeff (traceFun f α) y₀ (chart⁻¹ z)`) and
package it as the operator `L • id`. By `traceLocalCoeff_center`, this operator's own local
coefficient at `y₀` is exactly `L`, so the extension is self-consistent and its section is the
continuous bundle-extension. -/
noncomputable def traceBranchValue (f : X → Y) (α : HolomorphicOneForms X) (y₀ : Y) :
    ℂ →L[ℂ] ℂ :=
  (limUnder (𝓝[≠] ((chartAt ℂ y₀) y₀))
      (fun z => traceLocalCoeff (traceFun f α) y₀ ((chartAt ℂ y₀).symm z)))
    • ContinuousLinearMap.id ℂ ℂ

/-- **Canonical branch extension of the trace coefficient.** Equal to the fibre sum
`traceFun f α` off the branch locus, and to the **fixed-frame branch value** `traceBranchValue`
at each branch point (where the naive `finsum` is `0`). At a branch point the branch value is
read in the fixed `y₀`-trivialization (the local coefficient), NOT as the raw-operator limit — the
latter is discontinuous for a non-trivial tangent bundle. The membership test is decidable via
`Classical.dec`. -/
noncomputable def traceFunExt (f : X → Y) (α : HolomorphicOneForms X) (y : Y) :
    ℂ →L[ℂ] ℂ := by
  classical
  exact if y ∈ branchLocus f then traceBranchValue f α y else traceFun f α y

/-- Off the branch locus, the extension is the raw fibre sum. -/
theorem traceFunExt_of_notMem_branchLocus (f : X → Y) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    traceFunExt f α y = traceFun f α y := by
  classical
  rw [traceFunExt, if_neg hy]

/-- At a branch point, the extension is the fixed-frame branch value. -/
theorem traceFunExt_of_mem_branchLocus (f : X → Y) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∈ branchLocus f) :
    traceFunExt f α y = traceBranchValue f α y := by
  classical
  rw [traceFunExt, if_pos hy]

/-- **At a branch point the extension operator is `(local coefficient) • id`.** Since the branch
value is `L • id` and `traceLocalCoeff (L • id) y y = L` (`traceLocalCoeff_center`), the operator
`traceFunExt f α y` is recovered from its own (scalar, linear-in-`α`) local coefficient. This is
the bridge that turns the ℂ-linearity of the *scalar* local coefficient into ℂ-linearity of the
*operator* extension at branch points. -/
theorem traceFunExt_branchPoint_eq_smul_id (f : X → Y) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∈ branchLocus f) :
    traceFunExt f α y = (traceLocalCoeff (traceFunExt f α) y y) • ContinuousLinearMap.id ℂ ℂ := by
  rw [traceLocalCoeff_center, traceFunExt_of_mem_branchLocus f α hy, traceBranchValue]
  -- `(L • id) 1 = L`, so the RHS is `((L • id) 1) • id = L • id = traceBranchValue`.
  simp

/-- A punctured neighborhood of any point `y₀` **eventually avoids the branch locus**:
the branch locus is finite (hence `branchLocus f \ {y₀}` is closed), so its complement
is a neighborhood of `y₀`, and a point there which is also `≠ y₀` is off-branch. This is
the engine behind both the agreement lemma below and the linearity argument: on `𝓝[≠] y₀`
the trace is genuinely the off-branch fibre sum. -/
theorem eventually_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y₀ : Y) :
    ∀ᶠ y in 𝓝[≠] y₀, y ∉ branchLocus f := by
  have hBfin : (branchLocus f).Finite := finite_branchLocus_of_nonconstant f hf hnonconst
  have hclosed : IsClosed (branchLocus f \ {y₀}) := hBfin.diff.isClosed
  have hnhd : (branchLocus f \ {y₀})ᶜ ∈ 𝓝 y₀ :=
    hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnhd] with y hy_ne hy_notdiff
  rw [Set.mem_compl_iff, Set.mem_diff, not_and, not_not] at hy_notdiff
  exact fun hyB => hy_ne (hy_notdiff hyB)

/-- On the **punctured** neighborhood of any point `y₀`, the extension agrees with the
raw fibre sum: on `𝓝[≠] y₀` points are eventually off the branch locus
(`eventually_notMem_branchLocus`), where `traceFunExt = traceFun`. This is the bridge
turning a limit/continuity statement about `traceFun` into one about `traceFunExt`. -/
theorem traceFunExt_eventuallyEq_traceFun (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X) (y₀ : Y) :
    traceFunExt f α =ᶠ[𝓝[≠] y₀] traceFun f α := by
  filter_upwards [eventually_notMem_branchLocus f hf hnonconst y₀] with y hy_off
  exact traceFunExt_of_notMem_branchLocus f α hy_off

/-! ### Off-branch smoothness of the extended section

Off the branch locus the extension equals the raw fibre sum on a whole (open)
neighborhood, so off-branch `ContMDiffAt` of the *extended* section follows from the
unconditional off-branch `ContMDiffAt` of the raw fibre-sum section. -/

/-- The extended trace section is `ContMDiffAt` at every point **off** the branch
locus, unconditionally (no analytic hypothesis): the extension agrees with the raw
fibre sum on the open set `(branchLocus f)ᶜ`, where the fibre sum is holomorphic
(`contMDiffAt_traceFun_of_notMem_branchLocus`). -/
theorem contMDiffAt_traceSection_ext_of_notMem_branchLocus (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (α : HolomorphicOneForms X) {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (traceTotalSpaceMk (traceFunExt f α)) y₀ := by
  have hBclosed : IsClosed (branchLocus f) :=
    (finite_branchLocus_of_nonconstant f hf hnonconst).isClosed
  -- On the open complement of the branch locus, `traceFunExt = traceFun`.
  have heq : traceTotalSpaceMk (traceFunExt f α) =ᶠ[𝓝 y₀] traceTotalSpaceMk (traceFun f α) := by
    filter_upwards [hBclosed.isOpen_compl.mem_nhds hy₀] with y hy
    simp only [traceTotalSpaceMk, traceFunExt_of_notMem_branchLocus f α hy]
  exact (contMDiffAt_traceFun_of_notMem_branchLocus f hf hnonconst α hy₀).congr_of_eventuallyEq heq

/-- A connected complex 1-manifold has **no isolated points**: the punctured
neighborhood filter `𝓝[≠] y₀` is `NeBot`. (`Y` is `Infinite`
— `y_infinite_of_chartedSpace_complex` — hence `Nontrivial`; with `T1Space` +
`ConnectedSpace` this gives `PerfectSpace`, hence `NeBot (𝓝[≠] y₀)`.) This is what
makes limits along punctured neighborhoods unique, the engine of the linearity
argument below. -/
instance neBot_nhdsWithin_compl_self (y₀ : Y) : (𝓝[≠] y₀).NeBot := by
  haveI : Infinite Y := Jacobians.Discharge.ContMDiff.Degree.y_infinite_of_chartedSpace_complex
  infer_instance

/-! ### The reduction lemma (regluing + linearity), conditional on per-branch extension

The deliverable: a **fully-proven** reduction of `exists_traceForm` to one per-branch-point
analytic input. The input, `hext`, packages — for each form `α` and each branch point
`y₀` — the two facts that the (classically true) holomorphic extension supplies:

* `hsmooth`: the extended bundle section is `ContMDiffAt` at `y₀` (the *holomorphic*
  extension; from boundedness + Mathlib's removable singularity, then bundle regluing);
* `hcont`: the extension's **fixed-frame local coefficient**
  `y ↦ traceLocalCoeff (traceFunExt f α) y₀ y` is `ContinuousAt y₀` (the *continuous*
  extension, in the fixed `y₀`-trivialization — the shadow of `hsmooth`).

**Crucial soundness point.** `hcont` is phrased in the FIXED frame (the local coefficient),
NOT as continuity of the raw operator `traceFunExt f α : Y → (ℂ →L[ℂ] ℂ)` in the model fibre.
The latter is *provably false* for a non-trivial tangent bundle (kirovGenus ≥ 2): the operator is read
in the *varying* chart at `y`, whose transition factor is discontinuous (`CotangentCoeff.lean`).
The ℂ-linearity argument below is therefore re-derived in the fixed frame: at a branch point each
operator equals `(local coefficient) • id` (`traceFunExt_branchPoint_eq_smul_id`), and the scalar
local coefficients are additive/homogeneous by a unique-limit argument using `hcont`. This is
both true and sufficient.

Both `hsmooth` and `hcont` are consequences of the single analytic crux (local boundedness of
the trace near a branch point, §1 of the assembly docstring); we keep them as the hypothesis so
the regluing **and** the full ℂ-linearity of `T` are proven here, unconditionally. -/

/-- **Reduction lemma for the trace.** Given the per-branch-point extension data `hext`
(holomorphic-extension smoothness + fixed-frame local-coefficient continuity at each branch
point, for every form), the trace `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)` exists as a genuine
holomorphic-one-form linear map agreeing with the off-branch fibre sum `traceFun`.

Everything here is proven outright:
* **Section assembly**: `traceFunExt f α` is a global `ContMDiffSection` — off-branch from
  `contMDiffAt_traceSection_ext_of_notMem_branchLocus`, at branch points from `hext`.
* **Linearity**: at a branch point the extension operator is `(local coefficient) • id`, and the
  *scalar* local coefficient is the *unique* fixed-frame limit of the raw trace's local
  coefficient along the punctured neighborhood (`neBot_nhdsWithin_compl_self` +
  `tendsto_nhds_unique`); limits respect `+`/`•` and the local coefficient is linear in the
  operator (`inCoordinates_apply_one_add/smul`); off-branch the fibre sum is already
  additive/homogeneous (`traceFun_add_of_notMem_branchLocus`, `…_smul_…`). -/
theorem exists_traceForm_of_branchExtension (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (hext : ∀ (α : HolomorphicOneForms X) (y₀ : Y), y₀ ∈ branchLocus f →
      ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
          (traceTotalSpaceMk (traceFunExt f α)) y₀ ∧
        ContinuousAt (fun y => traceLocalCoeff (traceFunExt f α) y₀ y) y₀) :
    ∃ T : HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y,
      ∀ (α : HolomorphicOneForms X) (y : Y), y ∉ branchLocus f →
        (T α).toFun y = traceFun f α y := by
  classical
  -- Global `ContMDiff` of the extended section, for each form.
  have hsmooth : ∀ α : HolomorphicOneForms X, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (traceTotalSpaceMk (traceFunExt f α)) := by
    intro α y₀
    by_cases hy₀ : y₀ ∈ branchLocus f
    · exact (hext α y₀ hy₀).1
    · exact contMDiffAt_traceSection_ext_of_notMem_branchLocus f hf hnonconst α hy₀
  -- The underlying section assignment `α ↦ ⟨traceFunExt f α, …⟩`.
  set T₀ : HolomorphicOneForms X → HolomorphicOneForms Y :=
    fun α => ⟨traceFunExt f α, hsmooth α⟩ with hT₀_def
  -- **Local-coefficient convergence (the SOUND replacement for raw-operator convergence).**
  -- At a branch point `y₀`, the *fixed-frame* local coefficient of the raw trace converges to
  -- that of the extension: `hext`'s fixed-frame continuity gives the limit, and on the punctured
  -- neighborhood the extended local coefficient agrees with the raw one (off-branch they are
  -- equal). NB the raw OPERATOR does NOT converge in `ℂ →L[ℂ] ℂ` (kirovGenus ≥ 2 obstruction); only
  -- this fixed-frame scalar does — which is exactly what powers ℂ-linearity at branch points.
  have htendstoLC : ∀ (α : HolomorphicOneForms X) {y₀ : Y}, y₀ ∈ branchLocus f →
      Filter.Tendsto (fun y => traceLocalCoeff (traceFun f α) y₀ y) (𝓝[≠] y₀)
        (𝓝 (traceLocalCoeff (traceFunExt f α) y₀ y₀)) := by
    intro α y₀ hy₀
    have hca : Filter.Tendsto (fun y => traceLocalCoeff (traceFunExt f α) y₀ y) (𝓝[≠] y₀)
        (𝓝 (traceLocalCoeff (traceFunExt f α) y₀ y₀)) :=
      ((hext α y₀ hy₀).2.continuousWithinAt (s := {y₀}ᶜ))
    refine hca.congr' ?_
    -- On `𝓝[≠] y₀` points are off-branch, where `traceFunExt = traceFun`, so the local
    -- coefficients (which depend only on the coefficient at the point) agree.
    filter_upwards [eventually_notMem_branchLocus f hf hnonconst y₀] with y hy_off
    simp only [traceLocalCoeff, traceFunExt_of_notMem_branchLocus f α hy_off]
  -- Pointwise additivity of the extended coefficient (everywhere, incl. branch points).
  have hadd : ∀ (α β : HolomorphicOneForms X) (y : Y),
      traceFunExt f (α + β) y = traceFunExt f α y + traceFunExt f β y := by
    intro α β y
    by_cases hy : y ∈ branchLocus f
    · -- At a branch point each operator is `(local coeff) • id` (`…_eq_smul_id`); the scalar
      -- local coefficients add by the unique-limit argument in the fixed frame.
      have hLC : traceLocalCoeff (traceFunExt f (α + β)) y y
          = traceLocalCoeff (traceFunExt f α) y y + traceLocalCoeff (traceFunExt f β) y y := by
        refine tendsto_nhds_unique (htendstoLC (α + β) hy) ?_
        have hsum := (htendstoLC α hy).add (htendstoLC β hy)
        refine hsum.congr' ?_
        filter_upwards [eventually_notMem_branchLocus f hf hnonconst y] with z hz_off
        -- off-branch (at `z`): local coeff of `traceFun (α+β)` = sum, since `traceFun (α+β) z`
        -- splits (`traceFun_add`) and `inCoordinates …·1` is additive in the operator.
        have hoff : traceLocalCoeff (traceFun f (α + β)) y z
            = traceLocalCoeff (traceFun f α) y z + traceLocalCoeff (traceFun f β) y z := by
          simp only [traceLocalCoeff,
            traceFun_add_of_notMem_branchLocus f hf hnonconst α β hz_off]
          exact inCoordinates_apply_one_add (traceFun f α z) (traceFun f β z) y z
        exact hoff.symm
      rw [traceFunExt_branchPoint_eq_smul_id f (α + β) hy,
          traceFunExt_branchPoint_eq_smul_id f α hy, traceFunExt_branchPoint_eq_smul_id f β hy,
          hLC]
      exact add_smul (traceLocalCoeff (traceFunExt f α) y y)
        (traceLocalCoeff (traceFunExt f β) y y) (ContinuousLinearMap.id ℂ ℂ)
    · rw [traceFunExt_of_notMem_branchLocus f (α + β) hy,
        traceFunExt_of_notMem_branchLocus f α hy, traceFunExt_of_notMem_branchLocus f β hy,
        traceFun_add_of_notMem_branchLocus f hf hnonconst α β hy]
  -- Pointwise ℂ-homogeneity of the extended coefficient (everywhere, incl. branch points).
  have hsmul : ∀ (c : ℂ) (α : HolomorphicOneForms X) (y : Y),
      traceFunExt f (c • α) y = c • traceFunExt f α y := by
    intro c α y
    by_cases hy : y ∈ branchLocus f
    · have hLC : traceLocalCoeff (traceFunExt f (c • α)) y y
          = c • traceLocalCoeff (traceFunExt f α) y y := by
        refine tendsto_nhds_unique (htendstoLC (c • α) hy) ?_
        have hsm := (htendstoLC α hy).const_smul c
        refine hsm.congr' ?_
        filter_upwards [eventually_notMem_branchLocus f hf hnonconst y] with z hz_off
        have hoff : traceLocalCoeff (traceFun f (c • α)) y z
            = c • traceLocalCoeff (traceFun f α) y z := by
          simp only [traceLocalCoeff,
            traceFun_smul_of_notMem_branchLocus f hf hnonconst c α hz_off]
          exact inCoordinates_apply_one_smul c (traceFun f α z) y z
        exact hoff.symm
      rw [traceFunExt_branchPoint_eq_smul_id f (c • α) hy,
          traceFunExt_branchPoint_eq_smul_id f α hy, hLC, smul_assoc]
    · rw [traceFunExt_of_notMem_branchLocus f (c • α) hy,
        traceFunExt_of_notMem_branchLocus f α hy,
        traceFun_smul_of_notMem_branchLocus f hf hnonconst c α hy]
  -- Assemble the linear map. `+`/`•` of sections are pointwise (`coe_add`, `coe_smul`),
  -- so the section identities follow termwise from `hadd`/`hsmul`.
  refine ⟨{
    toFun := T₀
    map_add' := fun α β => ?_
    map_smul' := fun c α => ?_ }, ?_⟩
  · refine ContMDiffSection.ext (fun y => ?_)
    show traceFunExt f (α + β) y = (T₀ α + T₀ β).toFun y
    rw [hadd α β y]; rfl
  · refine ContMDiffSection.ext (fun y => ?_)
    show traceFunExt f (c • α) y = (c • T₀ α).toFun y
    rw [hsmul c α y]; rfl
  · -- Off-branch the section is the raw fibre sum, by construction of `traceFunExt`.
    intro α y hy
    show traceFunExt f α y = traceFun f α y
    exact traceFunExt_of_notMem_branchLocus f α hy

/-! ## Assembling into `HolomorphicOneForms Y` via branch extension

The off-branch fibre sum `traceFun f α` is now an **unconditional** holomorphic
one-form on `Y ∖ branchLocus f`: `contMDiffAt_traceFun_of_notMem_branchLocus`
depends only on `exists_localSheetSystem` (closed above) and the proven
`LocalSheetSystem.contMDiffAt_traceFun`. To upgrade it to a *global* element of
`HolomorphicOneForms Y` we must extend across the finite `branchLocus f`
(`finite_branchLocus_of_nonconstant`). The extended value at a branch point is the
removable-singularity **limit**, *not* the naive `finsum` (which is `0` there, since
the fibre over a branch point is still finite but the per-sheet derivatives blow up).
The global section's `toFun` is therefore the *extension*, characterized only by
agreeing with `traceFun` off the branch locus — we must not assert global smoothness
of `traceFun` itself, which is false at branch points.

### State of the assembly: framework PROVEN, one analytic fact ISOLATED

The regluing **and** the full ℂ-linearity are now proven outright in
`exists_traceForm_of_branchExtension` (above), which reduces `exists_traceForm` to a
single per-branch-point input `hext`. So the whole bundle/linearity scaffolding is
done and reusable; what remains is exactly that input, isolated below as
`traceExtendsAt_branchPoint` — the genuine analytic frontier.

`HolomorphicOneForms Y = ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω _`, so the extended
section `traceFunExt f α` must carry a *global* `ContMDiff` proof — including at branch
points. The per-branch-point input has two halves, **both consequences of the single
analytic crux** (local boundedness of the trace near a branch point):

1. **[GENUINE ANALYTIC CRUX — not in Mathlib, not in `Discharge/`]** *Local
   boundedness of the trace near each branch point.* In a chart at a branch point
   `y₀`, the coefficient `z ↦ traceFun f α (chart⁻¹ z)` is holomorphic on the punctured
   disk and **bounded** as `z → 0`. The classical reason: near `y₀` the cover has local
   normal form `w ↦ wᵉ` on each ramified sheet (`Discharge/Manifold/LocalNormalForm.lean`
   `MMeromorphicAt.exists_local_normal_form` gives the `wᵉ` model for the *map*), and
   the symmetric sum over the `e` colliding sheets of the per-sheet pullback
   `(α (sheetᵢ z)) ∘ (mfderiv sheetᵢ z)` cancels the `wᵉ⁻¹`-type blow-up via roots-of-
   unity orthogonality `∑ₖ ζ^{k(n+1)} = e·[e ∣ n+1]` (a Puiseux / Newton-symmetric-
   function computation). No project lemma currently supplies this; it is the analytic
   heart of the trace's well-definedness.

2. **Removable singularity + bundle regluing.** Given (1), Mathlib closes the chart
   step — `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (or
   `differentiableOn_update_limUnder_of_bddAbove`, file
   `Mathlib/Analysis/Complex/RemovableSingularity.lean`) — yielding *both* the
   continuity (`ContinuousAt (traceFunExt f α)`) and, after lifting the chart-level
   analyticity back through `contMDiffAt_hom_bundle`, the section `ContMDiffAt`. These
   are precisely the two conjuncts of `hext`.

Sound (classically true; Forster §10, Griffiths–Harris Ch. 2 §2.7). References:
Forster §4.22–4.25 (local normal form `wᵉ`), §10 (the trace). -/

/-! ### Bridge from chart-coefficient boundedness to the branch-point extension

The trace's branch-point extension `traceExtendsAt_branchPoint` is the *only* genuinely
analytic step of the whole trace construction. We discharge it here **modulo a single
clean local-boundedness input** (`traceLocalCoeff_mul_sub_tendsto_zero`, the analytic crux): the
*local coefficient* of the trace, read in the fixed chart at `y₀`, is bounded on a
punctured disk. From boundedness everything else is Mathlib's removable singularity
theorem plus the bundle-coordinate plumbing developed below.

The right scalar to control is **not** the discontinuous "global coefficient"
`(traceFun f α y) 1` (the value of the covector on the chart-`∂/∂z` *at the varying point
`y`*; discontinuous when the tangent bundle is non-trivial, exactly the obstruction
isolated in `CotangentCoeff.lean`), but the **local coefficient**

> `traceLocalCoeff f α y₀ y := inCoordinates … y₀ y y₀ y (traceFun f α y) (1 : ℂ)`,

the coordinate of the trace section in the *fixed `y₀`-trivialization*. This is the
object whose continuity/smoothness `Mathlib.contMDiffAt_hom_bundle` (`contMDiffAt_section`)
governs, and which `continuousAt_inCoordinates` (in `CotangentCoeff.lean`) already shows is
continuous wherever the section is smooth. -/

/-- **Section lift from the local coefficient (the converse of `continuousAt_inCoordinates`).**
If the scalar local coefficient `y ↦ traceLocalCoeff coeff y₀ y` is `ContMDiffAt` at `y₀`,
then the section `traceTotalSpaceMk coeff` is `ContMDiffAt` at `y₀`. This is the bundle-
coordinate engine: by `contMDiffAt_hom_bundle` the section is smooth iff its `inCoordinates`
operator is smooth into the fixed normed space `ℂ →L[ℂ] ℂ`; that operator equals
`(traceLocalCoeff coeff y₀ y) • id` (`clm_eq_apply_one_smul_id`), a scalar multiple of a
constant operator, hence smooth from the scalar's smoothness. -/
theorem contMDiffAt_traceTotalSpaceMk_of_localCoeff (coeff : Y → (ℂ →L[ℂ] ℂ)) {y₀ : Y}
    (hcoeff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (fun y => traceLocalCoeff coeff y₀ y) y₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω (traceTotalSpaceMk coeff) y₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- The `inCoordinates` operator equals `(scalar) • id`.
  have hsmul : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => (traceLocalCoeff coeff y₀ y) • ContinuousLinearMap.id ℂ ℂ) y₀ :=
    hcoeff.smul contMDiffAt_const
  refine hsmul.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))
  show ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
      y₀ y y₀ y (coeff y) = traceLocalCoeff coeff y₀ y • ContinuousLinearMap.id ℂ ℂ
  exact clm_eq_apply_one_smul_id _

/-- **Off-branch smoothness of the local coefficient.** Wherever `y₁` is off the branch
locus *and* lies in the fixed chart source at `y₀`, the scalar local coefficient
`y ↦ traceLocalCoeff (traceFun f α) y₀ y` is `ContMDiffAt` at `y₁`. Derived from the
off-branch section smoothness `contMDiffAt_traceFun_of_notMem_branchLocus` read in the
*fixed `y₀`-trivialization* (`contMDiffAt_section_iff` with the hom-bundle trivialization at
`y₀`, whose coordinate is exactly `inCoordinates … y₀ · y₀ ·` by `hom_trivializationAt_apply`),
then evaluated on the model basis vector `1`. -/
theorem contMDiffAt_traceLocalCoeff_of_notMem_branchLocus (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (α : HolomorphicOneForms X) (y₀ : Y) {y₁ : Y} (hy₁ : y₁ ∉ branchLocus f)
    (hy₁src : y₁ ∈ (chartAt ℂ y₀).source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (fun y => traceLocalCoeff (traceFun f α) y₀ y) y₁ := by
  -- The trace section is `ContMDiffAt` at `y₁` (off branch).
  have hsec : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (traceTotalSpaceMk (traceFun f α)) y₁ :=
    contMDiffAt_traceFun_of_notMem_branchLocus f hf hnonconst α hy₁
  -- Read it in the FIXED hom-bundle trivialization at `y₀`. Its base set is the tangent
  -- trivialization base set at `y₀` (∩ the trivial-bundle base set `univ`), i.e. the chart
  -- source at `y₀`, which contains `y₁`.
  have hy₁base : y₁ ∈ (trivializationAt (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) y₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    refine ⟨?_, Set.mem_univ _⟩
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy₁src
  have hcoord := ((trivializationAt (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) y₀).contMDiffAt_section_iff
      (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y)
      (s := fun y => traceFun f α y) hy₁base).mp hsec
  -- `(ehom ⟨y, traceFun f α y⟩).2 = inCoordinates … y₀ y y₀ y (traceFun f α y)` (defeq), an
  -- operator-valued `ContMDiffAt`; apply at `1` to get the scalar local coefficient.
  exact hcoord.clm_apply contMDiffAt_const

/-! ### Scalar manifold ↔ chart bridges (for maps `Y → ℂ`)

A scalar map `g : Y → ℂ` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ,ℂ) ω` at `y₀` exactly when its chart
pullback `g ∘ (chartAt ℂ y₀).symm` is `AnalyticAt` at `(chartAt ℂ y₀) y₀` (target chart on
the model space `ℂ` is the identity). We package the two directions needed for the
removable-singularity bridge. -/

/-- **Manifold smoothness ⟹ chart-pullback differentiability (scalar codomain).** If
`g : Y → ℂ` is `ContMDiffAt … ω` at `y₁`, its chart pullback `g ∘ (chartAt ℂ y₀).symm` is
`DifferentiableAt ℂ` at `(chartAt ℂ y₀) y₁`, provided `y₁` lies in the chart source. The
chart inverse `(chartAt ℂ y₀).symm : ℂ → Y` is `ContMDiffAt` at `(chartAt ℂ y₀) y₁`
(`contMDiffOn_chart_symm`, since `(chartAt ℂ y₀) y₁ ∈ target`) and maps it to `y₁`, so the
composite `g ∘ (chartAt ℂ y₀).symm : ℂ → ℂ` is `ContMDiffAt`, i.e. `DifferentiableAt`. -/
theorem differentiableAt_chartPullback_of_contMDiffAt {g : Y → ℂ} {y₀ y₁ : Y}
    (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω g y₁) (hy₁ : y₁ ∈ (chartAt ℂ y₀).source) :
    DifferentiableAt ℂ (g ∘ (chartAt ℂ y₀).symm) ((chartAt ℂ y₀) y₁) := by
  have hmem : (chartAt ℂ y₀) y₁ ∈ (chartAt ℂ y₀).target :=
    (chartAt ℂ y₀).map_source hy₁
  -- chart inverse is `ContMDiffAt` at the chart image, landing at `y₁`.
  have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ y₀).symm ((chartAt ℂ y₀) y₁) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (x := y₀) ((chartAt ℂ y₀) y₁) hmem).contMDiffAt
      ((chartAt ℂ y₀).open_target.mem_nhds hmem)
  have hsymm_eq : (chartAt ℂ y₀).symm ((chartAt ℂ y₀) y₁) = y₁ :=
    (chartAt ℂ y₀).left_inv hy₁
  have hg' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω g ((chartAt ℂ y₀).symm ((chartAt ℂ y₀) y₁)) := by
    rw [hsymm_eq]; exact hg
  -- composite `g ∘ chart.symm : ℂ → ℂ`, smooth at the chart image, hence differentiable.
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (g ∘ (chartAt ℂ y₀).symm) ((chartAt ℂ y₀) y₁) :=
    hg'.comp ((chartAt ℂ y₀) y₁) hsymm
  exact (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)

/-- **Chart-pullback analyticity ⟹ manifold smoothness (scalar codomain).** Converse of
`differentiableAt_chartPullback_of_contMDiffAt` at the basepoint: if `g : Y → ℂ` is
`ContinuousAt` at `y₀` and its chart pullback `g ∘ (chartAt ℂ y₀).symm` is `AnalyticAt ℂ` at
`(chartAt ℂ y₀) y₀`, then `g` is `ContMDiffAt … ω` at `y₀`. This is the `mpr` of
`contMDiffAt_iff` for a scalar target (the target chart is the identity, the source extended
chart is `chartAt ℂ y₀`), feeding the removably-extended analytic local coefficient back into
section smoothness. -/
theorem contMDiffAt_of_analyticAt_chartPullback {g : Y → ℂ} {y₀ : Y}
    (hcont : ContinuousAt g y₀)
    (han : AnalyticAt ℂ (g ∘ (chartAt ℂ y₀).symm) ((chartAt ℂ y₀) y₀)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω g y₀ := by
  rw [contMDiffAt_iff]
  refine ⟨hcont, ?_⟩
  have hrange : range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange, contDiffWithinAt_univ]
  -- Identify the extended-chart pullback with `g ∘ (chartAt ℂ y₀).symm` (target chart = id).
  have hfun : (extChartAt 𝓘(ℂ) (g y₀) ∘ g ∘ (extChartAt 𝓘(ℂ) y₀).symm)
      = (g ∘ (chartAt ℂ y₀).symm) := by
    funext z; simp
  have hbase : extChartAt 𝓘(ℂ) y₀ y₀ = (chartAt ℂ y₀) y₀ := by simp
  rw [hfun, hbase]
  exact han.contDiffAt

/-! ### The one-variable analytic heart of the local-boundedness crux

The whole branch-point boundedness reduces, sheet by sheet in coordinates, to the following
elementary one-variable fact: for an analytic `F` with `F w₀ = z₀` that is *not* locally
constant, the ratio `(F w − z₀)/F'(w)` tends to `0` as `w → w₀`. Geometrically `F` is the
map `f` read in charts at a ramification point; `(mfderiv f x)⁻¹ ∼ 1/F'(w)` blows up like
`(w − w₀)^{1−e}`, but it is multiplied by `z − z₀ = F(w) − z₀ ∼ (w − w₀)^e`, and the product
`∼ (w − w₀) → 0`. No symmetric-function cancellation is needed — just the factorization
`F − z₀ = (w − w₀)^e · g` with `g w₀ ≠ 0`. -/

/-- **One-variable analytic heart.** If `F` is analytic at `w₀` with `F w₀ = z₀` and is not
eventually constant `≡ z₀`, then `(F w − z₀)/F'(w) → 0` as `w → w₀` through `w ≠ w₀`. Proof:
`F − z₀ = (w − w₀)^(d+1) · g` (`g w₀ ≠ 0`), so for `w ≠ w₀` the ratio equals
`(w − w₀)·g/( (d+1)·g + (w − w₀)·g')`, whose limit is `0/((d+1) g w₀) = 0`. -/
theorem sub_div_deriv_tendsto_zero {F : ℂ → ℂ} {w₀ z₀ : ℂ}
    (hF : AnalyticAt ℂ F w₀) (hFw₀ : F w₀ = z₀)
    (hnc : ¬ ∀ᶠ w in 𝓝 w₀, F w = z₀) :
    Tendsto (fun w => (F w - z₀) / deriv F w) (𝓝[≠] w₀) (𝓝 0) := by
  -- Factor `F - z₀ = (w - w₀)^e • g`, `g` analytic, `g w₀ ≠ 0`.
  have hFsub : AnalyticAt ℂ (fun w => F w - z₀) w₀ := hF.sub analyticAt_const
  have hne0 : ¬ ∀ᶠ w in 𝓝 w₀, (fun w => F w - z₀) w = 0 := by
    simpa [sub_eq_zero] using hnc
  obtain ⟨e, g, hg, hg0, hFg⟩ :=
    (hFsub.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hne0
  -- `e ≥ 1`, write `e = d + 1`.
  have he : e ≠ 0 := by
    rintro rfl
    have h0 := hFg.self_of_nhds
    simp only [pow_zero, one_smul, hFw₀, sub_self] at h0
    exact hg0 h0.symm
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := Nat.exists_eq_succ_of_ne_zero he
  -- the candidate limit function `R`, continuous at `w₀` with value `0`.
  set R : ℂ → ℂ := fun w => (w - w₀) * g w / ((d + 1 : ℕ) * g w + (w - w₀) * deriv g w) with hR
  have hden0 : ((d + 1 : ℕ) : ℂ) * g w₀ ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨by exact_mod_cast (Nat.succ_ne_zero d), hg0⟩
  have hden : Tendsto (fun w => ((d + 1 : ℕ) : ℂ) * g w + (w - w₀) * deriv g w) (𝓝 w₀)
      (𝓝 (((d + 1 : ℕ) : ℂ) * g w₀)) := by
    have h1 : Tendsto (fun w => ((d + 1 : ℕ) : ℂ) * g w) (𝓝 w₀) (𝓝 (((d + 1 : ℕ) : ℂ) * g w₀)) :=
      tendsto_const_nhds.mul hg.continuousAt
    have h2 : Tendsto (fun w => (w - w₀) * deriv g w) (𝓝 w₀) (𝓝 (0 * deriv g w₀)) := by
      refine Tendsto.mul ?_ hg.deriv.continuousAt
      simpa using (continuous_sub_right w₀).tendsto w₀
    simpa using h1.add h2
  have hnum : Tendsto (fun w => (w - w₀) * g w) (𝓝 w₀) (𝓝 (0 * g w₀)) := by
    refine Tendsto.mul ?_ hg.continuousAt
    simpa using (continuous_sub_right w₀).tendsto w₀
  have hRlim : Tendsto R (𝓝 w₀) (𝓝 0) := by
    have h := hnum.div hden hden0
    simp only [zero_mul, zero_div] at h
    exact h
  have hgdiff_ev : ∀ᶠ w in 𝓝 w₀, DifferentiableAt ℂ g w := by
    filter_upwards [hg.eventually_analyticAt] with w hw using hw.differentiableAt
  obtain ⟨U, hUsub, hUopen, hw₀U⟩ := mem_nhds_iff.mp hFg
  have hcongr : (fun w => (F w - z₀) / deriv F w) =ᶠ[𝓝[≠] w₀] R := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hw₀U),
        mem_nhdsWithin_of_mem_nhds hgdiff_ev]
      with w hw_ne hwU hgw_diff
    have hwne : w ≠ w₀ := hw_ne
    have hFval : F w - z₀ = (w - w₀) ^ (d + 1) * g w := by
      have := hUsub hwU; simpa [smul_eq_mul] using this
    have hFeq : F =ᶠ[𝓝 w] (fun v => z₀ + (v - w₀) ^ (d + 1) * g v) := by
      filter_upwards [hUopen.mem_nhds hwU] with v hv
      have hvsub := hUsub hv
      simp only [Set.mem_setOf_eq, smul_eq_mul] at hvsub
      rw [add_comm]; exact sub_eq_iff_eq_add.mp hvsub
    have hpow : HasDerivAt (fun v : ℂ => (v - w₀) ^ (d + 1))
        (((d + 1 : ℕ) : ℂ) * (w - w₀) ^ d) w := by
      have h1 : HasDerivAt (fun v : ℂ => v - w₀) 1 w := by
        simpa using (hasDerivAt_id w).sub_const w₀
      simpa using h1.pow (d + 1)
    have hadd : HasDerivAt (fun v => z₀ + (v - w₀) ^ (d + 1) * g v)
        (((d + 1 : ℕ) : ℂ) * (w - w₀) ^ d * g w + (w - w₀) ^ (d + 1) * deriv g w) w :=
      (hpow.mul hgw_diff.hasDerivAt).const_add z₀
    have hderiv : deriv F w
        = ((d + 1 : ℕ) : ℂ) * (w - w₀) ^ d * g w + (w - w₀) ^ (d + 1) * deriv g w := by
      rw [hFeq.deriv_eq, hadd.deriv]
    rw [hFval, hderiv]
    have hp : (w - w₀) ^ d ≠ 0 := pow_ne_zero d (sub_ne_zero.mpr hwne)
    rw [show (w - w₀) ^ (d + 1) * g w = (w - w₀) ^ d * ((w - w₀) * g w) by rw [pow_succ]; ring,
       show (((d + 1 : ℕ) : ℂ) * (w - w₀) ^ d * g w + (w - w₀) ^ (d + 1) * deriv g w)
          = (w - w₀) ^ d * (((d + 1 : ℕ) : ℂ) * g w + (w - w₀) * deriv g w) by rw [pow_succ]; ring]
    rw [mul_div_mul_left _ _ hp]
  exact (hRlim.mono_left nhdsWithin_le_nhds).congr' hcongr.symm

/-! ### Exact per-preimage local coefficient and its growth

The trace's local coefficient, off the critical set, factors *per preimage* in one fixed chart
as `(α's local coefficient) / F'`, where `F = chartAt ℂ y₀ ∘ f ∘ (chartAt ℂ x₀).symm` reads `f` in
charts. The `symmL`/`(mfderiv f)⁻¹` obstruction factors **cancel** in the common `chartAt ℂ x₀`
frame — this is what makes the local coefficient continuous (kirovGenus ≥ 2) despite each factor being
discontinuous. From this exact value, the per-preimage growth `(c (f x) − c y₀) · (local coeff) →
0` is immediate from the one-variable `sub_div_deriv_tendsto_zero`. -/

/-- **Exact per-preimage local coefficient.** Off the critical set, the trace summand's
`y₀`-fixed-frame local coefficient at `x` equals `(α's local coefficient at `x`, read in the
`x₀`-frame) / F'(chartAt x₀ x)`, where `F = chartAt ℂ y₀ ∘ f ∘ (chartAt ℂ x₀).symm`. The proof
computes `inCoordinates(…)(traceSummand) 1 = (α x)((mfderiv f x)⁻¹ (∂/∂z))` and pushes everything
through the `chartAt x₀` and `chartAt y₀` frames: the trivialization coordinate maps are
`mfderiv` of charts (`TangentBundle.continuousLinearMapAt_trivializationAt` /
`symmL_trivializationAt`), the section `(mfderiv f x)⁻¹ = mfderiv g (f x)`
(`mfderiv_section_eq_inverse`), and `deriv (chart-section) = (F')⁻¹` since the chart-section is the
local inverse of `F`. -/
theorem traceSummand_inCoordinates_apply_one_eq_ref (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X) (y₀ : Y) {x₀ x : X}
    (hxcrit : x ∉ criticalSet f) (hxsrc : x ∈ (chartAt ℂ x₀).source)
    (hfx : f x ∈ (chartAt ℂ y₀).source) :
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
        y₀ (f x) y₀ (f x) (traceSummand f α x) (1 : ℂ)
      = (ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
          x₀ x x₀ x (α.toFun x) (1 : ℂ))
        / deriv (chartAt ℂ y₀ ∘ f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x) := by
  set c := chartAt ℂ y₀ with hc
  set ψ := chartAt ℂ x₀ with hψ
  have hstep1 : ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ
      (Bundle.Trivial Y ℂ) y₀ (f x) y₀ (f x) (traceSummand f α x) (1 : ℂ)
      = (traceSummand f α x)
          ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) y₀).symmL ℂ (f x) (1 : ℂ)) := by
    simp only [ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_apply]
    rfl
  have hsymmL : (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := Y)) y₀).symmL ℂ (f x) (1 : ℂ)
      = mfderiv 𝓘(ℂ) 𝓘(ℂ) c.symm (c (f x)) (1 : ℂ) := by
    have h := TangentBundle.symmL_trivializationAt (𝕜 := ℂ) (I := 𝓘(ℂ)) (x₀ := y₀) (x := f x) hfx
    rw [h, ModelWithCorners.range_eq_univ, mfderivWithin_univ]
    congr 1
  obtain ⟨g, V, hVopen, hfxV, hgfx, hsec, hgsmooth, hsf⟩ :=
    exists_twoSided_localInverse f hf hnonconst hxcrit
  have hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := hf.mdifferentiableAt (by decide)
  have hg_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (f x) :=
    (hgsmooth.contMDiffAt (hVopen.mem_nhds hfxV)).mdifferentiableAt (by decide)
  have hfs : (f ∘ g) =ᶠ[𝓝 (f x)] id := by
    filter_upwards [hVopen.mem_nhds hfxV] with y hy
    simp only [Function.comp_apply, id_eq]; exact hsec y hy
  have hinv : mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x) = (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x).inverse :=
    mfderiv_section_eq_inverse hgfx rfl hf_diff hg_diff hfs hsf
  have hcfx_mem : c (f x) ∈ c.target := c.map_source hfx
  have hcsymm_inv : c.symm (c (f x)) = f x := c.left_inv hfx
  have hcsymm_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm (c (f x)) := by
    have : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω c.symm (c (f x)) :=
      (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (x := y₀) (c (f x)) hcfx_mem).contMDiffAt
        (c.open_target.mem_nhds hcfx_mem)
    exact this.mdifferentiableAt (by decide)
  have hg_diff' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (c.symm (c (f x))) := by
    rw [hcsymm_inv]; exact hg_diff
  have hchain : (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x)) ((mfderiv 𝓘(ℂ) 𝓘(ℂ) c.symm (c (f x))) (1 : ℂ))
      = (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ c.symm) (c (f x))) (1 : ℂ) := by
    rw [mfderiv_comp_apply (c (f x)) hg_diff' hcsymm_diff (1 : ℂ), hcsymm_inv]
  have hval : (traceSummand f α x)
        ((mfderiv 𝓘(ℂ) 𝓘(ℂ) c.symm (c (f x))) (1 : ℂ))
      = (α.toFun x) ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ c.symm) (c (f x))) (1 : ℂ)) := by
    rw [traceSummand, ContinuousLinearMap.comp_apply, ← hinv]
    exact congrArg (α.toFun x) hchain
  set v : TangentSpace 𝓘(ℂ) x := (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ c.symm) (c (f x))) (1 : ℂ) with hv
  set a₀ : ℂ := ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ
      (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x) (1 : ℂ) with ha₀
  have hlin : (α.toFun x) v
      = ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x v)
          • a₀ := by
    rw [apply_eq_inCoordinates α x₀ x hxsrc v]
    set t : ℂ := (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x v
      with ht
    rw [ha₀, show (t : ℂ) = t • (1 : ℂ) by rw [smul_eq_mul, mul_one], map_smul]
    simp only [smul_eq_mul, mul_one]
  have hclm : (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x
      = mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ x := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (hxsrc)]
    congr 1
  have hψ_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x := by
    have : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ x :=
      (contMDiffOn_chart (I := 𝓘(ℂ)) (x := x₀)).contMDiffAt
        ((chartAt ℂ x₀).open_source.mem_nhds hxsrc)
    exact this.mdifferentiableAt (by decide)
  have hgcs_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (g ∘ c.symm) (c (f x)) :=
    hg_diff'.comp (c (f x)) hcsymm_diff
  have hgcs_pt : (g ∘ c.symm) (c (f x)) = x := by
    simp only [Function.comp_apply, hcsymm_inv, hgfx]
  have hψ_diff' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ ((g ∘ c.symm) (c (f x))) := by
    rw [hgcs_pt]; exact hψ_diff
  have ht_deriv : (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x v
      = deriv (ψ ∘ g ∘ c.symm) (c (f x)) := by
    rw [hclm, hv]
    rw [show (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ x) = (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ ((g ∘ c.symm) (c (f x))))
        from by rw [hgcs_pt]]
    have hcr : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (ψ ∘ (g ∘ c.symm)) (c (f x))) (1 : ℂ)
        = (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ ((g ∘ c.symm) (c (f x))))
            ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ c.symm) (c (f x))) (1 : ℂ)) :=
      mfderiv_comp_apply (c (f x)) hψ_diff' hgcs_diff (1 : ℂ)
    refine hcr.symm.trans ?_
    rw [mfderiv_eq_fderiv]
    rfl
  set w : ℂ := ψ x with hw
  set F : ℂ → ℂ := c ∘ f ∘ ψ.symm with hF
  set S : ℂ → ℂ := ψ ∘ g ∘ c.symm with hS
  have hc_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (c : Y → ℂ) (f x) :=
    (contMDiffOn_chart (I := 𝓘(ℂ)) (x := y₀)).contMDiffAt (c.open_source.mem_nhds hfx)
  have hψ_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ψ : X → ℂ) x :=
    (contMDiffOn_chart (I := 𝓘(ℂ)) (x := x₀)).contMDiffAt
      ((chartAt ℂ x₀).open_source.mem_nhds hxsrc)
  have hg_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g (f x) :=
    hgsmooth.contMDiffAt (hVopen.mem_nhds hfxV)
  have hcf_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (c ∘ f) x :=
    hc_smooth.comp x (hf.contMDiffAt)
  have hψg_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ψ ∘ g) (f x) := by
    have : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ (g (f x)) := by rw [hgfx]; exact hψ_smooth
    exact this.comp (f x) hg_smooth
  have hF_diff : DifferentiableAt ℂ F w :=
    differentiableAt_chartPullback_of_contMDiffAt hcf_smooth hxsrc
  have hS_diff : DifferentiableAt ℂ S (c (f x)) :=
    differentiableAt_chartPullback_of_contMDiffAt hψg_smooth hfx
  have hψsymm_inv : ψ.symm (ψ x) = x := ψ.left_inv hxsrc
  have hFw : F w = c (f x) := by
    simp only [hF, hw, Function.comp_apply, hψsymm_inv]
  have hwx : ψ.symm w = x := by rw [hw, hψsymm_inv]
  have hw_tgt : w ∈ ψ.target := by rw [hw]; exact ψ.map_source hxsrc
  have hψsymm_contAt : ContinuousAt ψ.symm w :=
    ψ.continuousOn_symm.continuousAt (ψ.open_target.mem_nhds hw_tgt)
  have hSF : (S ∘ F) =ᶠ[𝓝 w] id := by
    have h1 : ∀ᶠ u in 𝓝 w, u ∈ ψ.target := ψ.open_target.eventually_mem hw_tgt
    have hfψ_cont : ContinuousAt (fun u => f (ψ.symm u)) w := by
      have : ContinuousAt f (ψ.symm w) := by rw [hwx]; exact hf.continuous.continuousAt
      exact this.comp hψsymm_contAt
    have h2 : ∀ᶠ u in 𝓝 w, f (ψ.symm u) ∈ c.source := by
      have : f (ψ.symm w) ∈ c.source := by rw [hwx]; exact hfx
      exact hfψ_cont.eventually_mem (c.open_source.mem_nhds this)
    have h3 : ∀ᶠ u in 𝓝 w, (g ∘ f) (ψ.symm u) = ψ.symm u := by
      have := hψsymm_contAt.eventually (p := fun y => (g ∘ f) y = id y) (by rw [hwx]; exact hsf)
      simpa using this
    filter_upwards [h1, h2, h3] with u hu_tgt hu_src hu_pull
    show S (F u) = u
    have hFu : F u = c (f (ψ.symm u)) := by simp only [hF, Function.comp_apply]
    rw [hS]
    simp only [Function.comp_apply, hFu, c.left_inv hu_src]
    show ψ ((g ∘ f) (ψ.symm u)) = u
    rw [hu_pull, ψ.right_inv hu_tgt]
  have hF_hasDeriv : HasDerivAt F (deriv F w) w := hF_diff.hasDerivAt
  have hS_hasDeriv : HasDerivAt S (deriv S (c (f x))) (F w) := by
    rw [hFw]; exact hS_diff.hasDerivAt
  have hcomp_hasDeriv : HasDerivAt (S ∘ F) (deriv S (c (f x)) * deriv F w) w :=
    hS_hasDeriv.comp w hF_hasDeriv
  have hid_hasDeriv : HasDerivAt (S ∘ F) 1 w :=
    (hasDerivAt_id w).congr_of_eventuallyEq hSF
  have hmul1 : deriv S (c (f x)) * deriv F w = 1 :=
    hcomp_hasDeriv.unique hid_hasDeriv
  have hderivS : deriv S (c (f x)) = (deriv F w)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul1
  calc ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ
          (Bundle.Trivial Y ℂ) y₀ (f x) y₀ (f x) (traceSummand f α x) (1 : ℂ)
      = (α.toFun x) v := by rw [hstep1, hsymmL]; exact hval
    _ = (deriv S (c (f x))) • a₀ := by rw [hlin, ht_deriv]
    _ = (deriv F w)⁻¹ • a₀ := by rw [hderivS]
    _ = a₀ / deriv F w := by rw [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- **Per-preimage growth.** For a preimage `x₀ ∈ f⁻¹{y₀}`, the scaled trace-summand local
coefficient `(c (f x) − c y₀) · inCoordinates(…)(traceSummand f α x) 1` tends to `0` as `x → x₀`
through off-critical `x ≠ x₀`. By the exact value it equals `a₀(x) · (F(ψ x) − z₀)/F'(ψ x)` with
`a₀` the (continuous) local coefficient of `α`, and `(F(u) − z₀)/F'(u) → 0`
(`sub_div_deriv_tendsto_zero`, `F` analytic, `F(ψ x₀) = z₀`, not locally constant). -/
theorem traceSummand_localCoeff_mul_sub_tendsto (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X) {y₀ : Y} {x₀ : X}
    (hfx₀ : f x₀ = y₀) :
    Tendsto (fun x => (chartAt ℂ y₀ (f x) - chartAt ℂ y₀ y₀)
        * ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
            y₀ (f x) y₀ (f x) (traceSummand f α x) (1 : ℂ))
      (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 0) := by
  set c := chartAt ℂ y₀ with hc
  set ψ := chartAt ℂ x₀ with hψ
  set F : ℂ → ℂ := c ∘ f ∘ ψ.symm with hF
  set w₀ : ℂ := ψ x₀ with hw₀
  set z₀ : ℂ := c y₀ with hz₀
  have hx₀src : x₀ ∈ ψ.source := mem_chart_source ℂ x₀
  have hψsymm_inv : ψ.symm w₀ = x₀ := ψ.left_inv hx₀src
  have hF_an : AnalyticAt ℂ F w₀ := by
    have h := analyticAt_chartPullback f hf x₀
    have hpb : chartPullback f x₀ = F := by
      simp only [chartPullback, hF, hψ, hfx₀, hc]
    rw [hpb] at h
    exact h
  have hFw₀ : F w₀ = z₀ := by
    simp only [hF, hz₀, Function.comp_apply, hψsymm_inv, hfx₀]
  have hF_nonconst : ¬ ∀ᶠ u in 𝓝 w₀, F u = z₀ := by
    have h := chartPullback_not_eventuallyConst f hf hnonconst x₀
    intro hcon
    apply h
    have hpb : chartPullback f x₀ = F := by
      simp only [chartPullback, hF, hψ, hfx₀, hc]
    rw [hpb]
    have : F (ψ x₀) = z₀ := by rw [← hw₀]; exact hFw₀
    rw [show (chartAt ℂ x₀) x₀ = w₀ from rfl, this]
    exact hcon
  have hratio : Tendsto (fun u => (F u - z₀) / deriv F u) (𝓝[≠] w₀) (𝓝 0) :=
    sub_div_deriv_tendsto_zero hF_an hFw₀ hF_nonconst
  set a₀ : X → ℂ := fun x => ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ
      (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x) (1 : ℂ) with ha₀
  have ha₀_cont : ContinuousAt a₀ x₀ := continuousAt_localCoeff α x₀
  have hψ_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ψ : X → ℂ) x₀ :=
    (contMDiffOn_chart (I := 𝓘(ℂ)) (x := x₀)).contMDiffAt
      ((chartAt ℂ x₀).open_source.mem_nhds hx₀src)
  have hψ_contAt : ContinuousAt (ψ : X → ℂ) x₀ := hψ_smooth.continuousAt
  have hψ_tendsto : Tendsto (ψ : X → ℂ) (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝[≠] w₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hψ_contAt.mono_left nhdsWithin_le_nhds, ?_⟩
    have hsrc_ev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, x ∈ ψ.source :=
      mem_nhdsWithin_of_mem_nhds (ψ.open_source.mem_nhds hx₀src)
    have hne_ev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, x ≠ x₀ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards with x hx
      exact hx.2
    filter_upwards [hsrc_ev, hne_ev] with x hxsrc hxne
    show ψ x ∈ {w₀}ᶜ
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hcontra
    exact hxne (ψ.injOn hxsrc hx₀src (by rw [hcontra, hw₀]))
  have hratio_comp : Tendsto (fun x => (F (ψ x) - z₀) / deriv F (ψ x))
      (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 0) :=
    hratio.comp hψ_tendsto
  have ha₀_within : Tendsto a₀ (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 (a₀ x₀)) :=
    ha₀_cont.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun x => a₀ x * ((F (ψ x) - z₀) / deriv F (ψ x)))
      (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 0) := by
    have := ha₀_within.mul hratio_comp
    rwa [mul_zero] at this
  refine hprod.congr' ?_
  have hsrc_ev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, x ∈ ψ.source :=
    mem_nhdsWithin_of_mem_nhds (ψ.open_source.mem_nhds hx₀src)
  have hcrit_ev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, x ∉ criticalSet f := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards with x hx
    exact hx.1
  have hfsrc_ev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, f x ∈ c.source := by
    have hcont : ContinuousAt f x₀ := hf.continuous.continuousAt
    have hmem : f x₀ ∈ c.source := by rw [hfx₀]; exact mem_chart_source ℂ y₀
    exact mem_nhdsWithin_of_mem_nhds (hcont.preimage_mem_nhds (c.open_source.mem_nhds hmem))
  filter_upwards [hsrc_ev, hcrit_ev, hfsrc_ev] with x hxsrc hxcrit hfxsrc
  have hval := traceSummand_inCoordinates_apply_one_eq_ref f hf hnonconst α y₀ hxcrit hxsrc hfxsrc
  have hFψx : F (ψ x) = c (f x) := by
    simp only [hF, Function.comp_apply, ψ.left_inv hxsrc]
  show a₀ x * ((F (ψ x) - z₀) / deriv F (ψ x))
    = (c (f x) - z₀) * ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ
      (Bundle.Trivial Y ℂ) y₀ (f x) y₀ (f x) (traceSummand f α x) (1 : ℂ)
  rw [hval, hFψx, ha₀, hz₀]
  ring

/-- The linear map `φ ↦ inCoordinates … y₀ y y₀ y φ 1` (the local-coefficient functional). -/
noncomputable def localCoeffLin (y₀ y : Y) : (ℂ →L[ℂ] ℂ) →ₗ[ℂ] ℂ where
  toFun := fun φ => ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ
    (Bundle.Trivial Y ℂ) y₀ y y₀ y φ (1 : ℂ)
  map_add' := fun φ ψ => inCoordinates_apply_one_add φ ψ y₀ y
  map_smul' := by
    intro a φ
    simpa using inCoordinates_apply_one_smul a φ y₀ y

/-- **Additivity over the fibre.** Off the branch locus the local coefficient of the fibre-sum
trace is the fibre sum of the per-summand local coefficients. -/
theorem traceLocalCoeff_traceFun_eq_finsum (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    (y₀ : Y) {y : Y} (hy : y ∉ branchLocus f) :
    traceLocalCoeff (traceFun f α) y₀ y
      = ∑ᶠ x ∈ f ⁻¹' {y}, localCoeffLin y₀ y (traceSummand f α x) := by
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hy
  have h1 : traceLocalCoeff (traceFun f α) y₀ y = localCoeffLin y₀ y (traceFun f α y) := rfl
  rw [h1]
  have h2 : traceFun f α y = ∑ᶠ x ∈ f ⁻¹' {y}, traceSummand f α x := by
    unfold traceFun
    simp only [traceSummandAt]
  rw [h2, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, map_sum]

/-- **Off-branch fibre cardinality is locally constant.** For a regular value `y₁` there is an
open `V ∋ y₁` on which every fibre has the same cardinality `(f⁻¹{y₁}).ncard` (from the local
sheet system: the `n` injective holomorphic sheets sweep out each nearby fibre). -/
theorem fibre_ncard_locally_const (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {y₁ : Y} (hy₁ : y₁ ∉ branchLocus f) :
    ∃ V : Set Y, IsOpen V ∧ y₁ ∈ V ∧
      ∀ y ∈ V, (f ⁻¹' {y}).ncard = (f ⁻¹' {y₁}).ncard := by
  obtain ⟨S⟩ := exists_localSheetSystem f hf hnonconst hy₁
  have hcard_sheets : ∀ y ∈ S.V, (f ⁻¹' {y}).ncard = S.n := fun y hy => by
    rw [S.fibre_eq y hy, ← Set.image_univ,
      Set.ncard_image_of_injective _ (S.sheet_inj y hy), Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  exact ⟨S.V, S.isOpen_V, S.mem_V, fun y hy => by
    rw [hcard_sheets y hy, hcard_sheets y₁ S.mem_V]⟩

/-- The scaled per-summand local coefficient `Φ` summed in the fibre-sum assembly. -/
noncomputable def bigPhi (f : X → Y) (α : HolomorphicOneForms X) (y₀ : Y) (x : X) : ℂ :=
  (chartAt ℂ y₀ (f x) - chartAt ℂ y₀ y₀)
    * ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
        y₀ (f x) y₀ (f x) (traceSummand f α x) (1 : ℂ)

/-- **Uniform off-branch fibre-cardinality bound near a branch point** (the classical "off-branch
fibre cardinality = degree, hence locally bounded"). The fibre card is locally constant off the
branch locus (`fibre_ncard_locally_const`), and on a **preconnected punctured chart-ball**
`c.symm '' (Metric.ball z₀ r \ Badℂ)` — connected because a ball in `ℂ ≅ ℝ²` minus the finite set
`Badℂ = c '' (branchLocus f ∩ c.source)` is path-connected
(`Set.Countable.isPathConnected_ball_diff_complex`) — a locally-constant ℕ-valued function is
globally constant (`IsPreconnected.constant`, `ℕ` discrete). This punctured nbhd is eventual in
`𝓝[≠] y₀` (pushing `Metric.ball z₀ r \ Badℂ ∈ 𝓝[≠] z₀` along `c`), giving the uniform bound. -/
theorem fibre_ncard_bddAbove_near_branch (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {y₀ : Y} (_hy₀ : y₀ ∈ branchLocus f) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝[≠] y₀, y ∉ branchLocus f → (f ⁻¹' {y}).ncard ≤ N := by
  classical
  set c := chartAt ℂ y₀ with hc
  set z₀ := c y₀ with hz₀
  have hz₀tgt : z₀ ∈ c.target := c.map_source (mem_chart_source ℂ y₀)
  obtain ⟨r, hr, hball_sub⟩ := Metric.isOpen_iff.mp c.open_target z₀ hz₀tgt
  have hBfin : (branchLocus f).Finite := finite_branchLocus_of_nonconstant f hf hnonconst
  set Badℂ : Set ℂ := c '' (branchLocus f ∩ c.source) with hBad
  have hBadℂ_fin : Badℂ.Finite := ((hBfin.inter_of_left _).image c)
  set U : Set ℂ := Metric.ball z₀ r \ Badℂ with hU
  have hU_pc : IsPathConnected U :=
    Jacobians.Discharge.Set.Countable.isPathConnected_ball_diff_complex hr
      (Set.Finite.countable hBadℂ_fin)
  have hU_preconn : IsPreconnected U := hU_pc.isConnected.isPreconnected
  have hUsub : U ⊆ c.target := fun z hz => hball_sub (Set.diff_subset hz)
  set T : Set Y := c.symm '' U with hT
  have hT_preconn : IsPreconnected T :=
    hU_preconn.image c.symm (c.continuousOn_symm.mono hUsub)
  have hT_offbranch : ∀ y ∈ T, y ∉ branchLocus f := by
    rintro _ ⟨z, hzU, rfl⟩ hyB
    have hz_tgt : z ∈ c.target := hUsub hzU
    have hsrc : c.symm z ∈ c.source := c.map_target hz_tgt
    have : c (c.symm z) ∈ Badℂ := by
      rw [hBad]; exact Set.mem_image_of_mem c ⟨hyB, hsrc⟩
    rw [c.right_inv hz_tgt] at this
    exact hzU.2 this
  set card : Y → ℕ := fun y => (f ⁻¹' {y}).ncard with hcard
  have hcard_cont : ContinuousOn card T := by
    intro y hy
    have hyoff : y ∉ branchLocus f := hT_offbranch y hy
    obtain ⟨V, hVopen, hyV, hVcard⟩ := fibre_ncard_locally_const f hf hnonconst hyoff
    have hloc : ∀ᶠ y' in 𝓝[T] y, card y' = card y := by
      filter_upwards [nhdsWithin_le_nhds (hVopen.mem_nhds hyV)] with y' hy'V
      show (f ⁻¹' {y'}).ncard = (f ⁻¹' {y}).ncard
      rw [hVcard y' hy'V, hVcard y hyV]
    exact (tendsto_pure.mpr hloc).mono_right (pure_le_nhds _)
  obtain ⟨z₁, hz₁U⟩ := hU_pc.nonempty
  have hy₁T : c.symm z₁ ∈ T := ⟨z₁, hz₁U, rfl⟩
  set N : ℕ := card (c.symm z₁) with hN_def
  have hN : ∀ y ∈ T, card y = N :=
    fun y hy => IsPreconnected.constant hT_preconn hcard_cont hy hy₁T
  have hBadcompl : Badℂᶜ ∈ 𝓝[≠] z₀ := nhdsNE_le_cofinite z₀ hBadℂ_fin.compl_mem_cofinite
  have hball_nhds : Metric.ball z₀ r ∈ 𝓝[≠] z₀ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hr)
  have hU_ev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ U := by
    filter_upwards [hball_nhds, hBadcompl] with z hzb hzc
    exact ⟨hzb, hzc⟩
  have hsrc_nhds : c.source ∈ 𝓝 y₀ := c.open_source.mem_nhds (mem_chart_source ℂ y₀)
  have hc_contAt : ContinuousAt c y₀ := c.continuousOn.continuousAt hsrc_nhds
  have hc_tendsto : Tendsto c (𝓝[≠] y₀) (𝓝[≠] z₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc_contAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hsrc_nhds] with y hy_ne hy_src
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcy
    exact hy_ne (c.injOn hy_src (mem_chart_source ℂ y₀) (by rw [hcy, ← hz₀]))
  have hcU_ev : ∀ᶠ y in 𝓝[≠] y₀, c y ∈ U := hc_tendsto.eventually hU_ev
  have hT_ev : ∀ᶠ y in 𝓝[≠] y₀, y ∈ T := by
    filter_upwards [hcU_ev, nhdsWithin_le_nhds hsrc_nhds] with y hyU hy_src
    exact ⟨c y, hyU, c.left_inv hy_src⟩
  refine ⟨N, ?_⟩
  filter_upwards [hT_ev] with y hyT _
  exact (hN y hyT).le

/-- **[REMAINING ANALYTIC FRONTIER — the manifold-side of the boundedness crux]**

The `Y`-side of `traceLocalCoeff_mul_sub_tendsto_zero`: in the chart `c := chartAt ℂ y₀`, the
scaled local coefficient `(c y − c y₀) · traceLocalCoeff (traceFun f α) y₀ y → 0` as `y → y₀`
through `y ≠ y₀`. The crux itself follows by composing this with `c.symm` (which carries
`𝓝[≠] (c y₀)` to `𝓝[≠] y₀`); that reduction is fully proven below, so this lemma is the *single*
remaining input.

**Internal decomposition (the actual remaining work).**

⚠ **A naive `‖traceLocalCoeff coeff y₀ y‖ ≤ B·‖coeff y‖` with a uniform `B` is UNSOUND** (verified
2026-05-31). For arbitrary operators it is *equivalent* to local boundedness of the bare-fibre
coordinate `symmL(tangentTriv y₀) y 1`, which is exactly the **kirovGenus ≥ 2 obstruction**
(`CotangentCoeff.lean` `const_one_section_continuous_of_coordChange_fixes_one`): the constant
native-frame section is discontinuous and not locally bounded (no Riemannian metric is placed on
`TY`, so no compactness rescue). Hence one must NOT peel the `inCoordinates`/`symmL` factor off
the operator norm; the obstruction factors **cancel** only when the application
`inCoordinates(…)(traceSummand f α x) 1` is kept *together* and evaluated *exactly* in one chart.

1. *Exact per-preimage local coefficient (the real content).* Off-branch
   `traceLocalCoeff (traceFun f α) y₀ y = ∑_{x ∈ f⁻¹ y} inCoordinates(…)(traceSummand f α x) 1`
   (finite; `inCoordinates`-apply-`1` is additive over the fibre sum). Each term is the local
   coefficient of a section-pullback and computes **exactly** to `a(w) · S'(z)`, where
   `S := chart_X ∘ s ∘ c.symm` is the local section read in charts, `z = c y`, `w = S(z)`, and
   `a` is `α`'s coefficient in `chart_X`. Since `S = F⁻¹` for `F := c ∘ f ∘ chart_X.symm`, we get
   `S'(z) = 1/F'(w)`, so the term is `a(w)/F'(w)` — *no* `symmL` factor (the `(mfderiv f x)⁻¹`
   and `e.symmL` chart factors cancel in the common `chart_X` frame). Leverage the operator
   identity inside `contMDiffAt_pullback_section`
   (`inCoordinates(sheetPullback) = inCoordinates_X(α) ∘ inCoordinates(mfderiv s)`), evaluated at
   `1`. Then `(z − c y₀)·a(w)/F'(w) = a(w)·(F(w) − c y₀)/F'(w) → 0` by
   `sub_div_deriv_tendsto_zero` (PROVEN), `a` bounded.
   Helper lemmas already proven (kept in `scratch_E.lean` for integration): `norm_inverse_clm`
   (`‖T.inverse‖ = ‖T 1‖⁻¹` on `ℂ →L ℂ`) and `mfderiv_apply_one_eq_deriv_chartPullback`
   (`mfderiv h x 1 = deriv (h ∘ chart.symm) (chart x)` for `h : X → ℂ`).
2. *Assembly.* Properness (`X` compact ⟹ `f⁻¹ W ⊆ ⋃_j U_j` for small `W ∋ y₀`) + the uniform
   off-branch fibre cardinality reduce the finite fibre sum to a finite sum of terms each `→ 0`.

Sound (Forster §10; Griffiths–Harris Ch. 2 §2.7). -/
theorem traceLocalCoeff_mul_sub_tendsto_zero_Y (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f) :
    Tendsto (fun y => ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)
        * traceLocalCoeff (traceFun f α) y₀ y) (𝓝[≠] y₀) (𝓝 0) := by
  set c := chartAt ℂ y₀ with hc
  -- Uniform off-branch fibre-cardinality bound near the branch point.
  obtain ⟨N, hN⟩ := fibre_ncard_bddAbove_near_branch f hf hnonconst hy₀
  -- Per-preimage open neighborhood with the scaled-coefficient bound.
  have hloc : ∀ (x₀ : X), f x₀ = y₀ → ∀ ε' : ℝ, 0 < ε' →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∀ x ∈ U, x ∉ criticalSet f → x ≠ x₀ → ‖bigPhi f α y₀ x‖ < ε' := by
    intro x₀ hfx₀ ε' hε'
    have htend := traceSummand_localCoeff_mul_sub_tendsto f hf hnonconst α hfx₀
    have hev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, ‖bigPhi f α y₀ x‖ < ε' := by
      have := htend.eventually (Metric.ball_mem_nhds (0 : ℂ) hε')
      filter_upwards [this] with x hx
      simpa [bigPhi, Complex.dist_eq] using hx
    rw [eventually_nhdsWithin_iff] at hev
    rw [eventually_iff_exists_mem] at hev
    obtain ⟨V, hVnhd, hV⟩ := hev
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hVnhd
    refine ⟨U, hUopen, hxU, ?_⟩
    intro x hxU' hxcrit hxne
    exact hV x (hUsub hxU') ⟨hxcrit, hxne⟩
  have hproper : IsProperMap f := isProperMap_of_contMDiff f hf
  have hcompact : IsCompact (f ⁻¹' {y₀}) :=
    (isClosed_singleton.preimage hf.continuous).isCompact
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set ε' : ℝ := ε / (N + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  choose! U hUopen hUmem hUbnd using fun (p : X) (hp : f p = y₀) => hloc p hp ε' hε'
  obtain ⟨b, hbsub, hbfin, hbcover⟩ :=
    hcompact.elim_finite_subcover_image
      (b := f ⁻¹' {y₀}) (c := U)
      (fun i hi => hUopen i hi)
      (fun p hp => Set.mem_iUnion₂.mpr ⟨p, hp, hUmem p hp⟩)
  set V : Set X := ⋃ i ∈ b, U i with hVdef
  have hVopen : IsOpen V := isOpen_biUnion (fun i hi => hUopen i (hbsub hi))
  obtain ⟨W, hWopen, hWmem, hWsub⟩ := properNbhd hproper y₀ hVopen hbcover
  have hWnhd : W ∈ 𝓝[≠] y₀ := nhdsWithin_le_nhds (hWopen.mem_nhds hWmem)
  filter_upwards [hWnhd, hN, eventually_notMem_branchLocus f hf hnonconst y₀,
    self_mem_nhdsWithin] with y hyW hyN hybranch hyne
  have hynotbranch : y ∉ branchLocus f := hybranch
  have hyncard : (f ⁻¹' {y}).ncard ≤ N := hyN hynotbranch
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hynotbranch
  have hEsum := traceLocalCoeff_traceFun_eq_finsum f hf hnonconst α y₀ hynotbranch
  have hsummand : ∀ x ∈ f ⁻¹' {y},
      (c y - c y₀) * localCoeffLin y₀ y (traceSummand f α x) = bigPhi f α y₀ x := by
    intro x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [bigPhi, localCoeffLin, LinearMap.coe_mk, AddHom.coe_mk, hc]
    rw [hx]
  have heq : (c y - c y₀) * traceLocalCoeff (traceFun f α) y₀ y
      = ∑ᶠ x ∈ f ⁻¹' {y}, bigPhi f α y₀ x := by
    rw [hEsum, mul_finsum_mem _ _]
    exact finsum_mem_congr rfl hsummand
  have hxbound : ∀ x ∈ f ⁻¹' {y}, ‖bigPhi f α y₀ x‖ < ε' := by
    intro x hx
    have hxy : f x = y := by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; exact hx
    have hxcrit : x ∉ criticalSet f := fun hmem => hynotbranch ⟨x, hmem, hxy⟩
    have hxW : x ∈ f ⁻¹' W := by rw [Set.mem_preimage, hxy]; exact hyW
    have hxV : x ∈ V := hWsub hxW
    rw [hVdef, Set.mem_iUnion₂] at hxV
    obtain ⟨i, hib, hiU⟩ := hxV
    have hfiy₀ : f i = y₀ := by
      have := hbsub hib; rw [Set.mem_preimage, Set.mem_singleton_iff] at this; exact this
    have hxne_i : x ≠ i := by
      intro hcontra; rw [hcontra, hfiy₀] at hxy; exact hyne (by rw [Set.mem_singleton_iff, hxy])
    exact hUbnd i hfiy₀ x hiU hxcrit hxne_i
  rw [heq, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hcardN : hfin.toFinset.card ≤ N := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]; exact hyncard
  calc ‖∑ x ∈ hfin.toFinset, bigPhi f α y₀ x‖
      ≤ ∑ x ∈ hfin.toFinset, ‖bigPhi f α y₀ x‖ := norm_sum_le _ _
    _ ≤ hfin.toFinset.card • ε' := by
        refine Finset.sum_le_card_nsmul _ _ _ (fun x hx => ?_)
        exact le_of_lt (hxbound x ((Set.Finite.mem_toFinset hfin).mp hx))
    _ = (hfin.toFinset.card : ℝ) * ε' := by rw [nsmul_eq_mul]
    _ ≤ (N : ℝ) * ε' := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hε')
        exact_mod_cast hcardN
    _ < ε := by
        rw [hε'def]
        calc (N : ℝ) * (ε / (N + 1)) = (N / (N + 1)) * ε := by ring
          _ < 1 * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              rw [div_lt_one (by positivity)]
              linarith
          _ = ε := one_mul ε

/-- **[THE TRACE'S ANALYTIC CRUX — local boundedness at a branch point, little-o form]**

The single genuinely-analytic input. In the fixed chart `c := chartAt ℂ y₀`, the trace's
*local coefficient* `G z := traceLocalCoeff (traceFun f α) y₀ (c.symm z)` satisfies the
**local little-o** bound `(z - c y₀) · G z → 0` as `z → c y₀` (through the punctured
neighborhood). Equivalently `G =o[𝓝[≠] (c y₀)] (· - c y₀)⁻¹`: the trace one-form
`traceFun f α` on `Y ∖ branchLocus f`, read in the `y₀`-chart, has at worst a *removable*
singularity at the branch point (no genuine pole).

This is exactly the hypothesis of Mathlib's little-o removable-singularity theorem
`Complex.differentiableOn_update_limUnder_insert_of_isLittleO`, and it is the **only** fact
the whole trace construction is missing.

**Why the little-o (not global `BddAbove`).** Global boundedness over the whole chart target
is *false* in general (the chart codomain need not be relatively compact). The geometrically
correct — and provable — statement is the *local* one at `y₀`, and the little-o form is
strictly weaker than local boundedness yet still suffices for removability.

**Proof strategy (no roots-of-unity / Puiseux needed).** `‖traceFun f α y‖` is bounded by the
fibre sum `∑_{x ∈ f⁻¹ y} ‖α x‖ · ‖(mfderiv f x)⁻¹‖`. Near each branch preimage `x_j ∈ f⁻¹ y₀`
the map `f` has, in coordinates, an analytic normal form `F` with `F(0) = c y₀` and a
finite-order zero of `F - c y₀`; then the crude per-sheet estimate
`|z - c y₀| · ‖(mfderiv f x)⁻¹‖ = |F(w) - c y₀| / |F'(w)| → 0` (because `F - c y₀ = wᵉ · g`
with `g(0) ≠ 0`, so the ratio is `w · g/(e g + w g') → 0`). Summing the finitely many sheets
over the finite fibre gives `(z - c y₀) · G z → 0` — **no symmetric-function cancellation**,
just the triangle inequality. Holomorphy of `G` on the punctured disk is *not* used here; it
is supplied separately in `traceExtendsAt_branchPoint`. -/
theorem traceLocalCoeff_mul_sub_tendsto_zero (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f) :
    Tendsto
      (fun z : ℂ => (z - (chartAt ℂ y₀) y₀)
        * traceLocalCoeff (traceFun f α) y₀ ((chartAt ℂ y₀).symm z))
      (𝓝[≠] ((chartAt ℂ y₀) y₀)) (𝓝 0) := by
  set c := chartAt ℂ y₀ with hc
  set z₀ := c y₀ with hz₀
  have hz₀tgt : z₀ ∈ c.target := c.map_source (mem_chart_source ℂ y₀)
  have hsymm_z₀ : c.symm z₀ = y₀ := c.left_inv (mem_chart_source ℂ y₀)
  -- `c.symm` carries the punctured nbhd of `z₀` to the punctured nbhd of `y₀`.
  have hcs_cont : Tendsto c.symm (𝓝 z₀) (𝓝 y₀) := by
    have := c.continuousAt_symm hz₀tgt; rwa [ContinuousAt, hsymm_z₀] at this
  have hmap : Tendsto c.symm (𝓝[≠] z₀) (𝓝[≠] y₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcs_cont.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (c.open_target.mem_nhds hz₀tgt)]
      with z hz_ne hz_tgt
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcsy
    exact hz_ne (by rw [Set.mem_singleton_iff, hz₀, ← hcsy, c.right_inv hz_tgt])
  -- Compose the `Y`-side statement with `c.symm`, then rewrite `c (c.symm z) = z` on `c.target`.
  refine Tendsto.congr' ?_
    ((traceLocalCoeff_mul_sub_tendsto_zero_Y f hf hnonconst α hy₀).comp hmap)
  filter_upwards [nhdsWithin_le_nhds (c.open_target.mem_nhds hz₀tgt)] with z hz_tgt
  simp only [Function.comp_apply, ← hc, c.right_inv hz_tgt, ← hz₀]

/-- **Branch-value local-coefficient matching (now PROVEN, no analytic input).** With the
refactored `traceFunExt`, the branch value `traceFunExt f α y₀ = traceBranchValue f α y₀` is the
operator `L • id`, where `L` is the chart-pullback removable-singularity limit of the *local
coefficient* of the raw trace. The local coefficient of the extended trace at the center `y₀`
recovers exactly `L`:
`traceLocalCoeff (traceFunExt f α) y₀ y₀ = L = limUnder (𝓝[≠] (c y₀)) (z ↦ traceLocalCoeff (traceFun f α) y₀ (c⁻¹ z))`.

This is precisely the "local-coefficient matching" the section-smoothness bridge needs at the
puncture, and it is now a **definitional consequence of the center-frame identity**
`traceLocalCoeff_center` (`traceLocalCoeff (L • id) y₀ y₀ = (L • id) 1 = L`) — it requires *no*
boundedness/analytic input. (The old, design-flawed "raw convergence" conjunct — `ContinuousAt`
of the raw operator in the model fibre — was *provably false* for a non-trivial tangent bundle,
kirovGenus ≥ 2; it has been removed, and `traceExtendsAt_branchPoint` now expresses continuity in the
geometrically-correct *fixed frame*, see its statement.) -/
theorem traceFunExt_branchValue_correct (f : X → Y)
    (α : HolomorphicOneForms X) {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f) :
    traceLocalCoeff (traceFunExt f α) y₀ y₀ =
        limUnder (𝓝[≠] ((chartAt ℂ y₀) y₀))
          (fun z => traceLocalCoeff (traceFun f α) y₀ ((chartAt ℂ y₀).symm z)) := by
  rw [traceLocalCoeff_center, traceFunExt_of_mem_branchLocus f α hy₀, traceBranchValue]
  simp

/-- **[PROVEN MODULO the single analytic crux `traceLocalCoeff_mul_sub_tendsto_zero`]**

For every form `α` and every branch point `y₀ ∈ branchLocus f`, the canonical branch
extension `traceFunExt f α` is, at `y₀`:
* `ContMDiffAt` as a section of the cotangent bundle (the *holomorphic* extension), and
* `ContinuousAt` **in the fixed `y₀`-frame**, i.e. the local coefficient
  `y ↦ traceLocalCoeff (traceFunExt f α) y₀ y` is `ContinuousAt y₀`.

**Why the second conjunct is the *local coefficient*, not the raw operator.** The naive
"`ContinuousAt (traceFunExt f α) y₀`" — continuity of the operator read in the *model fibre*
`ℂ →L[ℂ] ℂ` — is **provably false** for a non-trivial tangent bundle (kirovGenus ≥ 2): the raw
operator `traceFun f α y` is `inCoordinates(…) ∘ clmAt(tangentTriv y₀) y`, whose chart-transition
factor is discontinuous (the `CotangentCoeff.lean` obstruction). The geometrically-correct
continuity statement is continuity of the section *in the bundle*, equivalently continuity of
its coordinate in the **fixed** `y₀`-trivialization — the local coefficient. (This is also
exactly the *shadow* of the first conjunct: section `ContMDiffAt` ⟹ local-coeff `ContMDiffAt`
⟹ `ContinuousAt`. The reduction lemma `exists_traceForm_of_branchExtension` consumes this
fixed-frame continuity soundly; see its `htendsto` argument, which is now phrased in local
coordinates.)

**Bridge structure.** The whole proof is the single fact: the *local coefficient* read in the
`y₀`-chart is `ContMDiffAt y₀`. It is holomorphic off `y₀` (off-branch section smoothness
`contMDiffAt_traceLocalCoeff_of_notMem_branchLocus` + the scalar chart bridges) and **bounded**
there, and has at worst a removable singularity (the crux `traceLocalCoeff_mul_sub_tendsto_zero`:
`(z - z₀)·G z → 0`), so by Mathlib's little-o removable singularity theorem
(`Complex.differentiableOn_update_limUnder_insert_of_isLittleO`, `DifferentiableOn.analyticAt`) it
extends analytically across `y₀`; its value at `y₀` matches `traceLocalCoeff (traceFunExt f α)
y₀ y₀` by `traceFunExt_branchValue_correct`. Then:
* conjunct 1 lifts it to the section via `contMDiffAt_traceTotalSpaceMk_of_localCoeff`;
* conjunct 2 is its `.continuousAt`.

Everything *downstream* — the global `ContMDiffSection` regluing and the full ℂ-linearity of
the trace — is proven unconditionally in `exists_traceForm_of_branchExtension`. -/
theorem traceExtendsAt_branchPoint (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
        (traceTotalSpaceMk (traceFunExt f α)) y₀ ∧
      ContinuousAt (fun y => traceLocalCoeff (traceFunExt f α) y₀ y) y₀ := by
  classical
  set c := chartAt ℂ y₀ with hc_def
  -- Abbreviations for the local coefficient of the raw / extended trace, and its chart pullback.
  set Hraw : Y → ℂ := fun y => traceLocalCoeff (traceFun f α) y₀ y with hHraw
  set Hext : Y → ℂ := fun y => traceLocalCoeff (traceFunExt f α) y₀ y with hHext
  set G : ℂ → ℂ := fun z => Hraw (c.symm z) with hG
  set z₀ : ℂ := c y₀ with hz₀
  -- The branch-value local-coefficient match (PROVEN, no analytic input).
  have hmatch : Hext y₀ = limUnder (𝓝[≠] z₀) G :=
    traceFunExt_branchValue_correct f α hy₀
  -- **Main claim**: the extended local coefficient `Hext` is `ContMDiffAt y₀`. Both conjuncts
  -- follow (conjunct 1 via the section-lift; conjunct 2 is its `ContinuousAt`).
  suffices hlc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω Hext y₀ by
    exact ⟨contMDiffAt_traceTotalSpaceMk_of_localCoeff (traceFunExt f α) hlc,
      hlc.continuousAt⟩
  -- Goal: `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ,ℂ) ω (fun y => traceLocalCoeff (traceFunExt f α) y₀ y) y₀`.
  set L : ℂ := limUnder (𝓝[≠] z₀) G with hL
  have hBfin : (branchLocus f).Finite := finite_branchLocus_of_nonconstant f hf hnonconst
  have hz₀_target : z₀ ∈ c.target := c.map_source (mem_chart_source ℂ y₀)
  -- The other branch points in the chart, pushed into the chart codomain: a finite set `Badℂ`
  -- of `c.target` not containing `z₀`. Removing it from `c.target` gives a nbhd `s` of `z₀` whose
  -- punctured part lands off the branch locus.
  set Bad : Set Y := (branchLocus f \ {y₀}) ∩ c.source with hBad
  have hBad_fin : Bad.Finite := (hBfin.diff.subset Set.inter_subset_left)
  set Badℂ : Set ℂ := c '' Bad with hBadℂ
  have hBadℂ_fin : Badℂ.Finite := hBad_fin.image _
  set s : Set ℂ := c.target \ Badℂ with hs_def
  have hz₀_notBadℂ : z₀ ∉ Badℂ := by
    rintro ⟨y, ⟨⟨_, hy_ne⟩, hy_src⟩, hcy⟩
    apply hy_ne
    -- `c y = z₀ = c y₀` with both in source ⟹ `y = y₀`.
    have := c.injOn hy_src (mem_chart_source ℂ y₀) (by rw [hcy])
    simpa using this
  have hz₀_s : z₀ ∈ s := ⟨hz₀_target, hz₀_notBadℂ⟩
  have hs_open : IsOpen s := c.open_target.sdiff hBadℂ_fin.isClosed
  have hs_mem : s ∈ 𝓝 z₀ := hs_open.mem_nhds hz₀_s
  -- On the punctured `s`, the chart preimage avoids the whole branch locus.
  have hpunct_off : ∀ z ∈ s \ {z₀}, c.symm z ∉ branchLocus f ∧ c.symm z ∈ c.source := by
    rintro z ⟨⟨hz_tgt, hz_notBad⟩, hz_ne⟩
    have hsrc : c.symm z ∈ c.source := c.map_target hz_tgt
    refine ⟨fun hzB => ?_, hsrc⟩
    -- if `c.symm z ∈ branchLocus`: either it is `y₀` (forces `z = z₀`) or it lands in `Badℂ`.
    by_cases hzy : c.symm z = y₀
    · exact hz_ne (by rw [Set.mem_singleton_iff, hz₀, ← hzy, c.right_inv hz_tgt])
    · exact hz_notBad ⟨c.symm z, ⟨⟨hzB, hzy⟩, hsrc⟩, c.right_inv hz_tgt⟩
  -- **`G` is complex-differentiable on the punctured `s`.**
  have hG_diff : DifferentiableOn ℂ G (s \ {z₀}) := by
    intro z hz
    obtain ⟨hz_off, hz_src⟩ := hpunct_off z hz
    -- `Hraw` is `ContMDiffAt (c.symm z)`; its `y₀`-chart pullback is differentiable at `c (c.symm z) = z`.
    have hHraw_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω Hraw (c.symm z) :=
      contMDiffAt_traceLocalCoeff_of_notMem_branchLocus f hf hnonconst α y₀ hz_off hz_src
    have hdiff := differentiableAt_chartPullback_of_contMDiffAt (y₀ := y₀) hHraw_smooth hz_src
    -- `c (c.symm z) = z`, so this is `DifferentiableAt G z`.
    rw [c.right_inv hz.1.1] at hdiff
    exact hdiff.differentiableWithinAt
  -- **`(z - z₀)·G z → 0`** (the analytic crux): `G` has at worst a removable singularity at `z₀`.
  have hG_tendsto : Tendsto (fun z => (z - z₀) * G z) (𝓝[≠] z₀) (𝓝 0) :=
    traceLocalCoeff_mul_sub_tendsto_zero f hf hnonconst α hy₀
  -- Convert to the little-o `(G - G z₀) =o[𝓝[≠] z₀] (· - z₀)⁻¹` consumed by removability.
  have hG_littleO : (fun z => G z - G z₀) =o[𝓝[≠] z₀] fun z => (z - z₀)⁻¹ := by
    refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz hcontra
      exact absurd (inv_eq_zero.mp hcontra) (sub_ne_zero.mpr hz)
    · -- `(G z - G z₀) / (z - z₀)⁻¹ = (z - z₀)·(G z - G z₀) → 0` (crux minus a `→0` constant tail).
      have hconst : Tendsto (fun z => (z - z₀) * G z₀) (𝓝[≠] z₀) (𝓝 0) := by
        have : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
          simpa using ((continuous_sub_right z₀).tendsto z₀).mono_left nhdsWithin_le_nhds
        simpa using this.mul_const (G z₀)
      have hdiff := hG_tendsto.sub hconst
      simp only [sub_zero] at hdiff
      have heq : (fun z => (G z - G z₀) / (z - z₀)⁻¹)
          = (fun z => (z - z₀) * G z - (z - z₀) * G z₀) := by
        funext z; rw [div_eq_mul_inv, inv_inv]; ring
      rw [heq]; exact hdiff
  -- **Removable singularity (little-o form)**: `update G z₀ L` is analytic at `z₀`.
  have hs_NE : s \ {z₀} ∈ 𝓝[≠] z₀ :=
    inter_mem (mem_nhdsWithin_of_mem_nhds hs_mem) self_mem_nhdsWithin
  have hupd : DifferentiableOn ℂ (Function.update G z₀ L) (insert z₀ (s \ {z₀})) := by
    have := Complex.differentiableOn_update_limUnder_insert_of_isLittleO hs_NE hG_diff hG_littleO
    rwa [← hL] at this
  have hins_mem : insert z₀ (s \ {z₀}) ∈ 𝓝 z₀ :=
    Filter.mem_of_superset hs_mem (fun z hz => by
      by_cases h : z = z₀
      · exact h ▸ Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨hz, h⟩)
  have hanalytic : AnalyticAt ℂ (Function.update G z₀ L) z₀ := hupd.analyticAt hins_mem
  -- **`Hext ∘ c.symm` agrees with the analytic extension on a full neighborhood of `z₀`.**
  have hsymm_z₀ : c.symm z₀ = y₀ := by rw [hz₀]; exact c.left_inv (mem_chart_source ℂ y₀)
  have hkey : (Hext ∘ c.symm) =ᶠ[𝓝 z₀] Function.update G z₀ L := by
    -- Off `z₀`: `Hext ∘ c.symm = Hraw ∘ c.symm = G = update G z₀ L`. At `z₀`: both equal `L`.
    have hpunct : (Hext ∘ c.symm) =ᶠ[𝓝[≠] z₀] Function.update G z₀ L := by
      -- On the punctured nbhd `Hext = Hraw` (pull back `traceFunExt =ᶠ traceFun` through `c.symm`).
      have hHeq : (Hext ∘ c.symm) =ᶠ[𝓝[≠] z₀] (Hraw ∘ c.symm) := by
        -- `c.symm` maps the punctured nbhd of `z₀` to the punctured nbhd of `y₀`:
        -- continuous at `z₀` (→ `y₀`) and injective on `c.target`, so `z ≠ z₀ ⟹ c.symm z ≠ y₀`.
        have hcs_cont : Filter.Tendsto c.symm (𝓝 z₀) (𝓝 y₀) := by
          have := (c.continuousAt_symm hz₀_target)
          rw [ContinuousAt, hsymm_z₀] at this; exact this
        have hmap : Filter.Tendsto c.symm (𝓝[≠] z₀) (𝓝[≠] y₀) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨hcs_cont.mono_left nhdsWithin_le_nhds, ?_⟩
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (c.open_target.mem_nhds hz₀_target)] with z hz_ne hz_tgt
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hcsy
          exact hz_ne (by rw [Set.mem_singleton_iff, hz₀, ← hcsy, c.right_inv hz_tgt])
        have hHeq' : Hext =ᶠ[𝓝[≠] y₀] Hraw := by
          filter_upwards [eventually_notMem_branchLocus f hf hnonconst y₀] with y hy_off
          simp only [hHext, hHraw, traceLocalCoeff, traceFunExt_of_notMem_branchLocus f α hy_off]
        exact hHeq'.comp_tendsto hmap
      filter_upwards [hHeq, self_mem_nhdsWithin] with z hz hz_ne
      rw [hz]
      simp only [hG, Function.comp_apply, Function.update_of_ne hz_ne]
    -- Patch the value at `z₀`: `(Hext ∘ c.symm) z₀ = Hext y₀ = L = update G z₀ L z₀`.
    have hval : (Hext ∘ c.symm) z₀ = Function.update G z₀ L z₀ := by
      simp only [Function.comp_apply, hsymm_z₀, Function.update_self]
      rw [hHext]; exact hmatch
    exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE hpunct hval
  -- **Conclude**: the extended local coefficient is `ContMDiffAt` at `y₀`.
  refine contMDiffAt_of_analyticAt_chartPullback ?_ ?_
  · -- `ContinuousAt Hext y₀`: `Hext = (Hext ∘ c.symm) ∘ c` near `y₀`; both factors continuous.
    have hcontPull : ContinuousAt (Hext ∘ c.symm) z₀ :=
      (hanalytic.continuousAt).congr hkey.symm
    have hc_contAt : ContinuousAt (c : Y → ℂ) y₀ :=
      (c.continuousOn.continuousAt (c.open_source.mem_nhds (mem_chart_source ℂ y₀)))
    have hcomp : ContinuousAt ((Hext ∘ c.symm) ∘ (c : Y → ℂ)) y₀ := by
      rw [hz₀] at hcontPull; exact hcontPull.comp hc_contAt
    refine hcomp.congr ?_
    filter_upwards [c.open_source.mem_nhds (mem_chart_source ℂ y₀)] with y hy
    simp only [Function.comp_apply, c.left_inv hy, hHext]
  · -- `AnalyticAt (Hext ∘ c.symm) z₀` from the analytic extension.
    rw [← hz₀]
    exact hanalytic.congr hkey.symm

/-- **Existence of the trace** `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)` as a genuine holomorphic
one-form linear map agreeing with the off-branch fibre sum `traceFun`. Now a one-line
consequence of the fully-proven reduction `exists_traceForm_of_branchExtension` and the
isolated per-branch-point analytic input `traceExtendsAt_branchPoint`. Sound (classically
true; Forster §10, Griffiths–Harris Ch. 2 §2.7). -/
theorem exists_traceForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    ∃ T : HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y,
      ∀ (α : HolomorphicOneForms X) (y : Y), y ∉ branchLocus f →
        (T α).toFun y = traceFun f α y :=
  exists_traceForm_of_branchExtension f hf hnonconst
    (fun α _y₀ hy₀ => traceExtendsAt_branchPoint f hf hnonconst α hy₀)

/-- **Trace (pushforward) of holomorphic one-forms**, `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)`,
extracted from `exists_traceForm`. Off the branch locus it is the holomorphic
fibre sum `traceFun`; across the (finite) branch locus it is the removable-singularity
extension. -/
noncomputable def traceForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y :=
  (exists_traceForm f hf hnonconst).choose

/-- `traceForm` agrees with the fibre-sum `traceFun` off the branch locus. -/
theorem traceForm_toFun_of_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    (traceForm f hf hnonconst α).toFun y = traceFun f α y :=
  (exists_traceForm f hf hnonconst).choose_spec α y hy

/-- **Local sheet decomposition of the trace form.** Off the branch locus there is a
local sheet system `S` at `y₀` over whose base `S.V` the trace one-form is the finite
sum of the per-sheet pullbacks: at every off-branch `y ∈ S.V`,
`(traceForm f hf hnonconst α).toFun y = ∑ᵢ sheetPullback α (S.sheet i) y`.

This is the **per-base-neighborhood input to the period-level projection formula**:
to integrate `traceForm f hf α` along a loop `δ` (which avoids the branch locus),
cover the compact `δ([0,1])` by finitely many such bases, and on each the trace
splits into sheet pullbacks, each of which is `∫_δ sheetPullback = ∫_{sheet∘δ} α`
(`lineIntegral_pullback_section`). Combines `exists_localSheetSystem` (the off-branch
covering) with `LocalSheetSystem.traceFun_eq_sum_sheetPullback` and the off-branch
agreement `traceForm_toFun_of_notMem_branchLocus`. -/
theorem exists_localSheetSystem_traceForm_eq_sum (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    ∃ S : LocalSheetSystem f y₀, ∀ y ∈ S.V, y ∉ branchLocus f →
      (traceForm f hf hnonconst α).toFun y = ∑ i, sheetPullback α (S.sheet i) y := by
  obtain ⟨S⟩ := exists_localSheetSystem f hf hnonconst hy₀
  refine ⟨S, fun y hyV hyB => ?_⟩
  rw [traceForm_toFun_of_notMem_branchLocus f hf hnonconst α hyB]
  exact S.traceFun_eq_sum_sheetPullback hf α hyV

/-! ## The projection formula (period level)

The eventual goal is the multi-sheet projection formula
`lineIntegral (traceForm f hf α) δ = ∑ₖ lineIntegral α (liftₖ)`, where `liftₖ` are
the lifts of a closed loop `δ` (off the branch locus) to the sheets of the cover.
The heart is the proven change-of-variables `lineIntegral_pullback`:
`lineIntegral α (f ∘ γ) = lineIntegral (pullbackForm f hf α) γ`.

We prove the **single-sheet** form in full: along one global holomorphic section
`s : Y → X` of `f` (with lift `s ∘ δ`), the line integral of the pulled-back form
`pullbackForm s hs α` over `δ` equals the line integral of `α` over the lift
`s ∘ δ`. The full multi-sheet identity is the sum of these single-sheet identities
over the sheet sections; what is missing is the lift/monodromy assembly producing
the indexed family of global lifts (the loop-lifting `PreimageCycle` machinery in
`PeriodLattice.lean`, gated on `exists_preimageCycle_of_off_branchLocus`). -/

/-- **Single-sheet projection formula (line integral).** For a holomorphic section
`s : Y → X` of `f`, the line integral of the pulled-back form `pullbackForm s hs α`
along a (regular) path `δ` equals the line integral of `α` along the lift `s ∘ δ`.

This is exactly `lineIntegral_pullback` read with the section `s` as the map: it is
the per-sheet term of the projection formula. The lift `s ∘ δ` is the path in `X`
covering `δ` (`f ∘ (s ∘ δ) = δ` since `f ∘ s = id`). -/
theorem lineIntegral_pullback_section (s : Y → X) (hs : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω s)
    (α : HolomorphicOneForms X) (δ : ℝ → Y)
    (hδ_cont : Continuous δ)
    (hδ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t)).toFun ∘ δ) t) :
    lineIntegral (pullbackForm s hs α) δ = lineIntegral α (s ∘ δ) :=
  (lineIntegral_pullback s hs α δ hδ_cont hδ_diff).symm

/-- **Single-sheet projection formula for the trace.** When `f` admits a *global*
holomorphic section `s` and the trace form coincides with the single-sheet pullback
`pullbackForm s hs α` (e.g. a one-sheeted cover, where the fibre over each off-branch
point is the single point `s y`), the line integral of the trace along `δ` equals
the line integral of `α` along the lift `s ∘ δ`.

The coincidence hypothesis `htrace` is what the multi-sheet assembly supplies as a
sum; here we isolate the clean single-sheet consequence of `lineIntegral_pullback`. -/
theorem lineIntegral_traceForm_single_sheet (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (s : Y → X) (hs : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω s)
    (α : HolomorphicOneForms X) (δ : ℝ → Y)
    (hδ_cont : Continuous δ)
    (hδ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t)).toFun ∘ δ) t)
    (htrace : traceForm f hf hnonconst α = pullbackForm s hs α) :
    lineIntegral (traceForm f hf hnonconst α) δ = lineIntegral α (s ∘ δ) := by
  rw [htrace]
  exact lineIntegral_pullback_section s hs α δ hδ_cont hδ_diff

/-- Evaluating a finite sum of holomorphic one-forms at `y` against a tangent
vector `v` equals the sum of the pointwise evaluations. -/
theorem sum_toFun_apply {k : ℕ} (forms : Fin k → HolomorphicOneForms Y) (y : Y) (v : ℂ) :
    (∑ i, forms i).toFun y v = ∑ i, (forms i).toFun y v := by
  classical
  induction k with
  | zero =>
    show (0 : HolomorphicOneForms Y).toFun y v = 0
    rfl
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ← ih (fun i => forms i.succ)]
    -- Addition of sections is pointwise; the covector evaluation distributes.
    rfl

/-- Line integral of a finite sum of forms is the sum of line integrals, under
per-form integrability along `γ`. (Finset version of `lineIntegral_add`, by
induction on the index set.) -/
theorem lineIntegral_sum {k : ℕ} (forms : Fin k → HolomorphicOneForms Y) (δ : ℝ → Y)
    (hint : ∀ i, IntervalIntegrable
      (fun t : ℝ => (forms i).toFun (δ t) (pathSpeed δ t)) MeasureTheory.volume 0 1) :
    lineIntegral (∑ i, forms i) δ = ∑ i, lineIntegral (forms i) δ := by
  classical
  induction k with
  | zero => simp [lineIntegral_zero]
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hint_tail : ∀ i : Fin m, IntervalIntegrable
        (fun t : ℝ => (forms i.succ).toFun (δ t) (pathSpeed δ t)) MeasureTheory.volume 0 1 :=
      fun i => hint i.succ
    have hint_head := hint 0
    have hint_tailsum : IntervalIntegrable
        (fun t : ℝ => (∑ i : Fin m, forms i.succ).toFun (δ t) (pathSpeed δ t))
          MeasureTheory.volume 0 1 := by
      have heq : (fun t : ℝ => (∑ i : Fin m, forms i.succ).toFun (δ t) (pathSpeed δ t)) =
          ∑ i : Fin m, (fun t : ℝ => (forms i.succ).toFun (δ t) (pathSpeed δ t)) := by
        funext t; rw [Finset.sum_apply]; exact sum_toFun_apply _ (δ t) (pathSpeed δ t)
      rw [heq]
      exact IntervalIntegrable.sum _ (fun i _ => hint_tail i)
    rw [lineIntegral_add _ _ _ hint_head hint_tailsum, ih (fun i => forms i.succ) hint_tail]

/-- **Multi-sheet projection formula (line integral).** Given a family of global
holomorphic sections `s i : Y → X` whose pullbacks sum to the trace form
(`htrace`), the line integral of the trace along `δ` is the sum over sheets of the
line integrals of `α` along the lifts `s i ∘ δ`. Combines `lineIntegral_sum` with
the single-sheet `lineIntegral_pullback_section`. This is the period-level
projection formula; the remaining classical input is producing the sheet sections
+ the `htrace` decomposition (the loop-lifting machinery). -/
theorem lineIntegral_traceForm_eq_sum_lifts {k : ℕ} (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (s : Fin k → Y → X) (hs : ∀ i, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (s i))
    (α : HolomorphicOneForms X) (δ : ℝ → Y)
    (hδ_cont : Continuous δ)
    (hδ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t)).toFun ∘ δ) t)
    (hint : ∀ i, IntervalIntegrable
      (fun t : ℝ => (pullbackForm (s i) (hs i) α).toFun (δ t) (pathSpeed δ t))
        MeasureTheory.volume 0 1)
    (htrace : traceForm f hf hnonconst α = ∑ i, pullbackForm (s i) (hs i) α) :
    lineIntegral (traceForm f hf hnonconst α) δ = ∑ i, lineIntegral α (s i ∘ δ) := by
  rw [htrace, lineIntegral_sum _ δ hint]
  exact Finset.sum_congr rfl fun i _ =>
    lineIntegral_pullback_section (s i) (hs i) α δ hδ_cont hδ_diff

/-! ## Covariant functoriality of the trace

`traceForm` is covariant to `f` (a trace sums over the sheets of the cover, and
sheet counts of the identity / a composite cover behave as expected). These are the
two functoriality laws of the genuine geometric trace `f₊`; together with the
single branch-extension input (`traceExtendsAt_branchPoint`) they are the trace's
remaining analytic content. They drive the ambient pullback `Tᵀ` downstream
(`Jacobians/TracePullback.lean`).

Each is stated with the non-constancy hypotheses that `traceForm` itself requires.
The constant-map bookkeeping is handled once, downstream, by the total wrapper
`traceFormTotal` and its laws. -/

/-- **`f₊(id) = id`** — the identity map is a one-sheeted unbranched cover, so its
trace is the identity. Honest gap: classically true (Forster §10), but in this
formalization `traceForm` is the removable-singularity extension of the off-branch
fibre sum, and proving the extension of the (single-sheet) fibre sum for `id` equals
`id` on *all* of `X` is the identity-theorem upgrade of the off-branch agreement —
the same analytic status as `traceExtendsAt_branchPoint`. -/
theorem traceForm_id (hnonconst : ¬ ∃ x₀ : X, ∀ x, (id : X → X) x = x₀) :
    traceForm (id : X → X) contMDiff_id hnonconst =
      LinearMap.id (R := ℂ) (M := HolomorphicOneForms X) := by
  -- `id` is injective on every neighborhood, so its critical set — hence its branch
  -- locus — is empty. Thus the trace agrees with the fibre sum at *every* point, and
  -- the singleton fibre `id⁻¹'{y} = {y}` collapses the sum to `α y`.
  have hcrit : criticalSet (id : X → X) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact hx ⟨Set.univ, Filter.univ_mem, Set.injOn_id _⟩
  have hbranch : branchLocus (id : X → X) = ∅ := by
    rw [branchLocus, hcrit, Set.image_empty]
  refine LinearMap.ext (fun α => ?_)
  refine ContMDiffSection.ext (fun y => ?_)
  show (traceForm (id : X → X) contMDiff_id hnonconst α).toFun y = α.toFun y
  have hy : y ∉ branchLocus (id : X → X) := by rw [hbranch]; exact Set.notMem_empty y
  rw [traceForm_toFun_of_notMem_branchLocus (id : X → X) contMDiff_id hnonconst α hy]
  -- `traceFun id α y = ∑ᶠ x ∈ id⁻¹'{y}, traceSummandAt id α y x`; the fibre is `{y}`.
  show (∑ᶠ (x : X) (_ : x ∈ (id : X → X) ⁻¹' {y}), traceSummandAt (id : X → X) α y x)
      = α.toFun y
  have hfib : (id : X → X) ⁻¹' {y} = {y} := by simp [Set.preimage_id]
  rw [hfib, finsum_mem_singleton]
  show traceSummand (id : X → X) α y = α.toFun y
  show (α.toFun y).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) y).inverse) = α.toFun y
  -- `mfderiv id y = id`, so its inverse is `id` and the comp collapses.
  have hinv : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) y).inverse
      = ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) y) := by
    rw [mfderiv_id]; exact ContinuousLinearMap.inverse_id
  rw [hinv]; exact ContinuousLinearMap.comp_id _

/-- **Local coefficient of an arbitrary smooth section is `ContMDiffAt`.** Generalizes
`contMDiffAt_traceLocalCoeff_of_notMem_branchLocus` from `traceFun f α` to any smooth section
`s : HolomorphicOneForms Y`: read in the FIXED `y₀`-hom-trivialization the section's coordinate is
`ContMDiffAt`, hence the scalar local coefficient (its value on `1`) is too. (No branch-locus
hypothesis — `s` is globally smooth.) -/
theorem contMDiffAt_localCoeff_section (s : HolomorphicOneForms Y) (y₀ : Y) {y₁ : Y}
    (hy₁src : y₁ ∈ (chartAt ℂ y₀).source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (fun y => traceLocalCoeff (s.toFun) y₀ y) y₁ := by
  have hsec : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (traceTotalSpaceMk (s.toFun)) y₁ := s.contMDiff_toFun.contMDiffAt
  have hy₁base : y₁ ∈ (trivializationAt (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) y₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    refine ⟨?_, Set.mem_univ _⟩
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy₁src
  have hcoord := ((trivializationAt (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) y₀).contMDiffAt_section_iff
      (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y)
      (s := fun y => s.toFun y) hy₁base).mp hsec
  exact hcoord.clm_apply contMDiffAt_const

/-- Off the critical set, `mfderiv g y` is invertible (it has a two-sided local-inverse
section). -/
theorem isInvertible_mfderiv_of_notMem_criticalSet (g : Y → X) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgnc : ¬ ∃ x₀ : X, ∀ y, g y = x₀) {y : Y} (hy : y ∉ criticalSet g) :
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) g y).IsInvertible := by
  obtain ⟨s, V, hVopen, hgyV, hsgy, hsec, hssmooth, hsf⟩ :=
    exists_twoSided_localInverse g hg hgnc hy
  have hg_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g y := hg.mdifferentiableAt (by decide)
  have hs_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s (g y) :=
    ((hssmooth.contMDiffAt (hVopen.mem_nhds hgyV)).mdifferentiableAt (by decide))
  have hg_diff' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (s (g y)) := by rw [hsgy]; exact hg_diff
  have hfs : (g ∘ s) =ᶠ[𝓝 (g y)] id := by
    filter_upwards [hVopen.mem_nhds hgyV] with z hz; exact hsec z hz
  have hcomp_gs : (mfderiv 𝓘(ℂ) 𝓘(ℂ) g y).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s (g y)) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) (g y)) := by
    have h1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ s) (g y) = mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) (g y) :=
      hfs.mfderiv_eq
    rw [mfderiv_id] at h1
    rw [← h1, mfderiv_comp (g y) hg_diff' hs_diff, hsgy]
  have hcomp_sg : (mfderiv 𝓘(ℂ) 𝓘(ℂ) s (g y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g y) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) y) := by
    have h1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (s ∘ g) y = mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : Y → Y) y :=
      hsf.mfderiv_eq
    rw [mfderiv_id] at h1
    rw [← h1, mfderiv_comp y hs_diff hg_diff]
  refine ⟨ContinuousLinearEquiv.equivOfInverse (mfderiv 𝓘(ℂ) 𝓘(ℂ) g y)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) s (g y)) ?_ ?_, rfl⟩
  · intro v
    have := ContinuousLinearMap.ext_iff.mp hcomp_sg v
    simpa using this
  · intro v
    have := ContinuousLinearMap.ext_iff.mp hcomp_gs v
    simpa using this

/-- **Covariance of the trace: `(g ∘ f)₊ = g₊ ∘ f₊`** (Griffiths–Harris Ch. 2 §2.7). Both sides
are smooth forms; their **fixed-frame local coefficients** (not the discontinuous raw fibre
components — the kirovGenus≥2 `CotangentCoeff` obstruction) agree off the finite bad set
`B = branchLocus (g∘f) ∪ branchLocus g ∪ g '' branchLocus f` via the off-branch fibre
factorization `traceFun (g∘f) α z = traceFun g (traceForm f α) z` (partition
`(g∘f)⁻¹{z} = ⊔_{y∈g⁻¹z} f⁻¹{y}` + chain rule `(mfderiv (g∘f))⁻¹ = (mfderiv f)⁻¹∘(mfderiv g)⁻¹` +
pulling the common right-comp out of the inner finsum). The local coefficients are `ContinuousOn`
the chart source (`contMDiffAt_localCoeff_section`), `Bᶜ` is dense (finite `B`, perfect space), so
they agree everywhere; evaluating at the chart center (`traceLocalCoeff_center`) gives the operator
equality. -/
theorem traceForm_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hfnc : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (hgnc : ¬ ∃ z₀ : Z, ∀ y, g y = z₀)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) (hgfnc : ¬ ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀) :
    traceForm (g ∘ f) hgf hgfnc =
      (traceForm g hg hgnc).comp (traceForm f hf hfnc) := by
  refine LinearMap.ext (fun α => ?_)
  rw [LinearMap.comp_apply]
  refine ContMDiffSection.ext (fun z₀ => ?_)
  set L' := traceForm (g ∘ f) hgf hgfnc α with hL'
  set R' := traceForm g hg hgnc (traceForm f hf hfnc α) with hR'
  apply ContinuousLinearMap.ext_ring
  set B : Set Z := branchLocus (g ∘ f) ∪ branchLocus g ∪ g '' (branchLocus f) with hB
  have hBfin : B.Finite := by
    refine (Set.Finite.union (Set.Finite.union ?_ ?_) ?_)
    · exact finite_branchLocus_of_nonconstant (g ∘ f) hgf hgfnc
    · exact finite_branchLocus_of_nonconstant g hg hgnc
    · exact (finite_branchLocus_of_nonconstant f hf hfnc).image g
  set t : Set Z := (chartAt ℂ z₀).source with ht
  have hcontL : ContinuousOn (fun z => traceLocalCoeff (L'.toFun) z₀ z) t := by
    intro z₁ hz₁
    refine (contMDiffAt_localCoeff_section L' z₀ hz₁).continuousAt.continuousWithinAt
  have hcontR : ContinuousOn (fun z => traceLocalCoeff (R'.toFun) z₀ z) t := by
    intro z₁ hz₁
    refine (contMDiffAt_localCoeff_section R' z₀ hz₁).continuousAt.continuousWithinAt
  have hagree : Set.EqOn (fun z => traceLocalCoeff (L'.toFun) z₀ z)
      (fun z => traceLocalCoeff (R'.toFun) z₀ z) (t \ B) := by
    intro z hz
    obtain ⟨_hzt, hzB⟩ := hz
    have hz_gf : z ∉ branchLocus (g ∘ f) := fun h => hzB (Or.inl (Or.inl h))
    have hz_g : z ∉ branchLocus g := fun h => hzB (Or.inl (Or.inr h))
    have hz_gimf : z ∉ g '' (branchLocus f) := fun h => hzB (Or.inr h)
    have hLeq : L'.toFun z = traceFun (g ∘ f) α z := by
      rw [hL']; exact traceForm_toFun_of_notMem_branchLocus (g ∘ f) hgf hgfnc α hz_gf
    have hReq : R'.toFun z = traceFun g (traceForm f hf hfnc α) z := by
      rw [hR']; exact traceForm_toFun_of_notMem_branchLocus g hg hgnc _ hz_g
    have hfact : traceFun (g ∘ f) α z = traceFun g (traceForm f hf hfnc α) z := by
      set β := traceForm f hf hfnc α with hβ
      have hy_off : ∀ y ∈ g ⁻¹' {z}, y ∉ branchLocus f := by
        intro y hy hyB
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
        exact hz_gimf ⟨y, hyB, hy⟩
      have hy_gcrit : ∀ y ∈ g ⁻¹' {z}, y ∉ criticalSet g := by
        intro y hy hycrit
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
        exact hz_g ⟨y, hycrit, hy⟩
      have hgfib_fin : (g ⁻¹' {z}).Finite := fiber_finite_off_branchLocus g hg hgnc hz_g
      have hffib_fin : ∀ y ∈ g ⁻¹' {z}, (f ⁻¹' {y}).Finite :=
        fun y hy => fiber_finite_off_branchLocus f hf hfnc (hy_off y hy)
      have hpart : (g ∘ f) ⁻¹' {z} = ⋃ y ∈ g ⁻¹' {z}, f ⁻¹' {y} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply,
          Set.mem_iUnion, exists_prop]
        constructor
        · intro hx; exact ⟨f x, hx, rfl⟩
        · rintro ⟨y, hgy, hfx⟩; rw [hfx]; exact hgy
      have hdisj : (g ⁻¹' {z}).PairwiseDisjoint (fun y => f ⁻¹' {y}) := by
        intro y₁ _ y₂ _ hne
        refine Set.disjoint_left.mpr (fun x hx₁ hx₂ => ?_)
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hx₁ hx₂
        exact hne (hx₁ ▸ hx₂)
      have hinner : ∀ y ∈ g ⁻¹' {z},
          (∑ᶠ (x : X) (_ : x ∈ f ⁻¹' {y}), traceSummand (g ∘ f) α x)
            = traceSummand g β y := by
        intro y hy
        have hy_gcrit_y : y ∉ criticalSet g := hy_gcrit y hy
        have hy_off_y : y ∉ branchLocus f := hy_off y hy
        have hg_inv : (mfderiv 𝓘(ℂ) 𝓘(ℂ) g y).IsInvertible :=
          isInvertible_mfderiv_of_notMem_criticalSet g hg hgnc hy_gcrit_y
        have hsummand : ∀ x ∈ f ⁻¹' {y},
            traceSummand (g ∘ f) α x
              = (traceSummand f α x).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) g y).inverse) := by
          intro x hx
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
          have hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := hf.mdifferentiableAt (by decide)
          have hg_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (f x) := by
            rw [hx]; exact hg.mdifferentiableAt (by decide)
          have hg_inv' : (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x)).IsInvertible := by rw [hx]; exact hg_inv
          show (α.toFun x).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ f) x).inverse)
            = ((α.toFun x).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f x).inverse)).comp
                ((mfderiv 𝓘(ℂ) 𝓘(ℂ) g y).inverse)
          have hcomp_eq : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ f) x).inverse
              = (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x).inverse.comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x)).inverse) := by
            rw [mfderiv_comp x hg_diff hf_diff]
            exact ContinuousLinearMap.IsInvertible.inverse_comp_of_left hg_inv'
          apply ContinuousLinearMap.ext_ring
          rw [hcomp_eq, hx]
          rfl
        have htf : (∑ᶠ (x : X) (_ : x ∈ f ⁻¹' {y}), traceSummand f α x) = β.toFun y := by
          have h1 : traceFun f α y = β.toFun y :=
            (traceForm_toFun_of_notMem_branchLocus f hf hfnc α hy_off_y).symm
          rw [← h1]; rfl
        rw [finsum_mem_eq_finite_toFinset_sum _ (hffib_fin y hy)]
        rw [Finset.sum_congr rfl (fun x hx => hsummand x ((Set.Finite.mem_toFinset _).mp hx))]
        show (∑ x ∈ (hffib_fin y hy).toFinset,
              (traceSummand f α x).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) g y).inverse))
            = (β.toFun y).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) g y).inverse)
        rw [← htf, finsum_mem_eq_finite_toFinset_sum _ (hffib_fin y hy)]
        exact (ContinuousLinearMap.finsetSum_comp _ _).symm
      show (∑ᶠ (x : X) (_ : x ∈ (g ∘ f) ⁻¹' {z}), traceSummand (g ∘ f) α x)
          = ∑ᶠ (y : Y) (_ : y ∈ g ⁻¹' {z}), traceSummand g β y
      have hLHS : (∑ᶠ (x : X) (_ : x ∈ (g ∘ f) ⁻¹' {z}), traceSummand (g ∘ f) α x)
          = ∑ᶠ (y : Y) (_ : y ∈ g ⁻¹' {z}) (x : X) (_ : x ∈ f ⁻¹' {y}),
              traceSummand (g ∘ f) α x := by
        rw [hpart]
        exact finsum_mem_biUnion hdisj hgfib_fin hffib_fin
      rw [hLHS]
      refine finsum_mem_congr rfl (fun y hy => ?_)
      rw [hinner y hy]
    show traceLocalCoeff (L'.toFun) z₀ z = traceLocalCoeff (R'.toFun) z₀ z
    rw [traceLocalCoeff, traceLocalCoeff, hLeq, hReq, hfact]
  have hsub : t ⊆ closure (t \ B) := by
    intro z hz
    rw [mem_closure_iff_nhdsWithin_neBot]
    have htopen : IsOpen t := (chartAt ℂ z₀).open_source
    have htmem : t ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (htopen.mem_nhds hz)
    have hdiff : t \ B ∈ 𝓝[≠] z := nhdsNE_of_nhdsNE_sdiff_finite htmem hBfin.to_subtype
    have hle : 𝓝[≠] z ≤ 𝓝[t \ B] z :=
      le_inf nhdsWithin_le_nhds (le_principal_iff.mpr hdiff)
    exact Filter.neBot_of_le hle
  have heq : Set.EqOn (fun z => traceLocalCoeff (L'.toFun) z₀ z)
      (fun z => traceLocalCoeff (R'.toFun) z₀ z) t :=
    Set.EqOn.of_subset_closure hagree hcontL hcontR (Set.diff_subset) hsub
  have hcenter : traceLocalCoeff (L'.toFun) z₀ z₀ = traceLocalCoeff (R'.toFun) z₀ z₀ :=
    heq (mem_chart_source ℂ z₀)
  rw [traceLocalCoeff_center, traceLocalCoeff_center] at hcenter
  exact hcenter

/-! ## Total trace wrapper (constant-map bookkeeping)

`traceForm` requires `f` non-constant (the off-branch fibre sum is empty of content
for a constant map, whose degree is `0`). The downstream ambient layer needs a map
defined for **every** holomorphic `f`. `traceFormTotal` supplies it: it is `0` on
constant maps (degree `0`, no sheets) and the genuine `traceForm` otherwise. Its
three laws (`_eq_zero_of_const`, `_id`, `_comp`) are the exact drop-in replacements
for the old `pushforwardForm_*`; the constancy case-splits live here, once. -/

/-- **Total trace** `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)`, defined for every holomorphic `f`:
the genuine `traceForm` when `f` is non-constant, and `0` when `f` is constant
(degree `0`). This is the object the ambient coordinate layer dualizes. -/
noncomputable def traceFormTotal (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y := by
  classical
  exact if h : ∃ y₀ : Y, ∀ x, f x = y₀ then 0 else traceForm f hf h

/-- **Total trace of a constant map is zero** (degree `0`, no sheets to sum over).
Drop-in replacement for `pushforwardForm_eq_zero_of_const`. -/
theorem traceFormTotal_eq_zero_of_const (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    traceFormTotal f hf = 0 := by
  classical
  rw [traceFormTotal, dif_pos hconst]

/-- **Off-constant, the total trace is the genuine trace.** -/
theorem traceFormTotal_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    traceFormTotal f hf = traceForm f hf hnonconst := by
  classical
  rw [traceFormTotal, dif_neg hnonconst]

/-- A non-constant `f : X → Y` between compact Riemann surfaces is **surjective**
(its image is clopen in connected `Y`). Re-exported here from
`surjective_of_nonconstant` (PeriodLattice) for the composite-non-constancy argument
in `traceFormTotal_comp`. -/
private theorem surjective_of_nonconstant' (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) : Function.Surjective f :=
  surjective_of_nonconstant f hf hnonconst

/-- **`traceFormTotal id = id`** — for an infinite `X` the identity is non-constant,
so `traceFormTotal id = traceForm id`, which is the identity by `traceForm_id`. Drop-in
replacement for `pushforwardForm_id`. -/
theorem traceFormTotal_id : traceFormTotal (id : X → X) contMDiff_id =
    LinearMap.id (R := ℂ) (M := HolomorphicOneForms X) := by
  classical
  haveI : Infinite X := Jacobians.Discharge.ContMDiff.Degree.y_infinite_of_chartedSpace_complex
  have hnc : ¬ ∃ x₀ : X, ∀ x, (id : X → X) x = x₀ := by
    rintro ⟨x₀, hx₀⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    exact hab ((hx₀ a).trans (hx₀ b).symm)
  rw [traceFormTotal_of_nonconstant (id : X → X) contMDiff_id hnc, traceForm_id hnc]

/-- **Covariance `traceFormTotal (g ∘ f) = traceFormTotal g ∘ₗ traceFormTotal f`.**
Case-splits on constancy: if `f` or `g` is constant the composite is constant and
both sides collapse to `0` (composition with the zero map); otherwise `f` is
surjective, so `g ∘ f` non-constant follows from `g` non-constant, and the law is
`traceForm_comp`. Drop-in replacement for `pushforwardForm_comp`. -/
theorem traceFormTotal_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) :
    traceFormTotal (g ∘ f) hgf =
      (traceFormTotal g hg).comp (traceFormTotal f hf) := by
  classical
  by_cases hfc : ∃ y₀ : Y, ∀ x, f x = y₀
  · -- `f` constant ⟹ `g ∘ f` constant; both sides are `0`.
    obtain ⟨y₀, hy₀⟩ := hfc
    have hgfc : ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀ := ⟨g y₀, fun x => by simp [hy₀ x]⟩
    rw [traceFormTotal_eq_zero_of_const (g ∘ f) hgf hgfc,
      traceFormTotal_eq_zero_of_const f hf ⟨y₀, hy₀⟩, LinearMap.comp_zero]
  · by_cases hgc : ∃ z₀ : Z, ∀ y, g y = z₀
    · -- `g` constant ⟹ `g ∘ f` constant; both sides are `0`.
      obtain ⟨z₀, hz₀⟩ := hgc
      have hgfc : ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀ := ⟨z₀, fun x => hz₀ (f x)⟩
      rw [traceFormTotal_eq_zero_of_const (g ∘ f) hgf hgfc,
        traceFormTotal_eq_zero_of_const g hg ⟨z₀, hz₀⟩, LinearMap.zero_comp]
    · -- both non-constant: `f` surjective ⟹ `g ∘ f` non-constant; apply `traceForm_comp`.
      have hgfnc : ¬ ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀ := by
        rintro ⟨z₀, hz₀⟩
        exact hgc ⟨z₀, fun y => by
          obtain ⟨x, rfl⟩ := surjective_of_nonconstant' f hf hfc y
          exact hz₀ x⟩
      rw [traceFormTotal_of_nonconstant (g ∘ f) hgf hgfnc,
        traceFormTotal_of_nonconstant f hf hfc, traceFormTotal_of_nonconstant g hg hgc,
        traceForm_comp f hf hfc g hg hgc hgf hgfnc]

end Jacobians
