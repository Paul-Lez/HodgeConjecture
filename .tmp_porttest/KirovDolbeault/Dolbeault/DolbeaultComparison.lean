/-
  Dolbeault cohomology `H^{0,1}(X)` and the Čech↔Dolbeault comparison — the **L3 kernel** of the
  `D = 0` Serre duality (`arithmeticGenus_eq_genus`).

  Built on the proven intrinsic Dolbeault data:
  * `RealForms`: `A⁰ = SmoothCFunctions X`, `A¹ = SmoothCOneForms X` (a `ContMDiffSection`, an
    `ℝ`-module), `differential : A⁰ → A¹` (`du`), `proj01 : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ)` (the
    `(0,1)`-fiber projection, a CLM), `dbar u = proj01 ∘ du` (`∂̄`).
  * `DolbeaultH01` (the *atom* file): `dbarL : A⁰ →ₗ[ℝ] A¹`, the `ℝ`-linear `∂̄`.

  This file assembles, by pure algebra (deliverables 1–4, complete):
  * `proj01L : A¹ →ₗ[ℝ] A¹` — `proj01` applied fiberwise (an `ℝ`-linear endomorphism of `A¹`);
  * `OneFormsZeroOne X := LinearMap.range proj01L` — the `(0,1)`-forms `A^{0,1}` (a `Submodule ℝ A¹`);
  * `dbarL_mem_zeroOne` : `im ∂̄ ⊆ A^{0,1}` (since `∂̄ = proj01L ∘ d`);
  * `DolbeaultH01 X` := the cokernel `A^{0,1} ⧸ im ∂̄` (on a curve `A^{0,2} = 0`, so this *is*
    `H^{0,1}`); an `ℝ`-module.

  Deliverable 5 — the comparison statement itself (`finrank ℝ (DolbeaultH01 X) =
  2 · finrank ℂ (cechH1 𝔘 0)`, see the SCALAR NOTE at the end of this file for the `2·` factor) — is
  PROVEN downstream: `cechH1_dolbeault_comparison_proof` (`DolbeaultComparisonEquiv.lean`, via the
  explicit `ℝ`-linear equivalence) and the `IsLeray`-free `GoodCover.cechH1_dolbeault_comparison'`.
-/
import KirovDolbeault.Dolbeault.DolbeaultH01
import KirovDolbeault.Dolbeault.CechComplex

open scoped Manifold ContDiff Bundle

-- Same permissive transparency as `RealForms`/`DolbeaultH01`: without it the `ContMDiffSection`
-- `ext`/`coe` lemmas fail to synthesise the hom-bundle `TopologicalSpace` (the ℂ-ℝ-module diamond).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Deliverable 1: `proj01` applied fiberwise as an `ℝ`-linear endomorphism of `A¹`.

The smoothness of `x ↦ proj01 (α x)` is the same mechanism `RealForms.dbar` uses: `proj01` is a
fixed CLM that slides through the tangent `symmL` because `mulI` commutes with `tangentCoordChange`.
`RealForms` proves that commutation as the `private` lemma `tangentCoordChange_comp_mulI`, not
visible here, so we re-establish it locally (pure, from public Mathlib lemmas) and adapt the proof to
an arbitrary smooth section `α` (where `dbar` had the concrete `differential u`). -/

/-- A real-restricted `ℂ`-linear map commutes with `mulI = (·*i)`. -/
private theorem restrictScalars_comp_mulI (L : ℂ →L[ℂ] ℂ) :
    (L.restrictScalars ℝ).comp mulI = mulI.comp (L.restrictScalars ℝ) := by
  ext v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, mulI,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.coe_restrictScalars']
  rw [← smul_eq_mul Complex.I v, map_smul, smul_eq_mul]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The tangent `coordChange` of the complex manifold is `ℂ`-linear, hence commutes with `mulI`. -/
private theorem tangentCoordChange_comp_mulI {a b z : X}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) a).source ∩ (extChartAt 𝓘(ℝ, ℂ) b).source) :
    (tangentCoordChange 𝓘(ℝ, ℂ) a b z).comp mulI = mulI.comp (tangentCoordChange 𝓘(ℝ, ℂ) a b z) := by
  have hℝ := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, ℂ)) (x := a) (y := b) (z := z) hz
  have hmem : extChartAt 𝓘(ℝ, ℂ) a z ∈
      ((extChartAt 𝓘(ℝ, ℂ) a).symm ≫ extChartAt 𝓘(ℝ, ℂ) b).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact Set.mem_image_of_mem _ hz
  have hℂ : DifferentiableWithinAt ℂ (extChartAt 𝓘(ℝ, ℂ) b ∘ (extChartAt 𝓘(ℝ, ℂ) a).symm)
      (Set.range 𝓘(ℝ, ℂ)) (extChartAt 𝓘(ℝ, ℂ) a z) :=
    (contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ω) b a hmem).differentiableWithinAt
      (by simp)
  have huniq : UniqueDiffWithinAt ℝ (Set.range 𝓘(ℝ, ℂ)) (extChartAt 𝓘(ℝ, ℂ) a z) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact uniqueDiffWithinAt_univ
  have heq : tangentCoordChange 𝓘(ℝ, ℂ) a b z =
      (fderivWithin ℂ (extChartAt 𝓘(ℝ, ℂ) b ∘ (extChartAt 𝓘(ℝ, ℂ) a).symm)
        (Set.range 𝓘(ℝ, ℂ)) (extChartAt 𝓘(ℝ, ℂ) a z)).restrictScalars ℝ :=
    huniq.eq hℝ (hℂ.hasFDerivWithinAt.restrictScalars ℝ)
  rw [heq, restrictScalars_comp_mulI]

/-- `x ↦ proj01 (α x)` is a smooth section whenever `α` is. This is exactly the smoothness mechanism
of `RealForms.dbar` (`proj01` is a fixed CLM and slides through the tangent `symmL` because `mulI`
commutes with `tangentCoordChange`), with the concrete section `differential u` replaced by an
arbitrary smooth section `α`. -/
theorem contMDiff_proj01_section (α : SmoothCOneForms X) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, proj01 (α x)⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  simp only [ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp]
  have h := α.contMDiff_toFun x₀
  rw [contMDiffAt_hom_bundle] at h
  simp only [ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp] at h
  have heq : (fun x => (proj01 (α x)).comp
        (Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x))
      =ᶠ[nhds x₀] (fun x => proj01 ((α x).comp
        (Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x))) := by
    filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀)] with x hx
    have hS : mulI.comp
          (Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x)
        = (Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x).comp
            mulI := by
      rw [TangentBundle.symmL_trivializationAt_eq_core hx]
      exact (tangentCoordChange_comp_mulI ⟨by rw [extChartAt_source]; exact hx,
        by rw [extChartAt_source]; exact mem_chart_source ℂ x⟩).symm
    rw [proj01_apply, proj01_apply]
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_assoc, hS]
  exact (ContMDiffAt.clm_apply contMDiffAt_const h.2).congr_of_eventuallyEq heq

/-- `proj01` applied fiberwise to a smooth `1`-form, packaged as a smooth `1`-form. -/
noncomputable def proj01Section (α : SmoothCOneForms X) : SmoothCOneForms X where
  toFun := fun x => proj01 (α x)
  contMDiff_toFun := contMDiff_proj01_section α

@[simp] theorem proj01Section_apply (α : SmoothCOneForms X) (x : X) :
    (proj01Section α) x = proj01 (α x) := rfl

/-- **`proj01` as an `ℝ`-linear endomorphism of `A¹`** (deliverable 1): the `(0,1)`-fiber projection
applied fiberwise. `map_add'`/`map_smul'` mirror `dbar_add`/`dbar_smul` — `proj01` is `ℝ`-linear on
each fiber. -/
noncomputable def proj01L : SmoothCOneForms X →ₗ[ℝ] SmoothCOneForms X where
  toFun := proj01Section
  map_add' α β := by
    refine ContMDiffSection.ext fun x => ?_
    simp only [proj01Section_apply, ContMDiffSection.coe_add, Pi.add_apply, proj01.map_add]
  map_smul' c α := by
    refine ContMDiffSection.ext fun x => ?_
    simp only [proj01Section_apply, ContMDiffSection.coe_smul, Pi.smul_apply, proj01.map_smul,
      RingHom.id_apply]

@[simp] theorem proj01L_apply (α : SmoothCOneForms X) : proj01L α = proj01Section α := rfl

/-! ### Deliverable 2: the `(0,1)`-forms `A^{0,1}` as a submodule of `A¹`. -/

/-- **The `(0,1)`-forms** `A^{0,1} X` (deliverable 2): the image of the `(0,1)`-projection `proj01L`.
A `Submodule ℝ` of `A¹ = SmoothCOneForms X`. (`proj01` is an idempotent picking out the
conjugate-`ℂ`-linear part of each fiber, so its range is exactly the `(0,1)`-forms.) -/
noncomputable def OneFormsZeroOne (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Submodule ℝ (SmoothCOneForms X) :=
  LinearMap.range (proj01L (X := X))

/-! ### Deliverable 3: `∂̄` lands in `A^{0,1}`. -/

/-- `∂̄u = proj01L (du)` as `1`-forms: both have fiber `x ↦ proj01 ((differential u) x)`. -/
theorem dbarL_eq_proj01L_differential (u : SmoothCFunctions X) :
    dbarL u = proj01L (differential u) := by
  refine ContMDiffSection.ext fun x => ?_
  rfl

/-- **`im ∂̄ ⊆ A^{0,1}`** (deliverable 3): `∂̄u` is a `(0,1)`-form, since `∂̄u = proj01L (du)` lies in
the range of `proj01L`. This is what makes `LinearMap.range dbarL` a submodule of `OneFormsZeroOne`,
hence the cokernel `DolbeaultH01` below well-formed. -/
theorem dbarL_mem_zeroOne (u : SmoothCFunctions X) : dbarL u ∈ OneFormsZeroOne X := by
  rw [dbarL_eq_proj01L_differential]
  exact LinearMap.mem_range_self _ _

/-- The image of `∂̄` is contained in `A^{0,1}` (the submodule form of `dbarL_mem_zeroOne`). -/
theorem range_dbarL_le_zeroOne :
    LinearMap.range (dbarL (X := X)) ≤ OneFormsZeroOne X := by
  rintro _ ⟨u, rfl⟩
  exact dbarL_mem_zeroOne u

/-! ### Deliverable 4: Dolbeault cohomology `H^{0,1}(X)` as the `∂̄`-cokernel on `A^{0,1}`. -/

/-- `im ∂̄` viewed inside `A^{0,1}` (legitimate as a submodule of `↥(OneFormsZeroOne X)` precisely by
`range_dbarL_le_zeroOne` / `dbarL_mem_zeroOne`). -/
noncomputable def dbarImageInZeroOne (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Submodule ℝ ↥(OneFormsZeroOne X) :=
  (LinearMap.range (dbarL (X := X))).submoduleOf (OneFormsZeroOne X)

/-- **Dolbeault cohomology `H^{0,1}(X)`** (deliverable 4): the cokernel of `∂̄` on the `(0,1)`-forms,
`A^{0,1} ⧸ im ∂̄`. On a (compact) Riemann surface `A^{0,2} = 0`, so the Dolbeault complex
`A⁰ →[∂̄] A^{0,1} → 0` has this single nontrivial cohomology and `H^{0,1}` *is* this cokernel.
An `ℝ`-module (the section space `A¹` carries only `Module ℝ`; the hom-bundle fiber `ℂ →L[ℝ] ℂ` is
not propagated to a `Module ℂ` on the sections — see the comparison's scalar note). -/
abbrev DolbeaultH01 (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ↥(OneFormsZeroOne X) ⧸ dbarImageInZeroOne X

-- `H^{0,1}` is a genuine real vector space (validates the representation).
noncomputable example : AddCommGroup (DolbeaultH01 X) := inferInstance
noncomputable example : Module ℝ (DolbeaultH01 X) := inferInstance

/-! ### Deliverable 5: the L3 kernel — Čech ↔ Dolbeault comparison.

This is the genuine analytic content of the `D = 0` Serre nugget (`H¹(X,𝒪) ≅ H^{0,1} ≅ Ω(X)^*`,
cf. `DolbeaultLadder.arithmeticGenus_eq_genus`). The proof is the ∂̄-globalization / Čech patching
argument — locally `∂̄`-solve a Čech `𝒪`-cocycle (`DbarLocal.dbar_solvable_locally`), glue with a
partition of unity, and the `∂̄` of the glued primitive is a global `(0,1)`-form whose class is the
image; conversely a global `(0,1)`-form is locally `∂̄`-exact and the local primitives' differences
are a holomorphic Čech cocycle. PDE-free given local solvability. PROVEN downstream
(`cechH1_dolbeault_comparison_proof`, `DolbeaultComparisonEquiv.lean`; `IsLeray`-free form
`GoodCover.cechH1_dolbeault_comparison'`).

**SCALAR NOTE (the ℂ-vs-ℝ question, resolved).** `cechH1 𝔘 0 = H¹(X, 𝒪)` is a `Module ℂ`; on a
compact Riemann surface of kirovGenus `g` it has `finrank ℂ = g`. `DolbeaultH01 X` is, *as built here*,
only a `Module ℝ`: the hom-bundle fiber `ℂ →L[ℝ] ℂ` is `Module ℂ` (via its codomain), but that
ℂ-action is **not** propagated to the `ContMDiffSection` space `A¹` (Mathlib synthesises neither
`SMul ℂ (SmoothCOneForms X)` nor `Module ℂ`), so the quotient inherits only `Module ℝ`. The honest
underlying spaces:
* `A^{0,1}` *is* genuinely a complex vector space (scale a `(0,1)`-form by `c ∈ ℂ` pointwise via the
  codomain — it stays `(0,1)`), and `H^{0,1}` has `finrank ℂ = g` (Dolbeault `≅ H¹(𝒪)`). Hence its
  **real** dimension is `2g`.
* Therefore the *naïve* "respective-scalars" equality `finrank ℂ (cechH1 𝔘 0) = finrank ℝ
  (DolbeaultH01 X)` would read `g = 2g` and is **FALSE** — we deliberately do NOT state that.

The correctly-typed, scalar-honest equality (the form proven downstream) is
`finrank ℝ (DolbeaultH01 X) = 2 * finrank ℂ (cechH1 𝔘 0)` (both sides `= 2g`). The cleaner
`finrank ℂ`-equality / `≃ₗ[ℂ]` requires first equipping `DolbeaultH01 X` with its natural `Module ℂ`
(the pointwise codomain action) — itself part of the L3 build — and is recorded as a comment for the
downstream `arithmeticGenus_eq_genus` consumer, which only needs `finrank ℂ (cechH1 𝔘 0) = g`. -/

end Jacobians.Dolbeault
