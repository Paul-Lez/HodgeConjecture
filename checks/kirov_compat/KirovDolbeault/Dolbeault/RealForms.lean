/-
  Dolbeault ladder — smooth ℂ-valued 1-forms over the real-manifold structure (the INTRINSIC route).

  On top of `RealManifold` (the real-`C^∞` structure of the complex manifold), this is the intrinsic
  real cotangent valued in `ℂ`: smooth sections of `TangentSpace 𝓘(ℝ,ℂ) →L[ℝ] ℂ`. This is the
  textbook-standard container for the Dolbeault complex `A¹ = A^{1,0} ⊕ A^{0,1}` (`∂̄u` lands in the
  `(0,1)` part) — no chart-local cocycle bespoke machinery.

  Mathlib's hom-of-bundles machinery is generic over the scalar field, so the only obstructions are
  the same ℂ-as-ℝ-module diamond as in `RealManifold` (handled with the same
  `set_option backward.isDefEq.respectTransparency false`, as Mathlib's own `Complex/RealDeriv.lean`),
  plus the single instance the hom-bundle needs but doesn't auto-derive for the *sub*-field ℝ:
  `ContinuousSMul ℝ (Trivial X ℂ)` (the trivial fiber `Trivial X ℂ x` is defeq `ℂ`).
-/
import KirovDolbeault.Dolbeault.RealManifold
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

open scoped Manifold ContDiff Bundle

set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Real-smooth `ℂ`-valued functions** `A⁰` on `X` — the source of `∂̄`: real-`C^∞` maps `X → ℂ`
(over the real model, i.e. NOT holomorphic). A real vector space. -/
abbrev SmoothCFunctions (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffMap (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) X ℂ (⊤ : ℕ∞)

noncomputable example : AddCommGroup (SmoothCFunctions X) := inferInstance

/-- The trivial `ℂ`-bundle is a continuous `ℝ`-module — the one instance Mathlib's hom-of-bundles
machinery needs but does not auto-derive for the sub-field `ℝ` (`Trivial X ℂ x` is defeq `ℂ`, and the
ℂ-`ℝ`-module diamond is resolved by the file `set_option`). -/
instance trivial_continuousSMul_real (x : X) : ContinuousSMul ℝ (Bundle.Trivial X ℂ x) :=
  inferInstanceAs (ContinuousSMul ℝ ℂ)

/-- **Smooth `ℂ`-valued 1-forms** on `X`: smooth sections of the real cotangent valued in `ℂ`
(real-linear maps `TangentSpace 𝓘(ℝ,ℂ) x → ℂ`). The intrinsic container for the Dolbeault complex
`A¹ = A^{1,0} ⊕ A^{0,1}`. A real (`Module ℝ`) vector space. -/
abbrev SmoothCOneForms (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffSection (𝓘(ℝ, ℂ)) (ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
    (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)

-- The intrinsic 1-form space is a genuine real vector space (validates the representation).
noncomputable example : AddCommGroup (SmoothCOneForms X) := inferInstance
noncomputable example : Module ℝ (SmoothCOneForms X) := inferInstance

/-- The **de Rham differential** `d : A⁰ → A¹` — the real differential `du = mfderiv u` of a smooth
`ℂ`-valued function, a smooth `ℂ`-valued 1-form. (`∂̄u` is its `(0,1)`-part; `∂u` the `(1,0)`-part.)
The section-smoothness is the standard "the differential of a `C^∞` function is a `C^∞` 1-form"
(`mfderiv_const` in tangent coordinates, bridged to the trivial-bundle codomain `ℂ`). -/
noncomputable def differential (u : SmoothCFunctions X) : SmoothCOneForms X where
  toFun := fun x => mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) u x
  contMDiff_toFun := by
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have h := (u.contMDiff x₀).mfderiv_const (m := (⊤ : ℕ∞)) (by simp)
    convert h using 3 with x
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      Bundle.Trivial.fiberBundle_trivializationAt',
      TangentBundle.continuousLinearMapAt_trivializationAt, ContinuousLinearMap.id_comp, mfld_simps]

/-- Multiplication by `i` as a real-linear endomorphism of `ℂ` (`= J`, the complex structure on the
real tangent space `T_x ≅ ℂ`). -/
noncomputable def mulI : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) Complex.I

/-- The **`(0,1)`-projection** on real-linear forms `ℂ →L[ℝ] ℂ`: `P(α) = ½(α + i·α(i·−))`, the
conjugate-`ℂ`-linear (Cauchy–Riemann) part. A fixed continuous-linear fiber endomorphism; applied
fiberwise to `du` it carves `∂̄u` out of the de Rham differential. -/
noncomputable def proj01 : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (2 : ℝ)⁻¹ • (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ) +
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ mulI).comp ((ContinuousLinearMap.compL ℝ ℂ ℂ ℂ).flip mulI))

/-- `proj01` written out: `P(α) = ½(α + i·α(i·−))`. -/
theorem proj01_apply (α : ℂ →L[ℝ] ℂ) :
    proj01 α = (2 : ℝ)⁻¹ • (α + mulI.comp (α.comp mulI)) := rfl

/-! ### The complex structure `J` on the real tangent bundle is smooth

The one genuinely complex-geometric input to `∂̄`: `mulI = J = (·*i)` is a `C^∞` section of the real
tangent bundle's endomorphisms. The mechanism is that the tangent `coordChange` of a *complex*
manifold is `ℂ`-linear — holomorphic charts have `ℂ`-linear `fderiv` (`fderiv ℝ = restrictScalars`
of `fderiv ℂ`) — hence commutes with `mulI`; together with the cocycle this forces `J` in coordinates
(`Jcoord = inCoordinates mulI`) to be the *constant* `mulI`, which is trivially smooth. -/

/-- A real-restricted `ℂ`-linear map commutes with `mulI = (·*i)` (the `ℂ`-`(i·)` action). -/
private theorem restrictScalars_comp_mulI (L : ℂ →L[ℂ] ℂ) :
    (L.restrictScalars ℝ).comp mulI = mulI.comp (L.restrictScalars ℝ) := by
  ext v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, mulI,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.coe_restrictScalars']
  rw [← smul_eq_mul Complex.I v, map_smul, smul_eq_mul]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The tangent `coordChange` of the complex manifold is `ℂ`-linear, hence commutes with `mulI`:
`fderiv ℝ` of a holomorphic transition is `restrictScalars` of `fderiv ℂ`. -/
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

/-- The **Dolbeault `∂̄` operator** `A⁰ → A^{0,1} ⊆ A¹`: the `(0,1)`-part of the de Rham differential,
`∂̄u = proj01 ∘ du`. A smooth `ℂ`-valued 1-form. -/
noncomputable def dbar (u : SmoothCFunctions X) : SmoothCOneForms X where
  toFun := fun x => proj01 ((differential u).toFun x)
  contMDiff_toFun := by
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    simp only [ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp]
    -- After trivialising the (trivial) `ℂ`-codomain the obligation is `x ↦ (proj01 (du x)).comp (Sₓ)`,
    -- where `Sₓ := (trivializationAt ℂ (TangentSpace 𝓘(ℝ,ℂ)) x₀).symmL ℝ x` is the tangent symmL.
    -- `Sₓ` IS a `tangentCoordChange`, so it commutes with `mulI`; hence `proj01` slides through the
    -- `.comp Sₓ`, turning the goal into `proj01 ∘ A` with `A x := (du x).comp Sₓ` = `differential`'s
    -- own (proven) reduced smoothness.  `proj01` is a fixed CLM, so `proj01 ∘ A` is `C^∞`.
    have h := (differential u).contMDiff_toFun x₀
    rw [contMDiffAt_hom_bundle] at h
    simp only [ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp] at h
    have heq : (fun x => (proj01 ((differential u).toFun x)).comp
          (Bundle.Trivialization.symmL ℝ (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) x₀) x))
        =ᶠ[nhds x₀] (fun x => proj01 (((differential u).toFun x).comp
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

end Jacobians.Dolbeault
