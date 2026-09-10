import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Complex.Basic

/-!
# Montel path — local representative of a holomorphic 1-form

For a holomorphic 1-form α (= smooth section of the cotangent bundle)
and a chart center `x₀`, the local representative is
`localRep α x₀ y := α.toFun y ((trivializationAt x₀).symmL ℂ y 1)`, the
value of `α` at `y` applied to the "unit tangent" at `y` transported
from the model space via the `x₀`-trivialization inverse.

This file establishes:
- `localRep` is continuous on the trivialization base set
  (which equals the chart source via `TangentBundle.trivializationAt_baseSet`).
- `localRep` is zero outside the base set (junk value of `symmL`).
- `localRep` respects the vector-space structure: add/neg/smul. -/

namespace Jacobians.Montel

open scoped Manifold ContDiff
open Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Local representative definition -/

/-- The local representative of a holomorphic 1-form α at y, using the
trivialization of the tangent bundle at x₀. In the chart around x₀,
α = `localRep α x₀ y · dz` where z is the chart coordinate. -/
noncomputable def localRep
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (y : X) : ℂ :=
  α.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Outside the trivialization's base set, `localRep α x₀` is zero (junk value
from `Trivialization.symm_apply_of_notMem`). -/
theorem localRep_eq_zero_of_notMem_baseSet
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X)
    (hy : y ∉ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) :
    localRep α x₀ y = 0 := by
  unfold localRep
  have : (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1 = 0 := by
    change (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symm y 1 = 0
    exact Trivialization.symm_apply_of_notMem _ hy 1
  rw [this]
  exact map_zero (α.toFun y)

/-! ### Continuity on the trivialization base set -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- A constant section of a vector bundle (via inverse trivialization) is
continuous on the trivialization's base set.

Proof: the section's total-space form equals `e.toOpenPartialHomeomorph.symm`
composed with `fun y => (y, v)`, which is continuous on `e.baseSet`
since `e.symm` is continuous on its source (= `baseSet × univ`). -/
theorem continuousOn_symmL_const
    (e : Trivialization ℂ (Bundle.TotalSpace.proj (E := fun x : X =>
      TangentSpace 𝓘(ℂ, ℂ) x)))
    [MemTrivializationAtlas e] (v : ℂ) :
    ContinuousOn
      (fun y : X => TotalSpace.mk' ℂ (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x)
        y (e.symmL ℂ y v))
      e.baseSet := by
  have h1 : ContinuousOn (fun p : X × ℂ => e.toOpenPartialHomeomorph.symm p)
      (e.baseSet ×ˢ Set.univ) := by
    apply e.toOpenPartialHomeomorph.continuousOn_symm.mono
    rw [← e.target_eq]
  have h2 : ContinuousOn (fun y : X => (y, v)) e.baseSet :=
    (continuousOn_id.prodMk continuousOn_const)
  have h3 : Set.MapsTo (fun y : X => (y, v)) e.baseSet (e.baseSet ×ˢ Set.univ) := by
    intro y hy
    exact ⟨hy, Set.mem_univ _⟩
  have h4 := h1.comp h2 h3
  refine h4.congr ?_
  intro y hy
  simpa using Trivialization.mk_symm e hy v

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `localRep α x₀` is continuous on the trivialization's base set. -/
theorem localRep_continuousOn
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    ContinuousOn (localRep α x₀)
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  have hα : ContinuousOn
      (fun y : X => TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        y (α.toFun y))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    α.contMDiff_toFun.continuous.continuousOn
  have hv := continuousOn_symmL_const (X := X)
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀) 1
  have hap := hα.clm_bundle_apply hv
  have hproj : Continuous
      (fun p : Bundle.TotalSpace ℂ (Bundle.Trivial X ℂ) => p.2) :=
    continuous_snd.comp (Bundle.Trivial.homeomorphProd X ℂ).continuous
  exact hproj.comp_continuousOn hap

/-! ### Behavior under vector-space operations -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `localRep` is additive: `localRep (α + β) = localRep α + localRep β`. -/
theorem localRep_add
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X) :
    localRep (α + β) x₀ y = localRep α x₀ y + localRep β x₀ y := by
  unfold localRep
  have : (α + β).toFun y = α.toFun y + β.toFun y := by
    change (⇑(α + β)) y = _
    rw [ContMDiffSection.coe_add]
    rfl
  rw [this]
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `localRep` is homogeneous: `localRep (c • α) = c • localRep α`. -/
theorem localRep_smul (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X) :
    localRep (c • α) x₀ y = c • localRep α x₀ y := by
  unfold localRep
  have : (c • α).toFun y = c • α.toFun y := by
    change (⇑(c • α)) y = _
    rw [ContMDiffSection.coe_smul]
    rfl
  rw [this]
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `localRep` on a negation: `localRep (-α) = -localRep α`. -/
theorem localRep_neg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X) :
    localRep (-α) x₀ y = -localRep α x₀ y := by
  unfold localRep
  have : (-α).toFun y = -α.toFun y := by
    change (⇑(-α)) y = _
    rw [ContMDiffSection.coe_neg]
    rfl
  rw [this]
  rfl

end Jacobians.Montel
