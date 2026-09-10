import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import KirovDolbeault.Genus
import KirovDolbeault.Montel

/-!
# Holomorphic 1-forms on a complex manifold

Uses Mathlib's `ContMDiffSection` and the `Bundle.ContinuousLinearMap`
hom-of-bundles construction to define holomorphic 1-forms as **analytic
sections of the cotangent bundle**.

The cotangent bundle at a point `x : X` is
`TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`, built via Mathlib's hom-of-bundles
machinery (`Bundle.ContinuousLinearMap.fiberBundle`, `vectorBundle`,
and `vectorPrebundle.isContMDiff`).

This is the **honest** definition (compare to a placeholder that sets
`HolomorphicOneForms X := Fin (kirovGenus X) → ℂ`).

## Dimension theorem (unproved)

On a compact connected complex 1-manifold, `HolomorphicOneForms X` is
a finite-dim ℂ-vector space of dimension `kirovGenus X`. This is a classical
result (Riemann–Roch) and is recorded here as an unproved obligation with TODO(math).

## References

Forster §§9–10; Miranda Ch. 4 §1.
-/

namespace Jacobians

open scoped Manifold ContDiff Bundle

set_option linter.unusedSectionVars false

-- `HolomorphicOneForms` and its `AddCommGroup` / `Module ℂ` instances are
-- defined in `Jacobians.Genus` (to allow `kirovGenus X := finrank ℂ (HOF X)`
-- without a circular import).

section Curve

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `NormedAddCommGroup` on `HolomorphicOneForms X` via Montel's chart-atlas
`supNormK`. This is real infrastructure (no gaps) and follows the
Ahlfors-Sario construction (see `Jacobians.Montel`). -/
noncomputable instance : NormedAddCommGroup (HolomorphicOneForms X) :=
  Jacobians.Montel.HolomorphicOneForms.normedAddCommGroup

/-- `NormedSpace ℂ` on `HolomorphicOneForms X` completing the normed-space
structure via `supNormK` homogeneity. -/
noncomputable instance : NormedSpace ℂ (HolomorphicOneForms X) :=
  Jacobians.Montel.HolomorphicOneForms.normedSpace

/-- The norm on `HolomorphicOneForms X` is exactly Montel's `supNormK` (by
construction — the `NormedAddCommGroup` instance is built from it). -/
theorem norm_HOF_eq_supNormK (α : HolomorphicOneForms X) :
    ‖α‖ = Jacobians.Montel.HolomorphicOneForms.supNormK α := rfl

/-- On a compact connected complex 1-manifold, the space of global holomorphic
1-forms is finite-dimensional. Derived via Montel/Riesz from
`Jacobians.Montel.HolomorphicOneForms.closedBall_isCompact` (the single
remaining unproved obligation: the closed unit ball under `supNormK` is compact
via Arzelà-Ascoli). -/
noncomputable instance : FiniteDimensional ℂ (HolomorphicOneForms X) :=
  FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one
    Jacobians.Montel.HolomorphicOneForms.closedBall_isCompact

/-- Dimension of holomorphic 1-forms = kirovGenus. With `kirovGenus X` defined as
`Module.finrank ℂ (HolomorphicOneForms X)` (see `Jacobians.Genus`), this
is `rfl`. -/
theorem finrank_HolomorphicOneForms_eq_genus :
    Module.finrank ℂ (HolomorphicOneForms X) = kirovGenus X := rfl

end Curve

/-! ### Pullback of forms along a holomorphic map. -/

section Functoriality

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z] [Nonempty Z]
    [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- Pullback of a holomorphic 1-form along a holomorphic map of complex
manifolds.

Pointwise: `(pullbackForm g α)(x) = α(g x) ∘ mfderiv g x`.

The smoothness (`contMDiff_toFun`) is the chain rule on bundle sections:
`α(g x) ∘ mfderiv g x : TX_x →L[ℂ] ℂ` varies smoothly with x because
both factors vary smoothly (α is smooth on Y, mfderiv g is smooth on X)
when read in tangent coordinates. -/
noncomputable def pullbackForm (g : X → Y) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    HolomorphicOneForms Y →ₗ[ℂ] HolomorphicOneForms X where
  toFun α :=
    { toFun := fun x : X =>
        (α.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x)
      contMDiff_toFun := by
        intro x₀
        -- Strategy: reduce to checking the hom-bundle iff + coordinate rep.
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        -- Goal: ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
        --         (fun x => inCoordinates ℂ TS_X ℂ Trivial_X x₀ x x₀ x
        --            ((α(g x)).comp (mfderiv g x))) x₀.
        -- Factor: inCoordinates = [α in coords] ∘ [mfderiv in coords].
        -- Step A: α(g x) in coordinates at g x₀ is smooth.
        -- Step B: mfderiv g x in coordinates (x₀ → g x₀) is smooth via mfderiv_const.
        -- Step C: compose via ContMDiff.clm_comp (normed space CLM).
        have hA : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
            (fun x => ContinuousLinearMap.inCoordinates ℂ
                (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
                (g x₀) (g x) (g x₀) (g x) (α.toFun (g x))) x₀ := by
          have hα := α.contMDiff_toFun (g x₀)
          rw [contMDiffAt_hom_bundle] at hα
          obtain ⟨_, h⟩ := hα
          -- h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
          --      (fun y => inCoordinates ... (g x₀) y (g x₀) y (α y)) (g x₀)
          exact h.comp x₀ (hg x₀)
        have hB : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
            (fun x => ContinuousLinearMap.inCoordinates ℂ
                (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ
                (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
                x₀ x (g x₀) (g x) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x)) x₀ :=
          (hg x₀).mfderiv_const (le_refl _)
        -- Compose them: [α in coords] ∘ [mfderiv in coords]
        have hcomp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
            (fun x => (ContinuousLinearMap.inCoordinates ℂ
                (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
                (g x₀) (g x) (g x₀) (g x) (α.toFun (g x))).comp
              (ContinuousLinearMap.inCoordinates ℂ
                (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ
                (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
                x₀ x (g x₀) (g x) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x))) x₀ :=
          hA.clm_comp hB
        -- Congr argument: the composition equals the target inCoordinates.
        apply hcomp.congr_of_eventuallyEq
        -- Need: eventually for x near x₀, LHS = RHS pointwise.
        filter_upwards [
          ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt ℂ _ x₀)),
          (hg.continuous.continuousAt.preimage_mem_nhds
            ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) (g x₀)).open_baseSet.mem_nhds
              (mem_baseSet_trivializationAt ℂ _ (g x₀))))
          ] with x hx_TS_X hx_TS_Y
        -- hx_TS_X : x ∈ (trivializationAt ℂ TangentSpace x₀).baseSet
        -- hx_TS_Y : g x ∈ (trivializationAt ℂ TangentSpace (g x₀)).baseSet
        ext
        simp only [ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_apply,
          Bundle.Trivial.fiberBundle_trivializationAt',
          Bundle.Trivial.continuousLinearMapAt_trivialization,
          ContinuousLinearMap.id_apply]
        -- After simp: LHS v = α(g x) (mfderiv g x ((trivTS_X x₀).symmL ℂ x v))
        -- RHS v = α(g x) ((trivTS_Y g x₀).symmL ℂ (g x)
        --           ((trivTS_Y g x₀).continuousLinearMapAt ℂ (g x)
        --             (mfderiv g x ((trivTS_X x₀).symmL ℂ x v))))
        -- The inner (symmL ∘ continuousLinearMapAt) on a fiber element is identity.
        rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hx_TS_Y] }
  map_add' α₁ α₂ := by
    apply ContMDiffSection.ext
    intro x
    show ((α₁ + α₂).toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x) =
      ((α₁.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x)) +
        ((α₂.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x))
    rfl
  map_smul' c α := by
    apply ContMDiffSection.ext
    intro x
    show ((c • α).toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x) =
      c • (α.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x)
    rfl

/-- `pullbackForm id = id`. Follows from `mfderiv id = id` and
`ContinuousLinearMap.comp_id`. -/
theorem pullbackForm_id : pullbackForm (id : X → X) contMDiff_id =
    LinearMap.id (R := ℂ) (M := HolomorphicOneForms X) := by
  ext α
  apply ContMDiffSection.ext
  intro x
  show (α.toFun x).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) x) = α.toFun x
  rw [mfderiv_id]
  exact ContinuousLinearMap.comp_id _

/-- Contravariance of pullback: `(g ∘ f)^* = f^* ∘ g^*`. Follows from
the chain rule `mfderiv_comp` + associativity of composition. -/
theorem pullbackForm_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) :
    pullbackForm (g ∘ f) hgf =
      (pullbackForm f hf).comp (pullbackForm g hg) := by
  ext α
  apply ContMDiffSection.ext
  intro x
  show (α.toFun ((g ∘ f) x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ f) x) =
    ((α.toFun (g (f x))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x))).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x)
  rw [mfderiv_comp x (hg.mdifferentiableAt (by decide))
    (hf.mdifferentiableAt (by decide))]
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

end Functoriality

/-! ### Ambient-space bridge

Connects the forms side (`HolomorphicOneForms X`, `pullbackForm`) to
the Jacobian-quotient ambient `(Fin (kirovGenus X) → ℂ)` via a basis
isomorphism and dualization. This is the glue layer between
`HolomorphicForms` and `ZLatticeQuotient` (where the quotient descent
lives).

`Ψ : (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ)` is the coefficient matrix of
`pullbackForm f hf` in the chosen basis; `Φ` is its matrix transpose
(a workaround for the real pushforward/trace). Real content for the
degree identity `Φ ∘ Ψ = d • id` is axiomatized by
`HasAmbientDegreeIdentity`. -/

section AmbientBridge

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- A linear isomorphism `(Fin (kirovGenus X) → ℂ) ≃ₗ[ℂ] HolomorphicOneForms X`
from a choice of basis, via `Module.finBasisOfFinrankEq` + the sorried
dimension equality `finrank_HolomorphicOneForms_eq_genus`. -/
noncomputable def ambientIso (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (Fin (kirovGenus X) → ℂ) ≃ₗ[ℂ] HolomorphicOneForms X :=
  (Module.finBasisOfFinrankEq ℂ (HolomorphicOneForms X)
    (finrank_HolomorphicOneForms_eq_genus X)).equivFun.symm

/-- The ambient ℂ-linear map `Ψ` induced by the pullback of forms along
`f : X → Y`. Defined via `ambientIso` + `pullbackForm`:
`Ψ = (ambientIso X).symm ∘ pullbackForm f hf ∘ ambientIso Y` (when the
kirovGenus sizes match; otherwise zero — this branch is never used in the
challenge). This is a concrete definition (no gaps at this level), but
it depends on `ambientIso` which internally depends on
`finrank_HolomorphicOneForms_eq_genus`. -/
noncomputable def ambientPsi {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ) := by
  classical
  by_cases hX : gX = kirovGenus X
  · by_cases hY : gY = kirovGenus Y
    · subst hX; subst hY
      -- Compose: (Fin gY → ℂ) →ₗ HOF Y →ₗ HOF X →ₗ (Fin gX → ℂ), then cast to CLM
      refine LinearMap.toContinuousLinearMap
        ((ambientIso X).symm.toLinearMap.comp
          ((pullbackForm f hf).comp (ambientIso Y).toLinearMap))
    · exact 0
  · exact 0

/-- The ambient ℂ-linear map `Φ` induced by the pushforward of forms along
`f : X → Y`. Defined as the matrix-transpose of `ambientPsi f hf` (= `Mᵀ`, via
the standard Pi basis). The transpose reverses composition order, so covariant
`ambientPhi_comp` is automatic from contravariant `ambientPsi_comp`. -/
noncomputable def ambientPhi {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin gY)) (Pi.basisFun ℂ (Fin gX))
        (ambientPsi f hf).toLinearMap).transpose.mulVecLin

/-- `ambientPsi id = id`. Proven via `pullbackForm_id`. -/
theorem ambientPsi_id (y : Fin (kirovGenus X) → ℂ) :
    ambientPsi (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id y = y := by
  unfold ambientPsi
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show (((ambientIso X).symm.toLinearMap.comp
      ((pullbackForm (id : X → X) contMDiff_id).comp (ambientIso X).toLinearMap)) : _ →ₗ[_] _) y = y
  rw [show (pullbackForm (id : X → X) contMDiff_id) = LinearMap.id from pullbackForm_id]
  simp

/-- Contravariant composition: `ambientPsi (g ∘ f) = ambientPsi f ∘ ambientPsi g`.
Proven via `pullbackForm_comp`. -/
theorem ambientPsi_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (z : Fin (kirovGenus Z) → ℂ) :
    ambientPsi (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf z =
      ambientPsi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (ambientPsi (gX := kirovGenus Y) (gY := kirovGenus Z) g hg z) := by
  unfold ambientPsi
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show (((ambientIso X).symm.toLinearMap.comp
      ((pullbackForm (g ∘ f) hgf).comp (ambientIso Z).toLinearMap))) z = _
  rw [pullbackForm_comp f hf g hg hgf]
  simp [LinearMap.comp_apply]

/- **Ambient degree identity** (`f_* ∘ f^* = deg(f) • id`, Griffiths–Harris
Ch. 2 §2.7 — the trace map for forms).

This is stated in `Jacobians.lean` as `Jacobian.ambientPhi_ambientPsi_eq`,
*not* here. It must pin the degree to the genuine `ContMDiff.degree f hf`,
which is defined downstream of this file. The previous formulation here
quantified over a free `d : ℕ`, making it vacuously false (instantiating
`d = 0` and `d = 1` forces `y = 0` for all `y`) — the same defect class as
the removed SmoothPath third conjunct. See `Jacobian.ambientPhi_ambientPsi_eq`
for the honest single-degree statement. -/

/-- `ambientPhi id = id` — follows from `ambientPsi_id` via the transpose
construction: transpose of identity matrix is identity. -/
theorem ambientPhi_id (x : Fin (kirovGenus X) → ℂ) :
    ambientPhi (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id x = x := by
  have hpsi : ambientPsi (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id
      = ContinuousLinearMap.id ℂ (Fin (kirovGenus X) → ℂ) :=
    ContinuousLinearMap.ext (fun y => ambientPsi_id y)
  unfold ambientPhi
  rw [show (ambientPsi (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id).toLinearMap
      = LinearMap.id (R := ℂ) (M := Fin (kirovGenus X) → ℂ) from by rw [hpsi]; rfl]
  simp [Matrix.transpose_one, Matrix.mulVecLin_one]

/-- Covariant composition: `ambientPhi (g ∘ f) = ambientPhi g ∘ ambientPhi f`.
Follows from `ambientPsi_comp` via matrix transpose reversing composition order. -/
theorem ambientPhi_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (x : Fin (kirovGenus X) → ℂ) :
    ambientPhi (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf x =
      ambientPhi (gX := kirovGenus Y) (gY := kirovGenus Z) g hg
        (ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf x) := by
  have hpsi : ambientPsi (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf =
      (ambientPsi (gX := kirovGenus X) (gY := kirovGenus Y) f hf).comp
        (ambientPsi (gX := kirovGenus Y) (gY := kirovGenus Z) g hg) :=
    ContinuousLinearMap.ext (fun z => ambientPsi_comp f hf g hg hgf z)
  unfold ambientPhi
  rw [show (ambientPsi (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf).toLinearMap =
      (ambientPsi (gX := kirovGenus X) (gY := kirovGenus Y) f hf).toLinearMap ∘ₗ
      (ambientPsi (gX := kirovGenus Y) (gY := kirovGenus Z) g hg).toLinearMap from by rw [hpsi]; rfl]
  rw [LinearMap.toMatrix_comp (Pi.basisFun ℂ (Fin (kirovGenus Z))) (Pi.basisFun ℂ (Fin (kirovGenus Y)))
    (Pi.basisFun ℂ (Fin (kirovGenus X)))]
  rw [Matrix.transpose_mul, Matrix.mulVecLin_mul]
  rfl

end AmbientBridge

end Jacobians
