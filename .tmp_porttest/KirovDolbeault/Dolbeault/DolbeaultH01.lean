/-
  Dolbeault cohomology `H^{0,1}(X)` and the comparison to Čech `H¹(X,𝒪)` — the L3 kernel of `D=0`
  Serre duality (`arithmeticGenus_eq_genus`). SCAFFOLD (from the 2026-06-02 expressibility spike).

  Spike finding (measured): the intrinsic ∂̄ operator `RealForms.dbar : A⁰ → A¹` is a *bare function*,
  but `A⁰ = SmoothCFunctions` and `A¹ = SmoothCOneForms` both already carry `AddCommGroup` + `Module ℝ`.
  So `H^{0,1}` is expressible with only bounded, mechanical friction — NO fundamental obstruction (the
  smooth-Dolbeault representation works; cf. the earlier (0,1)-form probe).

  FIRST ATOM (here): upgrade `dbar` to an ℝ-`LinearMap` `dbarL`. Its two obligations `dbar_add`,
  `dbar_smul` are TRUE (`differential` is additive/ℝ-linear via `mfderiv`; `proj01` is a CLM, hence
  linear) — bounded to prove, left as honest named obligations here pending the `mfderiv`-additivity plumbing.

  THEN (documented, not yet stated to avoid a mis-typed signature):
  * `A^{0,1} X` := the (0,1)-forms = range of the `proj01`-induced endomorphism on `A¹` (a `Submodule`).
  * `DolbeaultH01 X := A^{0,1} X ⧸ LinearMap.range dbarL` (on a curve `A^{0,2}=0`, so `H^{0,1}` is this
    cokernel). Resolve whether `A¹`/the quotient carries a `Module ℂ` (the fiber is `ℂ →L[ℝ] ℂ` valued
    in `Trivial X ℂ`) — needed to state the comparison as a `≃ₗ[ℂ]`.
  * **L3 kernel:** `cechH1 𝔘 0 ≃ₗ[ℂ] DolbeaultH01 X` — Čech↔Dolbeault, via ∂̄-globalization
    (`DbarLocal.dbar_solvable_locally` [building] + partition of unity + Čech patching). PDE-free.
  * **L4:** `arithmeticGenus_eq_genus` = `finrank`-transport along that equiv + finiteness.
-/
import KirovDolbeault.Dolbeault.RealForms

open scoped Manifold ContDiff

-- The `SmoothCOneForms` hom-bundle `TopologicalSpace`/`DFunLike` instances synthesize only under the
-- permissive transparency option `RealForms` itself uses (the ℂ-ℝ-module diamond); without it the
-- section `ext`/`coe_injective` lemmas fail to find `TopologicalSpace (TotalSpace …)`.
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `∂̄` is additive (`differential` is additive via `mfderiv_add`; `proj01` is linear). -/
theorem dbar_add (u v : SmoothCFunctions X) : dbar (u + v) = dbar u + dbar v := by
  refine ContMDiffSection.ext fun x => ?_
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x := (u.contMDiff x).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑v) x := (v.contMDiff x).mdifferentiableAt (by simp)
  simp only [ContMDiffSection.coe_add, Pi.add_apply]
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(u + v)) x)
      = proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) + proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑v) x)
  rw [show (⇑(u + v) : X → ℂ) = ⇑u + ⇑v from rfl, mfderiv_add hu hv, map_add]

/-- `∂̄` is ℝ-homogeneous (`const_smul_mfderiv`; `proj01` is linear). -/
theorem dbar_smul (c : ℝ) (u : SmoothCFunctions X) : dbar (c • u) = c • dbar u := by
  refine ContMDiffSection.ext fun x => ?_
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x := (u.contMDiff x).mdifferentiableAt (by simp)
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(c • u)) x)
      = c • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x)
  rw [show (⇑(c • u) : X → ℂ) = c • ⇑u from rfl, const_smul_mfderiv hu, map_smul]

/-- The intrinsic ∂̄ operator as an ℝ-linear map `A⁰ →ₗ[ℝ] A¹` (upgrade of the bare `dbar`), so that
`LinearMap.range dbarL` — the image needed to form `H^{0,1}` — is available. -/
noncomputable def dbarL : SmoothCFunctions X →ₗ[ℝ] SmoothCOneForms X where
  toFun := dbar
  map_add' := dbar_add
  map_smul' c u := dbar_smul c u

@[simp] theorem dbarL_apply (u : SmoothCFunctions X) : dbarL u = dbar u := rfl

end Jacobians.Dolbeault
