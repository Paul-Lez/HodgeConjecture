/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.DbarDisk

/-!
# R0 — the `(z − a)⁻¹` sign/normalization test for the fine-sheaf residue functional

This file is the **gate** for the Forster §17.3 fine-sheaf (PoU/area-integral) construction of
the residue functional `Res : H¹(X, Ω) → ℂ` (lane R of `docs/planning/CAMPAIGN_KEYSTONE.md`;
design in `docs/planning/S3_FINESHEAF_RES_SCOPING.md`, risk register item 1).  It pins, once and
for all, the sign/normalization convention that every later rung (R4 integral functional, R6
Mittag–Leffler tie, R8 nondegeneracy witness) must cite — derived end-to-end from the proven
`DbarDisk.cauchyPompeiu_area`, not chosen by hand.

## The model computation

Single-chart model of a Mittag–Leffler datum with principal part `(z − a)⁻¹` and residue `1`:
take a smooth compactly supported cutoff `χ` with `χ a = 1` and form the *smeared* (1,1)-density
`∂̄(χ·(z − a)⁻¹)` (a smooth compactly supported function away from `a`; the Lean total function
has junk value `0` at the single point `a`, which is `volume`-negligible).  The headline is

  `∫_ℂ ∂̄(χ·(z − a)⁻¹) dA = −π·χ(a)`   (`integral_dbar_smearedSimplePole`),

where the integral is against **Lebesgue area** `volume` on `ℂ` and `∂̄ = DbarDisk.dbar =
½(∂ₓ + i·∂_y)`.  Proof: away from `a` the factor `(z − a)⁻¹` is holomorphic, so by the Wirtinger
Leibniz rule (`dbar_mul`, new here) `∂̄(χ·(z−a)⁻¹) = (∂̄χ)/(z − a)`; the integral is then exactly
`DbarDisk.cauchyPompeiu_area` evaluated at the pole `z = a`.

## THE PINNED CONVENTION (cite this, do not re-derive)

With `∂̄ := DbarDisk.dbar` and area integrals against Lebesgue `volume` on `ℂ` (the chart-
coefficient representation of S3 scoping §2.2), the residue functional must be normalized as

  `Res := resNormalization • (area integral)`,  `resNormalization = −π⁻¹`,

so that the residue-`1` simple-pole model datum evaluates to `+1`
(`resNormalization_integral_eq_one`).  Bookkeeping against the classical Forster `(2πi)⁻¹·∬ τ`:
a chart (1,1)-form `τ = t·dz̄∧dz` integrates as `∬ τ = 2i·∫ t dA`, and for the *coboundary
orientation* `σ_loc = χ·(principal part)` produced by smoothing the datum itself one gets
`(2πi)⁻¹·2i·(−π) = −1`; our `resNormalization = (2πi)⁻¹·(−2i)`
(`resNormalization_eq_two_pi_I_inv_mul`) absorbs that global sign so the ladder's
simple-pole/residue-`1` witness lands on `+1`, matching `Jacobians.Dolbeault.resAt`'s
`resAt_const_mul_sub_inv` (`Res_a((z−a)⁻¹) = 1`) and the `GlobalResidue.nondegenerate` target
`res (cup …) = 1`.  Equivalently: read `τ` against `dz∧dz̄ = −2i·dA`.  **Do not fudge**: the raw
Forster constant on the Lebesgue-area integral would be `(2πi)⁻¹·(−π) = i/2`; the honest pinned
pair is (area integral `= −π·χ(a)`, normalizer `= −π⁻¹`).

## Main declarations

* `Jacobians.Dolbeault.FineResidue.dbar_mul` — Wirtinger `∂̄` Leibniz rule.
* `Jacobians.Dolbeault.FineResidue.dbar_smul_inv_sub` — `∂̄(χ·(z−a)⁻¹) = (∂̄χ)/(z−a)` off `a`.
* `Jacobians.Dolbeault.FineResidue.integral_dbar_smearedSimplePole` — the `−π·χ(a)` headline.
* `Jacobians.Dolbeault.FineResidue.resNormalization` — the pinned constant `−π⁻¹`.
* `Jacobians.Dolbeault.FineResidue.resNormalization_integral_eq_one` — the end-to-end sign test.
* `Jacobians.Dolbeault.FineResidue.exists_signTest_witness` — non-vacuity: a concrete
  `ContDiffBump` cutoff realizes the hypotheses at every `a`.
-/

open Complex MeasureTheory Metric
open scoped Real Topology

namespace Jacobians.Dolbeault.FineResidue

open DbarDisk

/-! ### The Wirtinger Leibniz rule -/

/-- **Leibniz rule for `∂̄`.** At a point where both factors are ℝ-differentiable,
`∂̄(f·g) = (∂̄f)·g + f·(∂̄g)`.  Immediate from `fderiv_mul` and bilinearity of the
`½(∂ₓ + i·∂_y)` combination. -/
theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = dbar f z * g z + f z * dbar g z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Away from the pole, the smeared simple-pole density is the cutoff's `∂̄` against the
principal part: `∂̄(χ·(z − a)⁻¹) = (∂̄χ)(ζ)/(ζ − a)` for `ζ ≠ a` (the second Leibniz term dies
because `(z − a)⁻¹` is holomorphic at `ζ`). -/
theorem dbar_smul_inv_sub {χ : ℂ → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (a : ℂ) {ζ : ℂ}
    (hζ : ζ ≠ a) :
    dbar (fun z => χ z * (z - a)⁻¹) ζ = dbar χ ζ / (ζ - a) := by
  have hsub : ζ - a ≠ 0 := sub_ne_zero.mpr hζ
  have hinvC : DifferentiableAt ℂ (fun z : ℂ => (z - a)⁻¹) ζ :=
    ((differentiableAt_id.sub_const a).inv hsub)
  rw [dbar_mul (hχ.differentiable (by simp) ζ) (hinvC.restrictScalars ℝ),
    dbar_eq_zero_of_differentiableAt hinvC, mul_zero, add_zero, div_eq_mul_inv]

/-! ### The headline area integral -/

/-- **R0 headline.**  For a smooth compactly supported cutoff `χ`, the Lebesgue area integral of
the smeared simple-pole density is

  `∫_ℂ ∂̄(χ·(z − a)⁻¹) dA = −π·χ(a)`.

This is `DbarDisk.cauchyPompeiu_area` evaluated at the pole: the integrand agrees a.e. with
`(∂̄χ)(ζ)/(ζ − a)`.  This fixes the sign and the `π` (not `2π`) scale of the fine-sheaf residue
ladder once and for all. -/
theorem integral_dbar_smearedSimplePole {χ : ℂ → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχsupp : HasCompactSupport χ) (a : ℂ) :
    ∫ ζ, dbar (fun z => χ z * (z - a)⁻¹) ζ = -π * χ a := by
  have hane : ∀ᵐ ζ : ℂ ∂volume, ζ ≠ a := by
    refine ae_iff.mpr ?_
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton a
  have hae : (fun ζ => dbar (fun z => χ z * (z - a)⁻¹) ζ)
      =ᵐ[volume] fun ζ => dbar χ ζ / (ζ - a) := by
    filter_upwards [hane] with ζ hζ
    exact dbar_smul_inv_sub hχ a hζ
  rw [integral_congr_ae hae, cauchyPompeiu_area hχ hχsupp a]

/-! ### The pinned normalization constant -/

/-- **THE PINNED RESIDUE NORMALIZATION** for the fine-sheaf (Forster §17.3) residue ladder, in
the chart-coefficient/Lebesgue-area representation (S3 scoping §2.2): the residue functional is

  `Res(c) := resNormalization • ∑_j ∫_ℂ ρ̃_j · t_j ∂volume`,  `resNormalization = −π⁻¹`.

Derived (not chosen) in `resNormalization_integral_eq_one`: this is the unique constant making
the smeared residue-`1` simple-pole model datum `∂̄(χ·(z − a)⁻¹)` evaluate to `+1`.  Relative to
Forster's `(2πi)⁻¹·∬ τ` it is `(2πi)⁻¹·(−2i)`, i.e. the chart coefficient `t` of `τ` is read
against the 2-form `dz∧dz̄ = −2i·dA` (see `resNormalization_eq_two_pi_I_inv_mul` and the module
docstring).  R4–R8 must cite this constant; do not re-derive or "simplify" it. -/
noncomputable def resNormalization : ℂ := -(π : ℂ)⁻¹

/-- Bookkeeping against Forster's `(2πi)⁻¹`: `resNormalization = (2πi)⁻¹·(−2i)` — the Jacobian
of reading a chart `(1,1)`-coefficient against `dz∧dz̄ = −2i·dA` instead of Lebesgue area. -/
theorem resNormalization_eq_two_pi_I_inv_mul :
    resNormalization = (2 * π * I)⁻¹ * (-2 * I) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [resNormalization]
  field_simp

/-- **R0 end-to-end sign test (the gate).**  With the pinned normalization, the smeared
residue-`1` simple-pole model datum evaluates to exactly `1`:

  `(−π⁻¹) · ∫_ℂ ∂̄(χ·(z − a)⁻¹) dA = 1`  whenever `χ a = 1`.

This matches the circle-integral atom `Jacobians.Dolbeault.resAt_const_mul_sub_inv`
(`Res_a((z−a)⁻¹) = 1`) and the `GlobalResidue.nondegenerate` target `res (cup …) = 1`. -/
theorem resNormalization_integral_eq_one {χ : ℂ → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχsupp : HasCompactSupport χ) {a : ℂ} (hχa : χ a = 1) :
    resNormalization * ∫ ζ, dbar (fun z => χ z * (z - a)⁻¹) ζ = 1 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_dbar_smearedSimplePole hχ hχsupp a, hχa, resNormalization]
  field_simp

/-! ### Non-vacuity: a concrete cutoff -/

/-- **Non-vacuity of the sign test.**  At every pole location `a` there is a concrete cutoff —
any `ContDiffBump` centered at `a`, complexified — satisfying all hypotheses, so the pinned
convention is realized, not vacuous. -/
theorem exists_signTest_witness (a : ℂ) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ χ a = 1 ∧
      resNormalization * ∫ ζ, dbar (fun z => χ z * (z - a)⁻¹) ζ = 1 := by
  have b : ContDiffBump a := ⟨1, 2, one_pos, one_lt_two⟩
  have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z => ((b z : ℝ) : ℂ) := by
    have h := Complex.ofRealCLM.contDiff.comp (b.contDiff (n := (⊤ : ℕ∞)))
    simpa [Function.comp_def] using h
  have hcs : HasCompactSupport fun z => ((b z : ℝ) : ℂ) := by
    have h := b.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    simpa [Function.comp_def] using h
  have hone : ((b a : ℝ) : ℂ) = 1 := by
    rw [b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one]
  exact ⟨fun z => ((b z : ℝ) : ℂ), hcd, hcs, hone,
    resNormalization_integral_eq_one hcd hcs hone⟩

end Jacobians.Dolbeault.FineResidue
