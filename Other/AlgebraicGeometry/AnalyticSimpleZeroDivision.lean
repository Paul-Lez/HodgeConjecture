/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Division by a simple coordinate zero

An analytic function which vanishes at a point is locally an analytic
multiple of the centred coordinate.  The quotient is the analytic divided
difference `dslope`.  This is the local analytic input needed to divide an
odd holomorphic function on the elliptic curve by the odd coordinate `y` at
the finite branch points.
-/

@[expose] public noncomputable section

open scoped Topology

/-- An analytic function vanishing at `c` factors through `z - c`, with an
analytic quotient.  The equality is pointwise, including at the centre. -/
theorem AnalyticAt.exists_eq_sub_smul_analytic
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {c : 𝕜}
    (hf : AnalyticAt 𝕜 f c) (hfc : f c = 0) :
    ∃ g : 𝕜 → E, AnalyticAt 𝕜 g c ∧
      ∀ z, (z - c) • g z = f z := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨dslope f c, ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩, ?_⟩
  intro z
  exact sub_smul_dslope_of_zero hfc z

/-- Scalar-valued form of `AnalyticAt.exists_eq_sub_smul_analytic`. -/
theorem AnalyticAt.exists_eq_sub_mul_analytic
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} {c : 𝕜}
    (hf : AnalyticAt 𝕜 f c) (hfc : f c = 0) :
    ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g c ∧
      ∀ z, (z - c) * g z = f z := by
  simpa only [smul_eq_mul] using
    hf.exists_eq_sub_smul_analytic hfc

/-- Scalar factorization at a zero, with the value of the quotient at the
center identified with the derivative. -/
theorem AnalyticAt.exists_eq_sub_mul_analytic_deriv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} {c : 𝕜}
    (hf : AnalyticAt 𝕜 f c) (hfc : f c = 0) :
    ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g c ∧
      g c = deriv f c ∧ ∀ z, (z - c) * g z = f z := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨dslope f c, ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩,
    dslope_same f c, ?_⟩
  intro z
  simpa only [smul_eq_mul] using sub_smul_dslope_of_zero hfc z
