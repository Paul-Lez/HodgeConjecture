/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license.
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Division by a simple complex zero
-/

@[expose] public section

open Filter Topology

namespace Complex

/-- A simple analytic zero has an analytic quotient by the local coordinate. -/
theorem exists_analyticAt_mul_sub_of_zero_deriv_ne_zero
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (hderiv : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a = deriv f a ∧
      (∀ᶠ z in 𝓝 a, f z = (z - a) * g z) := by
  have horder : analyticOrderAt f a = 1 :=
    hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfa hderiv
  obtain ⟨g, hg, hg0, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast (n := 1)).mp horder
  have hfg' : ∀ᶠ z in 𝓝 a, f z = (z - a) * g z := by
    filter_upwards [hfg] with z hz
    simpa [smul_eq_mul] using hz
  have hderiv_eq : deriv f a = deriv (fun z ↦ (z - a) * g z) a :=
    EventuallyEq.deriv_eq hfg'
  have hderiv_mul : deriv (fun z ↦ (z - a) * g z) a = g a := by
    change deriv ((fun z ↦ z - a) * g) a = g a
    simpa [id, sub_eq_add_neg] using
      (((hasDerivAt_id a).sub_const a).mul hg.hasStrictDerivAt.hasDerivAt).deriv
  exact ⟨g, hg, (hderiv_eq.trans hderiv_mul).symm, hfg'⟩

/-- The quotient in the simple-zero division theorem is nonzero on a neighborhood. -/
theorem exists_eventually_analyticAt_mul_sub_of_zero_deriv_ne_zero
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (hderiv : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (∀ᶠ z in 𝓝 a, g z ≠ 0) ∧
      (∀ᶠ z in 𝓝 a, f z = (z - a) * g z) := by
  obtain ⟨g, hg, hg0, hfg⟩ :=
    exists_analyticAt_mul_sub_of_zero_deriv_ne_zero hf hfa hderiv
  have hg0' : g a ≠ 0 := by rw [hg0]; exact hderiv
  exact ⟨g, hg, hg.continuousAt.eventually_ne hg0', hfg⟩

end Complex
