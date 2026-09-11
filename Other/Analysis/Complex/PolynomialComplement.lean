/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complements of complex polynomial zero sets

The nonzero locus of a nonzero complex multivariate polynomial is path connected in the
usual product topology. The complex line through two points restricts the polynomial to a
nonzero univariate polynomial, so it suffices to avoid its finitely many roots.
-/

@[expose] public section

open scoped Topology

open Set Filter

namespace MvPolynomial

/-- The nonzero locus of a nonzero complex multivariate polynomial is dense. -/
theorem dense_complex_nonzero {ι : Type*} (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    Dense {x : ι → ℂ | p.eval x ≠ 0} := by
  obtain ⟨y, hy⟩ : ∃ y, p.eval y ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (MvPolynomial.funext (by simpa using h))
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  let f : ℂ → (ι → ℂ) := fun t i => x i + t * (y i - x i)
  let q : Polynomial ℂ := p.eval₂ Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i - x i))
  have he (t : ℂ) : q.eval t = p.eval (f t) := by
    change (Polynomial.evalRingHom t) (p.eval₂ _ _) = _
    rw [MvPolynomial.hom_eval₂]
    have hh : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
      ext z
      simp
    rw [hh]
    congr 1
    funext i
    simp [f]
  have hq : q ≠ 0 := by
    intro h
    have := he 1
    simp [h, f] at this
    exact hy this.symm
  have hd : Dense {t : ℂ | ¬ q.IsRoot t} := by
    simpa only [compl_ofPred] using
      (Polynomial.finite_setOfPred_isRoot hq).countable.dense_compl ℂ
  rw [mem_closure_iff_nhds]
  intro U hU
  have hf : Continuous f := by fun_prop
  have hpre : f ⁻¹' U ∈ 𝓝 0 := by
    apply hf.continuousAt.preimage_mem_nhds
    simpa [f] using hU
  obtain ⟨t, ht, htU⟩ := hd.inter_nhds_nonempty hpre
  refine ⟨f t, htU, ?_⟩
  simpa [Polynomial.IsRoot, he] using ht

/-- The nonzero locus of a complex multivariate polynomial is path connected. -/
theorem isPathConnected_complex_nonzero {ι : Type*} (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    IsPathConnected {x : ι → ℂ | p.eval x ≠ 0} := by
  have hn : ∃ x, p.eval x ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (MvPolynomial.funext (by simpa using h))
  obtain ⟨x, hx⟩ := hn
  refine ⟨x, hx, ?_⟩
  intro y hy
  let f : ℂ → (ι → ℂ) := fun t i => x i + t * (y i - x i)
  let q : Polynomial ℂ := p.eval₂ Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i - x i))
  have he (t : ℂ) : q.eval t = p.eval (f t) := by
    change (Polynomial.evalRingHom t) (p.eval₂ _ _) = _
    rw [MvPolynomial.hom_eval₂]
    have hh : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
      ext z
      simp
    rw [hh]
    change p.eval₂ (RingHom.id ℂ) _ = p.eval₂ (RingHom.id ℂ) _
    congr 1
    funext i
    simp [f]
  have hq : q ≠ 0 := by
    intro h
    have := he 0
    simp [h, f] at this
    exact hx this.symm
  have hc : IsPathConnected {t : ℂ | ¬ q.IsRoot t} :=
    (Polynomial.finite_setOfPred_isRoot hq).countable.isPathConnected_compl_of_one_lt_rank
      (by simp [Complex.rank_real_complex])
  have h0 : (0 : ℂ) ∈ {t | ¬ q.IsRoot t} := by
    simpa [Polynomial.IsRoot, he, f] using hx
  have h1 : (1 : ℂ) ∈ {t | ¬ q.IsRoot t} := by
    simpa [Polynomial.IsRoot, he, f] using hy
  have hj := (hc.joinedIn 0 h0 1 h1).map (show Continuous f by fun_prop)
  have hm : f '' {t | ¬ q.IsRoot t} ⊆ {z | p.eval z ≠ 0} := by
    rintro _ ⟨t, ht, rfl⟩
    simpa [Polynomial.IsRoot, he] using ht
  simpa [f] using hj.mono hm

end MvPolynomial
