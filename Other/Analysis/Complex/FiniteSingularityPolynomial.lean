/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Other.Analysis.Complex.PolynomialGrowth
public import Other.Analysis.Complex.PolynomialComplement
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Polynomial growth away from finitely many singularities

A complex function bounded by a continuous function away from finitely many points
extends to an entire function with the same bound. In particular, a polynomial growth
bound makes this extension a polynomial of the corresponding degree.
-/

public section

open Filter Set Function
open scoped Topology

namespace Complex

/-- Removing finitely many singularities preserves a continuous pointwise bound. -/
theorem exists_entire_extension_of_finite_compl {E : Set ℂ} (hE : E.Finite)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Eᶜ) {B : ℂ → ℝ}
    (hB : Continuous B) (hbound : ∀ z ∉ E, ‖f z‖ ≤ B z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z ∉ E, g z = f z) ∧
      ∀ z, ‖g z‖ ≤ B z := by
  induction E, hE using Set.Finite.induction_on generalizing f with
  | empty =>
    exact ⟨f, by rw [compl_empty] at hf; exact differentiableOn_univ.mp hf, fun _ _ => rfl, fun z => hbound z (by simp)⟩
  | @insert c E hc hE ih =>
    have hEc : Eᶜ ∈ 𝓝 c := hE.isClosed.isOpen_compl.mem_nhds hc
    have hloc : ∀ᶠ z in 𝓝[≠] c, z ∉ insert c E := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hEc, self_mem_nhdsWithin] with z hz hzc
      exact fun h => (Set.mem_insert_iff.mp h).elim (fun h => hzc h) hz
    have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[≠] c)
        (norm ∘ fun z => f z - f c) := by
      refine ⟨B c + 1 + ‖f c‖, ?_⟩
      change ∀ᶠ z in 𝓝[≠] c, ‖f z - f c‖ ≤ B c + 1 + ‖f c‖
      have hBnear : ∀ᶠ z in 𝓝[≠] c, B z < B c + 1 :=
        (hB.continuousAt.eventually (gt_mem_nhds (by linarith))).filter_mono
          nhdsWithin_le_nhds
      filter_upwards [hloc, hBnear] with z hz hBz
      exact norm_sub_le_of_le ((hbound z hz).trans hBz.le) le_rfl
    let g := update f c (limUnder (𝓝[≠] c) f)
    have hg : DifferentiableOn ℂ g Eᶜ :=
      differentiableOn_update_limUnder_of_isLittleO hEc
        (hf.mono (by intro z hz; simp only [mem_compl_iff, mem_insert_iff, Set.mem_sdiff, mem_singleton_iff] at hz ⊢; exact fun h => h.elim hz.2 hz.1)) hbounded.isLittleO_sub_self_inv
    have hgbound : ∀ z ∉ E, ‖g z‖ ≤ B z := by
      intro z hz
      by_cases hzc : z = c
      · rw [hzc]
        have : NeBot (𝓝[≠] c) := NormedField.nhdsNE_neBot c
        have hcont := (hg.differentiableAt hEc).continuousAt
        apply le_of_tendsto_of_tendsto (b := 𝓝[≠] c)
          (hcont.norm.tendsto.mono_left nhdsWithin_le_nhds)
          (hB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        filter_upwards [hloc] with w hw
        have hwc : w ≠ c := (ne_of_mem_of_not_mem (Set.mem_insert c E) hw).symm
        simpa [g, update_of_ne hwc] using hbound w hw
      · simpa [g, update_of_ne hzc] using hbound z (by simp [hzc, hz])
    obtain ⟨F, hF, hFeq, hFbound⟩ := ih hg hgbound
    refine ⟨F, hF, ?_, hFbound⟩
    intro z hz
    have hzc : z ≠ c := (ne_of_mem_of_not_mem (Set.mem_insert c E) hz).symm
    rw [hFeq z (fun h => hz (Set.mem_insert_of_mem c h))]
    exact update_of_ne hzc _ _

/-- Polynomial growth away from finitely many points determines a polynomial. -/
theorem exists_polynomial_of_polynomial_growth_off_finite {E : Set ℂ} (hE : E.Finite)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Eᶜ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hbound : ∀ z ∉ E, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z ∉ E, p.eval z = f z := by
  obtain ⟨g, hg, heq, hgbound⟩ := exists_entire_extension_of_finite_compl hE hf
    (by fun_prop) hbound
  obtain ⟨p, hp, hpg⟩ := exists_polynomial_of_polynomial_growth hg hC N hgbound
  exact ⟨p, hp, fun z hz => (hpg z).trans (heq z hz)⟩

/-- A holomorphic function of polynomial growth on a complex polynomial principal open set
is represented there by a multivariate polynomial. -/
theorem exists_mvPolynomial_of_polynomial_growth_on_nonzero {n : ℕ}
    {f : (Fin n → ℂ) → ℂ} (p : MvPolynomial (Fin n) ℂ)
    (hp : p ≠ 0)
    (hf : DifferentiableOn ℂ f {z | MvPolynomial.eval z p ≠ 0})
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hgrowth : ∀ z, MvPolynomial.eval z p ≠ 0 →
      ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ q : MvPolynomial (Fin n) ℂ,
      ∀ z, MvPolynomial.eval z p ≠ 0 → MvPolynomial.eval z q = f z := by
  classical
  induction n generalizing C with
  | zero =>
    refine ⟨MvPolynomial.C (f 0), fun z _ => ?_⟩
    simp only [MvPolynomial.eval_C]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    obtain ⟨nodes, hnodes, hslice_ne⟩ :=
      exists_nodes_slice_ne_zero (k := N + 1) hp
    let ps (i : Fin (N + 1)) : MvPolynomial (Fin n) ℂ :=
      Polynomial.eval (MvPolynomial.C (nodes i)) (MvPolynomial.finSuccEquiv ℂ n p)
    have eval_ps (i : Fin (N + 1)) (y : Fin n → ℂ) :
        MvPolynomial.eval y (ps i) = MvPolynomial.eval (Fin.cons (nodes i) y) p := by
      rw [MvPolynomial.eval_eq_eval_mv_eval']
      simp only [ps, Polynomial.eval_map]
      rw [show nodes i = MvPolynomial.eval y (MvPolynomial.C (nodes i)) by simp,
        Polynomial.eval₂_at_apply]
      simp
    have hpoly (i : Fin (N + 1)) : ∃ q : MvPolynomial (Fin n) ℂ,
        ∀ y, MvPolynomial.eval y (ps i) ≠ 0 →
          MvPolynomial.eval y q = f (Fin.cons (nodes i) y) := by
      have hdiff : DifferentiableOn ℂ (fun y : Fin n → ℂ => f (Fin.cons (nodes i) y))
          {y | MvPolynomial.eval y (ps i) ≠ 0} := by
        apply hf.fun_comp (by fun_prop)
        intro y hy
        change MvPolynomial.eval (Fin.cons (nodes i) y) p ≠ 0
        rwa [← eval_ps]
      apply ih (ps i) (hslice_ne i) hdiff
        (C := C * (1 + ‖nodes i‖) ^ N) (by positivity)
      intro y hy
      apply growth_fin_cons_of_bound hC
      exact hgrowth _ (by simpa only [← eval_ps] using hy)
    choose qs hqs using hpoly
    let basis (i : Fin (N + 1)) : MvPolynomial (Fin (n + 1)) ℂ :=
      (Lagrange.basis Finset.univ nodes i).eval₂ MvPolynomial.C (MvPolynomial.X 0)
    let q : MvPolynomial (Fin (n + 1)) ℂ :=
      ∑ i, MvPolynomial.rename Fin.succ (qs i) * basis i
    let s : MvPolynomial (Fin n) ℂ := ∏ i, ps i
    have hs : s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hslice_ne i
    have hdense : Dense {y : Fin n → ℂ | MvPolynomial.eval y s ≠ 0} :=
      MvPolynomial.dense_complex_nonzero s hs
    have heq_good (z : Fin (n + 1) → ℂ) (hzD : MvPolynomial.eval z p ≠ 0)
        (hzs : MvPolynomial.eval (fun j : Fin n => z j.succ) s ≠ 0) :
        MvPolynomial.eval z q = f z := by
      have hpsi (i : Fin (N + 1)) :
          MvPolynomial.eval (fun j : Fin n => z j.succ) (ps i) ≠ 0 := by
        intro hi
        apply hzs
        simp only [s, MvPolynomial.eval_prod, Finset.prod_eq_zero_iff]
        exact ⟨i, Finset.mem_univ i, hi⟩
      have hzcons : Fin.cons (z 0) (fun j : Fin n => z j.succ) = z := by
        ext i
        exact Fin.cases rfl (fun _ => rfl) i
      let r : Polynomial ℂ := Polynomial.map
        (MvPolynomial.eval fun j : Fin n => z j.succ)
        (MvPolynomial.finSuccEquiv ℂ n p)
      have hr : r ≠ 0 := by
        intro hr
        apply hzD
        rw [← hzcons, MvPolynomial.eval_eq_eval_mv_eval']
        simpa [r] using congrArg (Polynomial.eval (z 0)) hr
      have hline : DifferentiableOn ℂ
          (fun t => f (Fin.cons t fun j : Fin n => z j.succ))
          (r.rootSet ℂ : Set ℂ)ᶜ := by
        apply hf.fun_comp (by fun_prop)
        intro t ht
        simpa [r, Polynomial.mem_rootSet_of_ne hr,
            MvPolynomial.eval_eq_eval_mv_eval'] using ht
      obtain ⟨a, haN, ha⟩ := exists_polynomial_of_polynomial_growth_off_finite
        (Polynomial.rootSet_finite r ℂ) hline (C := C *
          (1 + ‖fun j : Fin n => z j.succ‖) ^ N) (by positivity) N (fun t ht => by
            convert growth_fin_cons_of_bound hC t (fun j : Fin n => z j.succ)
              (hgrowth _ (by simpa [r, Polynomial.mem_rootSet_of_ne hr,
                MvPolynomial.eval_eq_eval_mv_eval'] using ht)) using 1
            ring)
      have haintr := Lagrange.eq_interpolate (f := a)
        (show Set.InjOn nodes (Finset.univ : Finset (Fin (N + 1))) from
          fun _ _ _ _ h => hnodes h)
        (show a.degree < ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ) from
          lt_of_le_of_lt Polynomial.degree_le_natDegree (by
            simp only [Finset.card_univ, Fintype.card_fin]
            exact_mod_cast Nat.lt_succ_of_le haN))
      have heval := congrArg (Polynomial.eval (z 0)) haintr
      have hzroot : z 0 ∉ r.rootSet ℂ := by
        rw [Polynomial.mem_rootSet_of_ne hr]
        intro h
        apply hzD
        rw [← hzcons, MvPolynomial.eval_eq_eval_mv_eval']
        simpa [r] using h
      rw [ha (z 0) hzroot, hzcons] at heval
      rw [heval, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
      simp only [q, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
        MvPolynomial.eval_rename, Function.comp_def, hqs _ _ (hpsi _), basis]
      apply Finset.sum_congr rfl
      intro i _
      have hnode : nodes i ∉ r.rootSet ℂ := by
        rw [Polynomial.mem_rootSet_of_ne hr]
        change Polynomial.eval (nodes i) r ≠ 0
        change Polynomial.eval (nodes i)
          (Polynomial.map (MvPolynomial.eval fun j : Fin n => z j.succ)
            (MvPolynomial.finSuccEquiv ℂ n p)) ≠ 0
        simp only [Polynomial.eval_map]
        rw [show nodes i = MvPolynomial.eval (fun j : Fin n => z j.succ)
            (MvPolynomial.C (nodes i)) by simp, Polynomial.eval₂_at_apply]
        exact hpsi i
      rw [ha (nodes i) hnode]
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      simp [Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum, map_sum]
    refine ⟨q, fun z hz => ?_⟩
    let tail : Fin n → ℂ := fun j => z j.succ
    let T : Set (Fin n → ℂ) := {y | MvPolynomial.eval y s ≠ 0}
    let F := 𝓝[T] tail
    have htail_closure : tail ∈ closure T := by
      rw [hdense.closure_eq]
      exact Set.mem_univ tail
    let _ : NeBot F := mem_closure_iff_nhdsWithin_neBot.mp htail_closure
    have hcons : ContinuousAt
        (fun y : Fin n → ℂ => (Fin.cons (z 0) y : Fin (n + 1) → ℂ)) tail := by
      fun_prop
    have hzcons' : Fin.cons (z 0) tail = z := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    have hq_tend : Tendsto
        (fun y : Fin n → ℂ => MvPolynomial.eval (Fin.cons (z 0) y) q) F
        (𝓝 (MvPolynomial.eval z q)) := by
      have h := (differentiable_mvPolynomial_eval q).continuous.continuousAt.comp' hcons
      change Tendsto (fun y => MvPolynomial.eval (Fin.cons (z 0) y) q)
        (𝓝 tail ⊓ Filter.principal T) (𝓝 (MvPolynomial.eval z q))
      convert h.tendsto.mono_left inf_le_left using 1
      rw [hzcons']
    have hf_tend : Tendsto (fun y : Fin n → ℂ => f (Fin.cons (z 0) y)) F (𝓝 (f z)) := by
      have hf_at : ContinuousAt f z :=
        (hf.differentiableAt ((isOpen_eval_ne_zero p).mem_nhds hz)).continuousAt
      rw [← hzcons'] at hf_at
      have h := hf_at.comp' hcons
      change Tendsto (fun y => f (Fin.cons (z 0) y))
        (𝓝 tail ⊓ Filter.principal T) (𝓝 (f z))
      convert h.tendsto.mono_left inf_le_left using 1
      rw [hzcons']
    have hevent : (fun y : Fin n → ℂ => MvPolynomial.eval (Fin.cons (z 0) y) q) =ᶠ[F]
        fun y : Fin n → ℂ => f (Fin.cons (z 0) y) := by
      have hD : ∀ᶠ y in 𝓝 tail, MvPolynomial.eval (Fin.cons (z 0) y) p ≠ 0 :=
        hcons.eventually ((isOpen_eval_ne_zero p).mem_nhds (by
          change MvPolynomial.eval (Fin.cons (z 0) tail) p ≠ 0
          rwa [hzcons']))
      filter_upwards [self_mem_nhdsWithin, hD.filter_mono inf_le_left] with y hyT hyD
      exact heq_good _ hyD hyT
    exact tendsto_nhds_unique_of_eventuallyEq hq_tend hf_tend hevent

end Complex
