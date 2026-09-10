import Other.Algebra.DeRham.KaehlerWedgeAlternating

open scoped Matrix

namespace Algebra.DeRham

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem mk_swap_neg_test (a b d : A) :
    mk R A 2 a ![b, d] = -mk R A 2 a ![d, b] := by
  have h := mk_alt R A 2 a ![b + d, b + d] (0 : Fin 2) (1 : Fin 2)
    (by simp) (by decide)
  simp only [show ![b + d, b + d] =
      Function.update (![0, b + d] : Fin 2 → A) 0 (b + d) by
        funext i; fin_cases i <;> simp,
    mk_diff_add] at h
  have hb : Function.update (![0, b + d] : Fin 2 → A) 0 b = ![b, b + d] := by
    funext i; fin_cases i <;> simp
  have hd : Function.update (![0, b + d] : Fin 2 → A) 0 d = ![d, b + d] := by
    funext i; fin_cases i <;> simp
  rw [hb, hd] at h
  rw [show ![b, b + d] =
      Function.update (![b, 0] : Fin 2 → A) 1 (b + d) by
        funext i; fin_cases i <;> simp,
    mk_diff_add] at h
  rw [show ![d, b + d] =
      Function.update (![d, 0] : Fin 2 → A) 1 (b + d) by
        funext i; fin_cases i <;> simp,
    mk_diff_add] at h
  have hbb' : Function.update (![b, 0] : Fin 2 → A) 1 b = ![b, b] := by
    funext i; fin_cases i <;> simp
  have hbd : Function.update (![b, 0] : Fin 2 → A) 1 d = ![b, d] := by
    funext i; fin_cases i <;> simp
  have hdb : Function.update (![d, 0] : Fin 2 → A) 1 b = ![d, b] := by
    funext i; fin_cases i <;> simp
  have hdd' : Function.update (![d, 0] : Fin 2 → A) 1 d = ![d, d] := by
    funext i; fin_cases i <;> simp
  rw [hbb', hbd, hdb, hdd'] at h
  have hbb : mk R A 2 a ![b, b] = 0 :=
    mk_alt R A 2 a ![b, b] (0 : Fin 2) (1 : Fin 2) (by simp) (by decide)
  have hdd : mk R A 2 a ![d, d] = 0 :=
    mk_alt R A 2 a ![d, d] (0 : Fin 2) (1 : Fin 2) (by simp) (by decide)
  rw [hbb, hdd, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

example (a : A) (w z : KaehlerDifferential R A) :
    kaehlerWedge R A (a • w) z = kaehlerWedge R A w (a • z) := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R A w
  obtain ⟨u, rfl⟩ := KaehlerDifferential.linearCombination_surjective R A z
  induction v using Finsupp.induction with
  | zero => simp
  | single_add b c v hb hc ih =>
      simp only [map_add, smul_add, ih, LinearMap.add_apply]
      congr 1
      clear ih
      induction u using Finsupp.induction with
      | zero => simp
      | single_add d e u hd he ih' =>
          simp only [map_add, smul_add, LinearMap.add_apply, ih']
          congr 1
          simp only [Finsupp.linearCombination_single]
          rw [smul_smul, smul_smul,
            kaehlerWedge_smul_D_smul_D,
            kaehlerWedge_smul_D_smul_D]
          congr 1
          ring

example (w z : KaehlerDifferential R A) :
    kaehlerWedge R A w z = -kaehlerWedge R A z w := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R A w
  obtain ⟨u, rfl⟩ := KaehlerDifferential.linearCombination_surjective R A z
  induction v using Finsupp.induction with
  | zero => simp
  | single_add b a v hb ha ih =>
      simp only [map_add, LinearMap.add_apply, ih, neg_add_rev]
      rw [add_comm]
      congr 1
      clear ih
      induction u using Finsupp.induction with
      | zero => simp
      | single_add d c u hd hc ih' =>
          simp only [map_add, LinearMap.add_apply, ih', neg_add_rev]
          rw [add_comm]
          congr 1
          simp only [Finsupp.linearCombination_single]
          rw [kaehlerWedge_smul_D_smul_D,
            kaehlerWedge_smul_D_smul_D, mul_comm]
          exact mk_swap_neg_test R A (c * a) b d

end Algebra.DeRham

namespace Algebra.DeRham

example (B : Type) [CommRing B] [Algebra ℂ B]
    (ω : KaehlerDifferential ℂ B)
    (hgen : ∀ w : KaehlerDifferential ℂ B, ∃ a : B, a • ω = w)
    (η : Form ℂ B 2) : η = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (relations ℂ B 2) η
  induction r using Finsupp.induction with
  | zero => rfl
  | single_add g c r hg hc ih =>
      rw [map_add, ih, add_zero]
      change Submodule.Quotient.mk (Finsupp.single g c) = 0
      rw [show Finsupp.single g c = c • Finsupp.single g 1 by simp,
        Submodule.Quotient.mk_smul]
      apply smul_eq_zero.mpr
      right
      change mk ℂ B 2 g.1 g.2 = 0
      have hv : g.2 = ![g.2 0, g.2 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hv]
      have hkw := kaehlerWedge_smul_D_smul_D ℂ B g.1 (g.2 0) 1 (g.2 1)
      rw [mul_one] at hkw
      rw [← hkw]
      obtain ⟨a, ha⟩ := hgen (KaehlerDifferential.D ℂ B (g.2 0))
      obtain ⟨b, hb⟩ := hgen (KaehlerDifferential.D ℂ B (g.2 1))
      rw [← ha, ← hb, smul_smul, one_smul]
      exact complex_kaehlerWedge_smul_self B (g.1 * a) b ω

end Algebra.DeRham
