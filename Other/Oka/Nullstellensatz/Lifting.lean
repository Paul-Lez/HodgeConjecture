/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Noetherian
public import Other.Oka.Nullstellensatz.CommonRoot

/-!
# Lifting points of zero loci along a Weierstrass polynomial

Let `I = (f₁, …, f_r)` be an ideal of germs in `n + 1` variables containing a Weierstrass
polynomial `W` in the last variable, and let `p₁, …, p_m` generate an ideal containing the
elimination ideal `I ∩ 𝒪_n`. Then every point `a` near the origin of `ℂⁿ` at which all `pⱼ`
vanish lifts to a point `(a, t)` near the origin of `ℂ^{n+1}` at which all `fᵢ` vanish
(`LocalOkaRing.eventually_exists_lift`): the zero locus of the elimination ideal is the
projection of the zero locus of `I`.

The proof divides each `fᵢ` by `W`, leaving remainders `bᵢ` which are polynomials in the last
variable, and eliminates the last variable with resultants: the resultants of `W` with the
combinations `∑ᵢ sⁱ bᵢ` lie in `I ∩ 𝒪_n`, hence vanish at `a`, and over `ℂ` this forces a
common root `t` of `W(a, ·)` and all `bᵢ(a, ·)`
(`Polynomial.exists_common_root_of_forall_resultant_eq_zero`). The root `t` is small because
`W` is a Weierstrass polynomial.

To evaluate the resultants at `a` we use that evaluation at a point is a ring homomorphism on
the germs whose power series converges absolutely there (`LocalOkaRing.summableSubalgebra`,
`LocalOkaRing.evalAlgHom`).

## Main definitions

- `LocalOkaRing.summableSubalgebra z`: the germs whose power series converges absolutely at
  `z`.
- `LocalOkaRing.evalAlgHom z`: evaluation at `z` on these germs, a `ℂ`-algebra homomorphism.

## Main results

- `LocalOkaRing.eventually_exists_lift`: the lifting property described above.
-/

@[expose] public section

open Filter Topology Polynomial

namespace MvPowerSeries

variable {ι : Type*}

lemma SummableAt.neg {P : MvPowerSeries ι ℂ} {x : ι → ℂ} (h : P.SummableAt x) :
    (-P).SummableAt x := by
  have : (-P).term x = fun d ↦ -P.term x d := funext fun d ↦ by simp [term]
  simpa [SummableAt, this] using h

end MvPowerSeries

namespace LocalOkaRing

variable {ι : Type*}

/-- The germs whose power series converges absolutely at `z`. -/
def summableSubalgebra (z : ι → ℂ) : Subalgebra ℂ (LocalOkaRing ι) where
  carrier := {P | (P : MvPowerSeries ι ℂ).SummableAt z}
  mul_mem' ha hb := MvPowerSeries.SummableAt.mul ha hb
  add_mem' ha hb := MvPowerSeries.SummableAt.add ha hb
  algebraMap_mem' c := MvPowerSeries.summableAt_algebraMap c z

lemma mem_summableSubalgebra {z : ι → ℂ} {P : LocalOkaRing ι} :
    P ∈ summableSubalgebra z ↔ (P : MvPowerSeries ι ℂ).SummableAt z :=
  Iff.rfl

/-- Evaluation at `z` of the germs whose power series converges absolutely at `z`. -/
noncomputable def evalAlgHom (z : ι → ℂ) : summableSubalgebra z →ₐ[ℂ] ℂ where
  toFun P := ((P : LocalOkaRing ι) : MvPowerSeries ι ℂ).eval z
  map_one' := MvPowerSeries.eval_one z
  map_mul' P Q := MvPowerSeries.eval_mul_of_summableAt
    (P := ((P : LocalOkaRing ι) : MvPowerSeries ι ℂ))
    (Q := ((Q : LocalOkaRing ι) : MvPowerSeries ι ℂ)) P.2 Q.2
  map_zero' := MvPowerSeries.eval_of_zero z
  map_add' P Q := MvPowerSeries.eval_add_of_summableAt
    (P := ((P : LocalOkaRing ι) : MvPowerSeries ι ℂ))
    (Q := ((Q : LocalOkaRing ι) : MvPowerSeries ι ℂ)) P.2 Q.2
  commutes' c := MvPowerSeries.eval_algebraMap c z

lemma evalAlgHom_apply (z : ι → ℂ) (P : summableSubalgebra z) :
    evalAlgHom z P = ((P : LocalOkaRing ι) : MvPowerSeries ι ℂ).eval z :=
  rfl

/-- Near the origin, every coefficient of a polynomial over the germs converges. -/
lemma eventually_forall_coeff_mem_summableSubalgebra (q : (LocalOkaRing ι)[X]) :
    ∀ᶠ z in 𝓝 (0 : ι → ℂ), ∀ k, q.coeff k ∈ summableSubalgebra z := by
  have h : ∀ᶠ z in 𝓝 (0 : ι → ℂ), ∀ k ∈ Finset.range (q.natDegree + 1),
      q.coeff k ∈ summableSubalgebra z :=
    (Filter.eventually_all_finset _).mpr fun k _ ↦ (q.coeff k).locallyConvergent
  filter_upwards [h] with z hz k
  by_cases hk : k ≤ q.natDegree
  · exact hz k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hk)]
    exact zero_mem _

/-- A polynomial over the germs whose coefficients converge at `z` lifts to a polynomial over
`summableSubalgebra z`. -/
lemma exists_map_eq_of_forall_coeff_mem {z : ι → ℂ} (q : (LocalOkaRing ι)[X])
    (hq : ∀ k, q.coeff k ∈ summableSubalgebra z) :
    ∃ q' : (summableSubalgebra z)[X], q'.map (summableSubalgebra z).val.toRingHom = q := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  exact fun k ↦ ⟨⟨q.coeff k, hq k⟩, rfl⟩

variable {n : ℕ}

/-- The value of `fromPolynomial q` at `(a, t)` is the value at `t` of the complex polynomial
obtained by evaluating the coefficients of `q` at `a`. -/
lemma eval_fromPolynomial_snoc_eq {a : Fin n → ℂ} (q' : (summableSubalgebra a)[X]) (t : ℂ) :
    ((fromPolynomial (q'.map (summableSubalgebra a).val.toRingHom) :
        LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc a t) =
      (q'.map (evalAlgHom a).toRingHom).eval t := by
  set q := q'.map (summableSubalgebra a).val.toRingHom with hq
  have hc : ∀ k, ((q.coeff k : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt a :=
    fun k ↦ by rw [hq, Polynomial.coeff_map]; exact (q'.coeff k).2
  rw [eval_fromPolynomial_snoc q a hc t, eval_eq_sum_range' (n := q.natDegree + 1)]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hq, Polynomial.coeff_map, Polynomial.coeff_map]
    rfl
  · refine Nat.lt_succ_of_le (natDegree_map_le.trans ?_)
    rw [hq, natDegree_map_eq_of_injective Subtype.val_injective q']

/-- **Lifting points of the zero locus of an elimination ideal.** Let `I = (f₁, …, f_r)`
contain the Weierstrass polynomial `W` in the last variable, and let `p₁, …, p_m` generate an
ideal containing `I ∩ 𝒪_n`. Then for every neighbourhood `U` of the origin of `ℂ^{n+1}`, every
point `a` close enough to the origin of `ℂⁿ` at which all `pⱼ` vanish lifts to a point
`(a, t) ∈ U` at which all `fᵢ` vanish. -/
theorem eventually_exists_lift {r m : ℕ} {W : (LocalOkaRing (Fin n))[X]}
    (hW : IsLocalWeierstrassPolynomial
      (W.map (Subring.subtype (localOkaSubring (Fin n)).toSubring)))
    (f : Fin r → LocalOkaRing (Fin (n + 1)))
    (hWf : fromPolynomial W ∈ Ideal.span (Set.range f)) (p : Fin m → LocalOkaRing (Fin n))
    (hp : (Ideal.span (Set.range f)).comap incl ≤ Ideal.span (Set.range p))
    {U : Set (Fin (n + 1) → ℂ)} (hU : U ∈ 𝓝 0) :
    ∀ᶠ a in 𝓝 (0 : Fin n → ℂ),
      (∀ j, ((p j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval a = 0) →
      ∃ t : ℂ, (Fin.snoc a t : Fin (n + 1) → ℂ) ∈ U ∧
        ∀ i, ((f i : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
          (Fin.snoc a t) = 0 := by
  classical
  set I := Ideal.span (Set.range f)
  have hWm : W.Monic := monic_of_injective Subtype.val_injective hW.monic
  -- divide each `fᵢ` by `W`
  choose a b hb hab using fun i ↦ localweierstrass_division W hW (f i)
  have hbdeg : ∀ i, (b i).natDegree ≤ W.natDegree + 1 := fun i ↦ by
    by_cases hb0 : b i = 0
    · rw [hb0, natDegree_zero]; exact Nat.zero_le _
    · have := (natDegree_lt_natDegree hb0 (hb i)).le
      omega
  have hfb : ∀ i, fromPolynomial (b i) ∈ I := fun i ↦ by
    have : fromPolynomial (b i) = f i - a i * fromPolynomial W := by rw [hab i]; ring
    rw [this]
    exact sub_mem (Ideal.subset_span ⟨i, rfl⟩) (Ideal.mul_mem_left _ _ hWf)
  -- the resultants and their membership in the elimination ideal
  obtain ⟨B, hB⟩ : ∃ B : ℕ → (LocalOkaRing (Fin n))[X],
      B = fun s : ℕ ↦ ∑ i : Fin r, C (algebraMap ℂ _ ((s : ℂ) ^ (i : ℕ))) * b i := ⟨_, rfl⟩
  have hBdeg : ∀ s, (B s).natDegree ≤ W.natDegree + 1 := fun s ↦ hB ▸
    natDegree_sum_le_of_forall_le _ _ fun i _ ↦ (natDegree_C_mul_le _ _).trans (hbdeg i)
  obtain ⟨c, hc⟩ : ∃ c : ℕ → LocalOkaRing (Fin n),
      c = fun s ↦ resultant W (B s) W.natDegree (W.natDegree + 1) :=
    ⟨_, rfl⟩
  have hcI : ∀ s, incl (c s) ∈ I := by
    intro s
    rw [hc]
    have h1 := Ideal.mem_map_of_mem (fromPolynomial (n := n))
      (mem_span_of_resultant W (B s) le_rfl (hBdeg s) (Or.inr (Nat.succ_ne_zero _)))
    rw [fromPolynomial_C, Ideal.map_span, Set.image_pair] at h1
    refine (Ideal.span_le.mpr ?_) h1
    rintro x (rfl | rfl)
    · exact hWf
    · simp only [hB, map_sum, map_mul]
      exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hfb i)
  choose h hh using fun s ↦
    (Submodule.mem_span_range_iff_exists_fun (R := LocalOkaRing (Fin n))).mp
      (hp (Ideal.mem_comap.mpr (hcI s)))
  -- the neighbourhood of the origin on which the division identities can be evaluated
  set G : Set (Fin (n + 1) → ℂ) := {z | (∀ i,
      ((a i : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt z ∧
      ((fromPolynomial (b i) : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).SummableAt z) ∧
      ((fromPolynomial W : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).SummableAt z} with hGdef
  have hG : G ∈ 𝓝 0 :=
    (eventually_all.mpr fun i ↦
      (a i).locallyConvergent.and (fromPolynomial (b i)).locallyConvergent).and
      (fromPolynomial W).locallyConvergent
  have hsnoc : Tendsto (fun q : (Fin n → ℂ) × ℂ ↦ (Fin.snoc q.1 q.2 : Fin (n + 1) → ℂ))
      (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun q : (Fin n → ℂ) × ℂ ↦ (Fin.snoc q.1 q.2 : Fin (n + 1) → ℂ) :=
      Continuous.finSnoc continuous_fst continuous_snd
    have h0 : (Fin.snoc (0 : Fin n → ℂ) (0 : ℂ) : Fin (n + 1) → ℂ) = 0 := by
      funext j
      refine Fin.lastCases ?_ (fun j ↦ ?_) j <;> simp
    have := hcont.tendsto ((0 : Fin n → ℂ), (0 : ℂ))
    rwa [nhds_prod_eq, h0] at this
  obtain ⟨A, hA, T0, hT0, hAT⟩ := eventually_prod_iff.mp (hsnoc.eventually_mem (inter_mem hU hG))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hT0
  -- the conditions on the base point
  have hsum_h : ∀ᶠ a' in 𝓝 (0 : Fin n → ℂ), ∀ s ∈ Finset.range (W.natDegree * r + 1), ∀ j,
      h s j ∈ summableSubalgebra a' :=
    (eventually_all_finset _).mpr fun s _ ↦ eventually_all.mpr fun j ↦ (h s j).locallyConvergent
  have hsum_p : ∀ᶠ a' in 𝓝 (0 : Fin n → ℂ), ∀ j, p j ∈ summableSubalgebra a' :=
    eventually_all.mpr fun j ↦ (p j).locallyConvergent
  have hsum_b : ∀ᶠ a' in 𝓝 (0 : Fin n → ℂ), ∀ i k, (b i).coeff k ∈ summableSubalgebra a' :=
    eventually_all.mpr fun i ↦ eventually_forall_coeff_mem_summableSubalgebra (b i)
  filter_upwards [hA, eventually_error_lt W hW hε,
    eventually_forall_coeff_mem_summableSubalgebra W, hsum_b, hsum_h, hsum_p]
    with a' ha'A herr hWa hba hha hpa hvan
  set T := summableSubalgebra a'
  obtain ⟨W', hW'⟩ := exists_map_eq_of_forall_coeff_mem W hWa
  choose b' hb' using fun i ↦ exists_map_eq_of_forall_coeff_mem (b i) (hba i)
  set ev := (evalAlgHom a').toRingHom with hev
  have hW'm : W'.Monic := monic_of_injective Subtype.val_injective (hW' ▸ hWm)
  have hWdeg : W'.natDegree = W.natDegree := by
    rw [← hW', natDegree_map_eq_of_injective Subtype.val_injective]
  have hwm : (W'.map ev).Monic := hW'm.map ev
  have hwdeg : (W'.map ev).natDegree = W.natDegree := by rw [hW'm.natDegree_map, hWdeg]
  have hcoeff : ∀ (q : T[X]) k, (q.map ev).coeff k =
      (((q.map T.val.toRingHom).coeff k : LocalOkaRing (Fin n)) :
        MvPowerSeries (Fin n) ℂ).eval a' := fun q k ↦ by
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    rfl
  -- the resultants vanish at `a'`
  have hres0 : ∀ s ∈ Finset.range ((W'.map ev).natDegree * r + 1),
      resultant (W'.map ev) (∑ i : Fin r, C ((s : ℂ) ^ (i : ℕ)) * (b' i).map ev)
        (W'.map ev).natDegree (W.natDegree + 1) = 0 := by
    intro s hs
    rw [hwdeg] at hs ⊢
    set B' : T[X] := ∑ i : Fin r, C (algebraMap ℂ T ((s : ℂ) ^ (i : ℕ))) * b' i with hB'
    have hB'1 : B'.map T.val.toRingHom = B s := by
      rw [hB', hB, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Polynomial.map_mul, Polynomial.map_C, hb' i]
      congr 2
    have hB'2 : B'.map ev = ∑ i : Fin r, C ((s : ℂ) ^ (i : ℕ)) * (b' i).map ev := by
      rw [hB', Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Polynomial.map_mul, Polynomial.map_C]
      congr 2
      exact (evalAlgHom a').commutes _
    have hcs : c s = T.val.toRingHom (resultant W' B' W.natDegree (W.natDegree + 1)) := by
      rw [hc]
      dsimp only
      rw [← resultant_map_map, hW', hB'1]
    rw [← hB'2, resultant_map_map]
    change (((resultant W' B' W.natDegree (W.natDegree + 1) : T) : LocalOkaRing (Fin n)) :
      MvPowerSeries (Fin n) ℂ).eval a' = 0
    have hcs' : ((resultant W' B' W.natDegree (W.natDegree + 1) : T) : LocalOkaRing (Fin n)) =
        c s := hcs.symm
    rw [hcs', ← hh s, AddSubmonoidClass.coe_finsetSum,
      MvPowerSeries.eval_sum_of_summableAt (P := fun j ↦
        ((h s j • p j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ))
        (fun j _ ↦ (hha s hs j).mul (hpa j))]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [smul_eq_mul, MulMemClass.coe_mul,
      MvPowerSeries.eval_mul_of_summableAt (hha s hs j) (hpa j), hvan j, mul_zero]
  have hbdeg' : ∀ i, ((b' i).map ev).natDegree ≤ W.natDegree + 1 := fun i ↦ by
    refine natDegree_map_le.trans ?_
    rw [← natDegree_map_eq_of_injective (f := T.val.toRingHom) Subtype.val_injective (b' i),
      hb' i]
    exact hbdeg i
  obtain ⟨t, hwt, hbt⟩ := exists_common_root_of_forall_resultant_eq_zero hwm
    (fun i ↦ (b' i).map ev) hbdeg' hres0
  have hsmall : ∑ k ∈ Finset.range (W'.map ev).natDegree, ‖(W'.map ev).coeff k‖ * ε ^ k <
      ε ^ (W'.map ev).natDegree := by
    rw [hwdeg]
    convert herr using 3 with k
    rw [hcoeff, hW']
  have htε : ‖t‖ < ε := norm_lt_of_isRoot hwm hε hsmall hwt
  have hmem := hAT ha'A (hball (by rwa [dist_zero_right]))
  refine ⟨t, hmem.1, fun i ↦ ?_⟩
  obtain ⟨hGa, hGW⟩ := hmem.2
  rw [hab i, AddMemClass.coe_add, MulMemClass.coe_mul,
    MvPowerSeries.eval_add_of_summableAt ((hGa i).1.mul hGW) (hGa i).2,
    MvPowerSeries.eval_mul_of_summableAt (hGa i).1 hGW, ← hW', ← hb' i,
    eval_fromPolynomial_snoc_eq, eval_fromPolynomial_snoc_eq, hwt.eq_zero, (hbt i).eq_zero,
    mul_zero, add_zero]

end LocalOkaRing

end
