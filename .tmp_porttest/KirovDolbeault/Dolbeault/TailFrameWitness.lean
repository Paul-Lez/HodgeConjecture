/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailSerre
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealSlitGeometry
import KirovDolbeault.Dolbeault.CanonicalFormDifferential
import KirovDolbeault.MeromorphicLiouville

/-!
# The tail pair frame witness: `Nonempty (TailPairFrame X)` at positive genus

Keystone input 1 of the tail-duality campaign (`docs/planning/TAILRR_BLOCKER.md`): the
construction of a `TailPairFrame X` — a canonical frame `(ω₀, K)`, its per-point chart slot
family, and the **pair-frame residue theorem** `∑ₚ Res_p(F·ω₀) = 0`.

## The route

The pair-frame residue atom is discharged from the PROVEN Gate-A residue theorem
`SerreResidueTheorem.residueTheorem_unconditional` (`∑ₐ Res_a(α·g) = 0` for a *holomorphic*
1-form `α` and a global meromorphic `g`), via three bridges, all built here:

1. **The residue bridge** `resAt_eq_planarCoeff_neg_one`: the contour residue `resAt`
   (`Residue.lean`, circle integrals) IS the order-`(−1)` planar Laurent coefficient
   `planarCoeff (-1)` (`TailSerre.lean`, limit-based) for any function meromorphic at the
   centre.  Proven by leading-monomial stripping: the two functionals agree on monomials
   (`∮ (z−c)^n = 0` for `n ≠ −1`, Cauchy–Goursat) and on order-`≥ 0` germs (both vanish:
   removable singularity), and both are additive.

2. **The junk repair** `MeromorphicFunction.repair`: replaces `F.toFun` by its punctured-limit
   `holoRepr`, so the chart reads are *honestly analytic* off the divisor support — the
   analyticity hypothesis `residueTheorem_unconditional` consumes.  Germ-equal to `F` at every
   point, so all planar coefficients (and the residue sum) are unchanged.

3. **The frame from a nonzero holomorphic form** `tailPairFrameOfForm`: at `kirovGenus X > 0`
   a nonzero `α : HolomorphicOneForms X` exists; `ω₀ := holToMero α` with its form divisor
   `K` (`exists_form_divisor`) is a `CanonicalForm17Data`, and the slot family is the chart
   coefficient `coeffAt α p` (exact order `K p` by `order_eq`, definitionally).

## Main declarations

* `resAt_eq_planarCoeff_neg_one` — the residue bridge (one-variable, reusable).
* `Jacobians.MeromorphicFunction.repair` — the junk repair, with germ-equality and honest
  analyticity off poles.
* `canonicalDataOfForm` / `tailPairFrameOfForm` — the frame from a nonzero holomorphic form.
* `nonempty_tailPairFrame_of_kirovGenus_pos` — **the headline**:
  `0 < kirovGenus X → Nonempty (TailPairFrame X)`.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI §1; Forster,
*Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter
open scoped Manifold ContDiff Topology Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Jacobians

namespace Dolbeault

/-! ## Part 1 — the residue bridge `resAt = planarCoeff (-1)` (one variable)

`resAt` (`Residue.lean`) is the contour-integral residue; `planarCoeff (-1)` (`TailSerre.lean`)
is the limit-based order-`(−1)` Laurent coefficient.  For a function meromorphic at the centre
they agree: both vanish on order-`≥ 0` germs, agree on Laurent monomials, and are additive, so
leading-monomial stripping closes the gap. -/

/-- The order-`0` coefficient of a constant is the constant. -/
theorem laurentCoeff_const (a c : ℂ) : laurentCoeff 0 (fun _ => a) c = a := by
  have hd : dePole 0 (fun _ => a) c = fun _ => a := by
    funext z
    simp [dePole]
  rw [laurentCoeff, hd]
  exact tendsto_const_nhds.limUnder_eq

/-- All strips of a constant beyond the first are the zero function. -/
theorem stripFun_const_eq_zero (a c : ℂ) : ∀ j : ℕ, stripFun (fun _ => a) c 0 (j + 1) = fun _ => (0 : ℂ)
  | 0 => by
      funext z
      rw [stripFun_succ]
      show (fun _ => a) z - laurentCoeff (0 + (0 : ℕ)) (stripFun (fun _ => a) c 0 0) c
        * (z - c) ^ ((0 : ℤ) + (0 : ℕ)) = 0
      rw [stripFun_zero_iter]
      norm_num [laurentCoeff_const]
  | (j + 1) => by
      funext z
      rw [stripFun_succ, stripFun_const_eq_zero a c j]
      have h0 : laurentCoeff (0 + ((j : ℤ) + 1)) (fun _ => (0 : ℂ)) c = 0 :=
        laurentCoeff_zero_fun _ _
      push_cast
      rw [h0]
      ring

/-- Planar coefficients of a constant: `a` at order `0`, `0` elsewhere. -/
theorem planarCoeff_const (k : ℤ) (a c : ℂ) :
    planarCoeff k (fun _ => a) c = if k = 0 then a else 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [planarCoeff_zero_fun]
    simp
  · have hmero : MeromorphicAt (fun _ => a) c := MeromorphicAt.const a c
    have hord : meromorphicOrderAt (fun _ => a) c = 0 := by
      rw [meromorphicOrderAt_const]
      exact if_neg ha
    rcases lt_trichotomy k 0 with hk | hk | hk
    · rw [if_neg (by omega)]
      refine planarCoeff_eq_zero_of_lt_order ?_ hmero
      rw [hord]
      exact_mod_cast hk
    · subst hk
      rw [if_pos rfl, planarCoeff_eq_fullCoeffFrom hmero (lo := 0)
        (by rw [hord]; exact le_of_eq (by norm_num)) le_rfl, sub_self, Int.toNat_zero,
        fullCoeffFrom_offset_zero', laurentCoeff_const]
    · rw [if_neg (by omega), planarCoeff_eq_fullCoeffFrom hmero (lo := 0)
        (by rw [hord]; exact le_of_eq (by norm_num)) (by omega)]
      have hj : (k - 0).toNat = (k.toNat - 1) + 1 := by omega
      rw [hj, fullCoeffFrom, stripFun_const_eq_zero a c (k.toNat - 1)]
      exact laurentCoeff_zero_fun _ _

/-- Planar coefficients of a Laurent monomial: `a` at the exponent, `0` elsewhere. -/
theorem planarCoeff_monomial (k : ℤ) (a c : ℂ) (m : ℤ) :
    planarCoeff k (fun z => a * (z - c) ^ m) c = if k = m then a else 0 := by
  have hswap : (fun z => a * (z - c) ^ m) = (fun z => (z - c) ^ m * (fun _ : ℂ => a) z) := by
    funext z
    ring
  rw [hswap, planarCoeff_monomial_mul m k (MeromorphicAt.const a c), planarCoeff_const]
  by_cases h : k = m <;> simp [h, sub_eq_zero]

/-- The contour residue of a Laurent monomial: `a` at exponent `−1`, `0` elsewhere
(`∮ (z−c)^m = 0` for `m ≠ −1`). -/
theorem resAt_monomial (a c : ℂ) (m : ℤ) :
    resAt (fun z => a * (z - c) ^ m) c = if m = -1 then a else 0 := by
  by_cases hm : m = -1
  · subst hm
    rw [if_pos rfl]
    have h1 : (fun z => a * (z - c) ^ (-1 : ℤ)) = fun z => a * (z - c)⁻¹ := by
      funext z
      rw [zpow_neg_one]
    rw [h1]
    exact resAt_const_mul_sub_inv a c
  · rw [if_neg hm]
    have hcint : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∮ z in C(c, r), a * (z - c) ^ m) = 0 := by
      filter_upwards with r
      rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne hm,
        mul_zero]
    rw [resAt_eq_of_eventuallyEq_circleIntegral hcint, smul_zero]

/-- The contour residue vanishes on order-`≥ 0` germs (removable singularity: the
normal-form representative is analytic, hence holomorphic on a ball). -/
theorem resAt_eq_zero_of_order_nonneg {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c)
    (h : 0 ≤ meromorphicOrderAt F c) : resAt F c = 0 := by
  have heq := hF.eq_nhdsNE_toMeromorphicNFAt
  have hNF : MeromorphicNFAt (toMeromorphicNFAt F c) c := meromorphicNFAt_toMeromorphicNFAt
  have hordeq : meromorphicOrderAt (toMeromorphicNFAt F c) c = meromorphicOrderAt F c :=
    (meromorphicOrderAt_congr heq).symm
  have hana : AnalyticAt ℂ (toMeromorphicNFAt F c) c :=
    hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 (hordeq ▸ h)
  rw [resAt_congr heq]
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball c ρ,
      DifferentiableAt ℂ (toMeromorphicNFAt F c) z := by
    have hev := hana.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz)).differentiableAt⟩
  exact resAt_eq_zero_of_differentiableOn_ball hρ hball

/-- The bounded-depth residue bridge: at pole depth `≤ m`, the contour residue is the
order-`(−1)` planar coefficient.  Induction on the depth by leading-monomial stripping. -/
private theorem resAt_eq_planarCoeff_neg_one_of_le {c : ℂ} :
    ∀ m : ℕ, ∀ F : ℂ → ℂ, MeromorphicAt F c →
      ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c →
      resAt F c = planarCoeff (-1) F c
  | 0, F, hF, hord => by
      have h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt F c := by
        have : ((-(0 : ℤ) : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) := by norm_num
        rw [← this]
        simpa using hord
      rw [resAt_eq_zero_of_order_nonneg hF h0]
      refine (planarCoeff_eq_zero_of_lt_order ?_ hF).symm
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-1 : ℤ) < 0)) h0
  | (m + 1), F, hF, hord => by
      set n : ℤ := -((m : ℤ) + 1) with hn
      have hordn : ((n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c := by
        refine le_trans (le_of_eq ?_) hord
        rw [hn]
        push_cast
        ring_nf
      set a : ℂ := laurentCoeff n F c with ha
      by_cases ha0 : a = 0
      · -- the coefficient at the bottom vanishes, so the order is already ≥ −m
        have hlt : ((n : ℤ) : WithTop ℤ) < meromorphicOrderAt F c :=
          (laurentCoeff_eq_zero_iff hF hordn).mp (by rw [← ha]; exact ha0)
        have hord' : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c := by
          rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
          · rw [htop]; exact le_top
          · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
            rw [← hv]
            rw [← hv] at hlt
            have hnv : n < v := by exact_mod_cast hlt
            have : -(m : ℤ) ≤ v := by omega
            exact_mod_cast this
        exact resAt_eq_planarCoeff_neg_one_of_le m F hF hord'
      · -- strip the leading monomial
        set Mneg : ℂ → ℂ := fun z => -a * (z - c) ^ n with hMneg
        have hMnegm : MeromorphicAt Mneg c := meromorphicAt_monomial (-a) c n
        have hMnegord : meromorphicOrderAt Mneg c = (n : WithTop ℤ) :=
          meromorphicOrderAt_monomial (neg_ne_zero.mpr ha0) c n
        set G : ℂ → ℂ := F + Mneg with hG
        have hGm : MeromorphicAt G c := hF.add hMnegm
        have hordG : ((n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G c := by
          refine le_trans (le_min hordn (le_of_eq hMnegord.symm)) ?_
          exact meromorphicOrderAt_add hF hMnegm
        have hcoeffG : laurentCoeff n G c = 0 := by
          rw [hG, laurentCoeff_add hF hMnegm hordn (le_of_eq hMnegord.symm), ← ha,
            hMneg, laurentCoeff_monomial]
          ring
        have hltG : ((n : ℤ) : WithTop ℤ) < meromorphicOrderAt G c :=
          (laurentCoeff_eq_zero_iff hGm hordG).mp hcoeffG
        have hordG' : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G c := by
          rcases eq_or_ne (meromorphicOrderAt G c) ⊤ with htop | hne
          · rw [htop]; exact le_top
          · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
            rw [← hv]
            rw [← hv] at hltG
            have hnv : n < v := by exact_mod_cast hltG
            have : -(m : ℤ) ≤ v := by omega
            exact_mod_cast this
        have hIH : resAt G c = planarCoeff (-1) G c :=
          resAt_eq_planarCoeff_neg_one_of_le m G hGm hordG'
        set M : ℂ → ℂ := fun z => a * (z - c) ^ n with hM
        have hMm : MeromorphicAt M c := meromorphicAt_monomial a c n
        have hFGM : F = G + M := by
          funext z
          rw [hG]
          simp only [Pi.add_apply, hMneg, hM]
          ring
        have hres : resAt F c = resAt G c + resAt M c := by
          rw [hFGM]
          exact resAt_add (MeromorphicAt.holoPunctured hGm) (MeromorphicAt.holoPunctured hMm)
        have hpla : planarCoeff (-1) F c = planarCoeff (-1) G c + planarCoeff (-1) M c := by
          rw [hFGM]
          exact planarCoeff_add hGm hMm (-1)
        have hMres : resAt M c = planarCoeff (-1) M c := by
          rw [hM, resAt_monomial, planarCoeff_monomial]
          by_cases hcase : n = -1
          · rw [if_pos hcase, if_pos hcase.symm]
          · rw [if_neg hcase, if_neg (fun h => hcase h.symm)]
        rw [hres, hpla, hIH, hMres]

/-- **The residue bridge** (one variable): for `F` meromorphic at `c`, the contour residue
`resAt F c` equals the order-`(−1)` planar Laurent coefficient `planarCoeff (-1) F c`. -/
theorem resAt_eq_planarCoeff_neg_one {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c) :
    resAt F c = planarCoeff (-1) F c := by
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · rw [planarCoeff_of_order_eq_top htop]
    have heq : F =ᶠ[𝓝[≠] c] (fun _ => (0 : ℂ)) := meromorphicOrderAt_eq_top_iff.mp htop
    rw [resAt_congr heq]
    exact resAt_eq_zero_of_differentiableOn_ball one_pos
      (fun z _ => differentiableAt_const 0)
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
    refine resAt_eq_planarCoeff_neg_one_of_le (max 0 (-v)).toNat F hF ?_
    rw [← hv]
    have h1 : -(((max 0 (-v)).toNat : ℤ)) ≤ v := by omega
    exact_mod_cast h1

end Dolbeault

/-! ## Part 2 — the junk repair of a meromorphic function

`F.toFun` may carry junk values at removable singularities (its meromorphy constrains only
germs).  The repair replaces it by the punctured limit `holoRepr`, which is germ-equal to `F`
at every point and *honestly analytic* off the poles — the hypothesis shape the Gate-A residue
theorem consumes. -/

namespace MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The chart read of `holoRepr` is germ-equal (punctured) to the chart read of `toFun`,
at every point: both agree with the normal-form representative off the centre. -/
theorem holoRepr_read_eventuallyEq (f : MeromorphicFunction X) (x : X) :
    f.holoRepr ∘ (chartAt (H := ℂ) x).symm =ᶠ[𝓝[≠] ((chartAt (H := ℂ) x) x)]
      f.toFun ∘ (chartAt (H := ℂ) x).symm :=
  (f.holoRepr_chartPullback_eventuallyEq_NFAt x).trans
    (f.meromorphic x).eq_nhdsNE_toMeromorphicNFAt.symm

/-- **The junk repair**: the meromorphic function with underlying map `holoRepr` (the
punctured limit of `f.toFun`).  Germ-equal to `f` everywhere; honestly analytic off poles. -/
noncomputable def repair (f : MeromorphicFunction X) : MeromorphicFunction X where
  toFun := f.holoRepr
  meromorphic := fun x => (f.meromorphic x).congr (f.holoRepr_read_eventuallyEq x).symm

@[simp] theorem repair_toFun (f : MeromorphicFunction X) : f.repair.toFun = f.holoRepr := rfl

/-- The repaired chart read is honestly analytic at any point of nonnegative order. -/
theorem repair_read_analyticAt (f : MeromorphicFunction X) {x : X}
    (h : 0 ≤ f.orderAtPoint x) :
    AnalyticAt ℂ (fun z => f.repair.toFun ((chartAt (H := ℂ) x).symm z))
      ((chartAt (H := ℂ) x) x) :=
  f.analyticAt_holoRepr_chartPullback_of_orderNonneg h

/-- Off the divisor support, the order (as an integer) is nonnegative. -/
theorem orderAtPoint_nonneg_of_not_mem_div_support {f : MeromorphicFunction X} {p : X}
    (h : p ∉ f.div.support) : 0 ≤ f.orderAtPoint p := by
  have hdiv0 : (f.div) p = 0 := Finsupp.notMem_support_iff.mp h
  have h1 : f.orderAtPoint p = 0 := hdiv0
  omega

end MeromorphicFunction

namespace Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 3 — the canonical frame from a nonzero holomorphic form -/

/-- The form order of `holToMero α` reads the chart coefficient `coeffAt α p`. -/
theorem formOrderW_holToMero (α : HolomorphicOneForms X) (p : X) :
    (holToMero α).formOrderW p
      = meromorphicOrderAt (coeffAt α p) ((chartAt (H := ℂ) p) p) := by
  rw [MeromorphicOneForm.formOrderW,
    show (holToMero α).toFun = holToSection α from rfl, formCoeff_holToSection]

/-- A nonzero holomorphic form has non-germ-zero coefficient somewhere (witnessed at a point
where the centred local representative is nonzero). -/
theorem exists_formOrderW_holToMero_ne_top (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    ∃ x, (holToMero α).formOrderW x ≠ ⊤ := by
  obtain ⟨b, hb⟩ := exists_localRep_self_ne_zero α hα
  refine ⟨b, ?_⟩
  rw [formOrderW_holToMero]
  intro htop
  have hev : coeffAt α b =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] (fun _ => (0 : ℂ)) :=
    meromorphicOrderAt_eq_top_iff.mp htop
  have hmem : (chartAt (H := ℂ) b) b ∈ (chartAt (H := ℂ) b).target :=
    (chartAt (H := ℂ) b).map_source (mem_chart_source ℂ b)
  have hana : AnalyticAt ℂ (coeffAt α b) ((chartAt (H := ℂ) b) b) :=
    coeffAt_analyticAt α b hmem
  have h1 : Filter.Tendsto (coeffAt α b) (𝓝[≠] ((chartAt (H := ℂ) b) b))
      (𝓝 (Jacobians.Montel.localRep α b b)) := by
    have h1' : Filter.Tendsto (coeffAt α b) (𝓝 ((chartAt (H := ℂ) b) b))
        (𝓝 (coeffAt α b ((chartAt (H := ℂ) b) b))) := hana.continuousAt
    rw [coeffAt_chartCenter] at h1'
    exact h1'.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (coeffAt α b) (𝓝[≠] ((chartAt (H := ℂ) b) b)) (𝓝 0) :=
    (Filter.tendsto_congr' hev).mpr tendsto_const_nhds
  exact hb (tendsto_nhds_unique h1 h2)

/-- **The canonical-frame datum from a nonzero holomorphic 1-form** (Forster §17.4 with
`ω₀ = α` holomorphic): `ω₀ := holToMero α`, `K :=` its form divisor (`exists_form_divisor`). -/
noncomputable def canonicalDataOfForm (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    CanonicalForm17Data X where
  ω₀ := holToMero α
  nontrivial := exists_formOrderW_holToMero_ne_top α hα
  K := (exists_form_divisor (holToMero α)
    (MeromorphicOneForm.formOrderW_ne_top_of_exists (holToMero α)
      (exists_formOrderW_holToMero_ne_top α hα))).choose
  order_eq := (exists_form_divisor (holToMero α)
    (MeromorphicOneForm.formOrderW_ne_top_of_exists (holToMero α)
      (exists_formOrderW_holToMero_ne_top α hα))).choose_spec

@[simp] theorem canonicalDataOfForm_ω₀ (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    (canonicalDataOfForm α hα).ω₀ = holToMero α := rfl

/-! ## Part 4 — the pair-frame residue theorem from Gate A -/

/-- **The planar pair-frame residue theorem** for a holomorphic frame form: for any global
meromorphic `F` and any finite `S ⊇ supp (div F)`, the planar residue sum of the slot
products vanishes.  Route: junk-repair `F`, apply the Gate-A residue theorem
(`residueTheorem_unconditional`), and convert each contour residue to a planar coefficient by
the residue bridge. -/
theorem resSum_planar (α : HolomorphicOneForms X) (F : MeromorphicFunction X)
    {S : Finset X} (hS : F.div.support ⊆ S) :
    ∑ p ∈ S, planarCoeff (-1)
      (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * coeffAt α p ζ)
      ((chartAt (H := ℂ) p) p) = 0 := by
  classical
  have hpoles : ∀ x : X, x ∉ S →
      AnalyticAt ℂ (fun z => F.repair.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) := by
    intro x hx
    have hx' : x ∉ F.div.support := fun h => hx (hS h)
    exact F.repair_read_analyticAt
      (MeromorphicFunction.orderAtPoint_nonneg_of_not_mem_div_support hx')
  have h0 := SerreResidueTheorem.residueTheorem_unconditional α F.repair S hpoles
  rw [← h0]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- the slot-product integrands are germ-equal (junk repair does not move germs)
  have hev : (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * coeffAt α p ζ)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) p) p)]
      (fun z => coeffAt α p z * F.repair.toFun ((chartAt (H := ℂ) p).symm z)) := by
    filter_upwards [F.holoRepr_read_eventuallyEq p] with z hz
    have hz' : F.repair.toFun ((chartAt (H := ℂ) p).symm z)
        = F.toFun ((chartAt (H := ℂ) p).symm z) := hz
    rw [hz', mul_comm]
  -- the repaired slot-product integrand is meromorphic at the chart centre
  have hmem : (chartAt (H := ℂ) p) p ∈ (chartAt (H := ℂ) p).target :=
    (chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p)
  have hmero : MeromorphicAt
      (fun z => coeffAt α p z * F.repair.toFun ((chartAt (H := ℂ) p).symm z))
      ((chartAt (H := ℂ) p) p) :=
    (coeffAt_analyticAt α p hmem).meromorphicAt.mul (F.repair.meromorphic p)
  have hstep1 : planarCoeff (-1)
      (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * coeffAt α p ζ)
      ((chartAt (H := ℂ) p) p)
      = planarCoeff (-1)
        (fun z => coeffAt α p z * F.repair.toFun ((chartAt (H := ℂ) p).symm z))
        ((chartAt (H := ℂ) p) p) := planarCoeff_congr hev (-1)
  rw [hstep1]
  exact (resAt_eq_planarCoeff_neg_one hmero).symm

/-! ## Part 5 — the frame and the headline -/

/-- **The tail pair frame from a nonzero holomorphic 1-form.**  Slots are the chart
coefficients `coeffAt α p` (exact order `K p` by `order_eq`, definitionally); the residue
atom is `resSum_planar`. -/
noncomputable def tailPairFrameOfForm (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    TailPairFrame X where
  data := canonicalDataOfForm α hα
  slot := fun p => coeffAt α p
  slot_mero := fun p =>
    (coeffAt_analyticAt α p
      ((chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p))).meromorphicAt
  slot_order := fun p => by
    have h := (canonicalDataOfForm α hα).order_eq p
    rw [show (canonicalDataOfForm α hα).ω₀ = holToMero α from rfl,
      formOrderW_holToMero] at h
    exact h
  resSum := fun F => resSum_planar α F Finset.subset_union_left

/-- **The headline — keystone input 1 of the tail-duality campaign**: at positive genus
(`kirovGenus X = dim H⁰(X, Ω) > 0`, i.e. a nonzero holomorphic 1-form exists), the tail
pair frame is nonempty. -/
theorem nonempty_tailPairFrame_of_kirovGenus_pos (hg : 0 < kirovGenus X) :
    Nonempty (TailPairFrame X) := by
  have hex : ∃ α : HolomorphicOneForms X, α ≠ 0 := by
    by_contra hcon
    push Not at hcon
    haveI hsub : Subsingleton (HolomorphicOneForms X) :=
      ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h0 : kirovGenus X = 0 := by
      unfold kirovGenus
      exact Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨α, hα⟩ := hex
  exact ⟨tailPairFrameOfForm α hα⟩

end Dolbeault

end Jacobians

end
