/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.GridMerge
public import Other.Oka.Analytification.GAGA.RungeSeveral
public import Other.Oka.Topology.Sheaves.Cohomology.Dimension
public import Other.Oka.Topology.Sheaves.Cohomology.Exhaustion
public import Other.Oka.Topology.Sheaves.Cohomology.MayerVietorisNatural

/-!
# Theorem B on product domains, for an abstract abelian sheaf on `ℂ^ι`

We carry out the sheaf-theoretic part of the proof of Theorem B for the structure sheaf on
`D = (ℂ^×)^P × ℂ^{ι \ P}` (see the plan in `Oka.Analytification.GAGA.Cousin`) for an arbitrary
abelian sheaf `F` on `ℂ^ι`, with the analytic input as hypotheses:

* `Complex.TheoremB.CousinSplitting F`: on overlaps coming from a Cousin splitting of holomorphic
  functions, sections of `F` split as well (for `F = 𝒪` this is a tautology);
* `Complex.TheoremB.MittagLefflerExhaustion F`: `lim¹_n F(U n) = 0` along the exhaustion
  `U n = prod (Complex.exhaustion P n)` of `D`.

The exhaustion step uses the Milnor-type vanishing `TopCat.Sheaf.H'_eq_zero_of_monotone`.

Cohomology of opens is Mathlib's `CategoryTheory.Sheaf.H' F q U = Extᵠ(ℤ[U], F)` with the
restriction maps `TopCat.Sheaf.MayerVietoris.res`.

## Main definitions

* `Complex.TheoremB.CompactlyZero F c W`: the class `c ∈ H'ᵠ(U)` restricts to zero on every
  open with compact closure in `W ⊆ U`.
* `Complex.TheoremB.exhaustionOpens P n`: the exhaustion `prod (Complex.exhaustion P n)` of `D`,
  as opens.

## Main results

* `Complex.TheoremB.compactlyZero_union`: the **merge lemma**: for a Cousin-shrinkable pair
  `A, B`, if `c` is compactly zero on `A` and on `B`, then on `A ∪ B` (Mayer–Vietoris and its
  naturality; in degree one via the Cousin splitting, in higher degrees via compact vanishing in
  one degree lower on the product of holed rectangles `A' ∩ B'`).
* `Complex.TheoremB.compactlyZero_prod`: every class of positive degree on an open `U` is
  compactly zero on every product of holed rectangles with closure in `U` (merging along grids,
  `Complex.HoledRect.mem_of_merge`, and local vanishing).
* `Complex.TheoremB.compactlyZeroOnProd`, `Complex.TheoremB.compactlyZero_puncturedSet`:
  classes of positive degree on a product of holed rectangles, or on `D`, are compactly zero.
* `Complex.TheoremB.eq_zero_of_eq_puncturedSet`: **Theorem B**: `H'ᵠ(D, F) = 0` for `q ≥ 1`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite Set
open TopCat.Sheaf.MayerVietoris

namespace Complex.TheoremB

open HoledRect

variable {ι : Type u}

set_option hygiene false in
/-- The space `ℂ^ι` as an object of `TopCat`. -/
local notation "𝕏" => TopCat.of (ι → ℂ)

variable (F : TopCat.AbSheaf 𝕏)

/-- The class `c ∈ H'ᵠ(U)` is *compactly zero on* `W`: `W ⊆ U` and `c` restricts to zero on every
open `V` with compact closure contained in `W`. -/
def CompactlyZero {q : ℕ} {U : Opens 𝕏} (c : CategoryTheory.Sheaf.H'.{u} F q U)
    (W : Set (ι → ℂ)) : Prop :=
  W ⊆ U ∧ ∀ (V : Opens 𝕏) (hV : V ≤ U), IsCompact (closure (V : Set (ι → ℂ))) →
    closure (V : Set (ι → ℂ)) ⊆ W → res F q hV c = 0

/-- The degree zero input: whenever holomorphic functions on `V` split as sums of holomorphic
functions on `A` and on `B` over `A ∩ B ⊆ V`, sections of `F` over `V` restrict to differences of
sections over `A` and over `B`. -/
def CousinSplitting : Prop :=
  ∀ (V A B : Opens 𝕏) (h : A ⊓ B ≤ V),
    (∀ d : (ι → ℂ) → ℂ, DifferentiableOn ℂ d V → ∃ fA fB : (ι → ℂ) → ℂ,
      DifferentiableOn ℂ fA A ∧ DifferentiableOn ℂ fB B ∧ ∀ x ∈ A ⊓ B, d x = fA x + fB x) →
    ∀ s : F.obj.obj (op V), ∃ (a : F.obj.obj (op A)) (b : F.obj.obj (op B)),
      F.obj.map (homOfLE h).op s =
        F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b

/-- `lim¹_n F(U n) = 0` along the exhaustion `U n = prod (Complex.exhaustion P n)` of
`(ℂ^×)^P × ℂ^{ι \ P}`. -/
def MittagLefflerExhaustion [DecidableEq ι] : Prop :=
  ∀ (P : Finset ι) (U : ℕ → Opens 𝕏) (hU : Monotone U),
    (∀ n, (U n : Set (ι → ℂ)) = prod (exhaustion P n)) → TopCat.Sheaf.LimOneVanishesOn F.obj hU

/-- Every class of degree `q` on a product of holed rectangles is compactly zero on it. -/
def CompactlyZeroOnProd (q : ℕ) : Prop :=
  ∀ (s : ι → HoledRect) (U : Opens 𝕏), (U : Set (ι → ℂ)) = prod s →
    ∀ c : CategoryTheory.Sheaf.H'.{u} F q U, CompactlyZero F c U

variable {F}

section CompactlyZero

variable {q : ℕ} {U : Opens 𝕏} {c : CategoryTheory.Sheaf.H'.{u} F q U}

lemma CompactlyZero.mono {W W' : Set (ι → ℂ)} (h : CompactlyZero F c W) (hW : W' ⊆ W) :
    CompactlyZero F c W' :=
  ⟨hW.trans h.1, fun V hV hc hVW ↦ h.2 V hV hc (hVW.trans hW)⟩

lemma compactlyZero_empty : CompactlyZero F c ∅ := by
  refine ⟨empty_subset _, fun V hV _ hVW ↦ ?_⟩
  have hV0 : V = ⊥ := by
    ext x
    exact ⟨fun hx ↦ (hVW (subset_closure hx)).elim, fun hx ↦ hx.elim⟩
  subst hV0
  have := TopCat.Sheaf.subsingleton_H'_bot F q
  exact Subsingleton.elim _ _

/-- A class which restricts to zero on an open `V` is compactly zero on `V`. -/
lemma compactlyZero_of_res_eq_zero {V : Opens 𝕏} (hV : V ≤ U) (h : res F q hV c = 0) :
    CompactlyZero F c V := by
  refine ⟨hV, fun V' hV' _ hV'V ↦ ?_⟩
  have hle : V' ≤ V := fun x hx ↦ hV'V (subset_closure hx)
  rw [← res_comp hV hle, h, map_zero]

end CompactlyZero

section Merge

variable {A' B' A'' B'' : Opens 𝕏} (hA : A'' ≤ A') (hB : B'' ≤ B')
include hA hB

/-- In degree zero, if holomorphic functions on `A' ∩ B'` split over `A'' ∩ B''`, then the
Mayer–Vietoris connecting map of `(A'', B'')` kills restrictions of classes on `A' ∩ B'`. -/
lemma δ_res_eq_zero_of_cousinSplitting (hC : CousinSplitting F)
    (hsplit : ∀ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g (A' ⊓ B' : Opens 𝕏) →
      ∃ fA fB : (ι → ℂ) → ℂ, DifferentiableOn ℂ fA A'' ∧ DifferentiableOn ℂ fB B'' ∧
        ∀ x ∈ A'' ⊓ B'', g x = fA x + fB x)
    (d : CategoryTheory.Sheaf.H'.{u} F 0 (A' ⊓ B')) :
    δ A'' B'' F 0 (res F 0 (inf_le_inf hA hB) d) = 0 := by
  obtain ⟨a, b, hab⟩ := hC (A' ⊓ B') A'' B'' (inf_le_inf hA hB) hsplit (zeroAddEquiv F _ d)
  have e : res F 0 (inf_le_inf hA hB) d = (zeroAddEquiv F _).symm
      (F.obj.map (homOfLE (inf_le_inf hA hB)).op (zeroAddEquiv F _ d)) := by
    rw [← res_zeroAddEquiv_symm, AddEquiv.symm_apply_apply]
  rw [e, hab]
  exact δ_zeroAddEquiv_symm_sub a b

/-- If a class on `A' ∩ B'` is compactly zero there and `A'' ∩ B''` has compact closure in
`A' ∩ B'`, then the Mayer–Vietoris connecting map of `(A'', B'')` kills its restriction. -/
lemma δ_res_eq_zero_of_compactlyZero {q : ℕ} {d : CategoryTheory.Sheaf.H'.{u} F q (A' ⊓ B')}
    (hd : CompactlyZero F d (A' ⊓ B' : Opens 𝕏))
    (hc : IsCompact (closure ((A'' ⊓ B'' : Opens 𝕏) : Set (ι → ℂ))))
    (hcl : closure ((A'' ⊓ B'' : Opens 𝕏) : Set (ι → ℂ)) ⊆ (A' ⊓ B' : Opens 𝕏)) :
    δ A'' B'' F q (res F q (inf_le_inf hA hB) d) = 0 := by
  rw [hd.2 _ _ hc hcl, map_zero]

end Merge

/-- **The merge lemma.** Let `A, B` be Cousin-shrinkable and `c ∈ H'ᵠ⁺¹(U)` compactly zero on `A`
and on `B`. Then `c` is compactly zero on `A ∪ B`, provided sections of `F` split (`q = 0`) or
classes of degree `q` on products of holed rectangles are compactly zero (`q ≥ 1`). -/
theorem compactlyZero_union {q : ℕ} {U : Opens 𝕏}
    {c : CategoryTheory.Sheaf.H'.{u} F (q + 1) U} {A B : Set (ι → ℂ)}
    (hAB : CousinShrinkable A B) (hA : CompactlyZero F c A) (hB : CompactlyZero F c B)
    (hC : q = 0 → CousinSplitting F) (hZ : 0 < q → CompactlyZeroOnProd F q) :
    CompactlyZero F c (A ∪ B) := by
  refine ⟨union_subset hA.1 hB.1, fun V hV hVc hVAB ↦ ?_⟩
  obtain ⟨A', B', A'', B'', hA'o, hB'o, hA''o, hB''o, hA'c, hA'A, hB'c, hB'B, hA''A', hB''B',
    hK, ⟨s', hs'⟩, hsplit⟩ := hAB _ hVc hVAB
  obtain ⟨oA', rfl⟩ : ∃ o : Opens 𝕏, (o : Set (ι → ℂ)) = A' := ⟨⟨A', hA'o⟩, rfl⟩
  obtain ⟨oB', rfl⟩ : ∃ o : Opens 𝕏, (o : Set (ι → ℂ)) = B' := ⟨⟨B', hB'o⟩, rfl⟩
  obtain ⟨oA'', rfl⟩ : ∃ o : Opens 𝕏, (o : Set (ι → ℂ)) = A'' := ⟨⟨A'', hA''o⟩, rfl⟩
  obtain ⟨oB'', rfl⟩ : ∃ o : Opens 𝕏, (o : Set (ι → ℂ)) = B'' := ⟨⟨B'', hB''o⟩, rfl⟩
  have hA'U : oA' ≤ U := fun x hx ↦ hA.1 (hA'A (subset_closure hx))
  have hB'U : oB' ≤ U := fun x hx ↦ hB.1 (hB'B (subset_closure hx))
  have hA''A'le : oA'' ≤ oA' := fun x hx ↦ hA''A' (subset_closure hx)
  have hB''B'le : oB'' ≤ oB' := fun x hx ↦ hB''B' (subset_closure hx)
  have hWU : oA' ⊔ oB' ≤ U := sup_le hA'U hB'U
  have hVW : V ≤ oA'' ⊔ oB'' := fun x hx ↦ hK (subset_closure hx)
  -- `c` restricted to `A' ∪ B'` is a Mayer–Vietoris boundary
  obtain ⟨d, hd⟩ : ∃ d, δ oA' oB' F q d = res F (q + 1) hWU c := by
    refine ((exact_δ_toProd oA' oB' F q) (res F (q + 1) hWU c)).1 ?_
    rw [toProd_apply, res_comp, res_comp, hA.2 oA' _ hA'c hA'A, hB.2 oB' _ hB'c hB'B]
    rfl
  -- its restriction to `A'' ∩ B''` is killed by the connecting map
  have hδ : δ oA'' oB'' F q (res F q (inf_le_inf hA''A'le hB''B'le) d) = 0 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact δ_res_eq_zero_of_cousinSplitting hA''A'le hB''B'le (hC rfl) (fun g hg ↦ hsplit g hg) d
    · refine δ_res_eq_zero_of_compactlyZero hA''A'le hB''B'le (hZ hq s' (oA' ⊓ oB') hs' d) ?_ ?_
      · exact (hA'c.of_isClosed_subset isClosed_closure
          ((closure_mono inter_subset_left).trans (hA''A'.trans subset_closure)))
      · exact (closure_inter_subset_inter_closure _ _).trans (inter_subset_inter hA''A' hB''B')
  have hc0 : res F (q + 1) (sup_le_sup hA''A'le hB''B'le) (res F (q + 1) hWU c) = 0 := by
    refine (congrArg (res F (q + 1) (sup_le_sup hA''A'le hB''B'le)) hd.symm).trans ?_
    exact (δ_naturality hA''A'le hB''B'le F d).symm.trans hδ
  have := congrArg (res F (q + 1) hVW) hc0
  rwa [res_comp, res_comp, map_zero] at this

/-- Classes of positive degree vanish near every point: the local hypothesis of merging. -/
lemma exists_mem_nhds_compactlyZero {q : ℕ} {U : Opens 𝕏}
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) U) {x : ι → ℂ} (hx : x ∈ (U : Set (ι → ℂ))) :
    ∃ W ∈ {W | CompactlyZero F c W}, W ∈ nhds x := by
  obtain ⟨V, hVU, hxV, hV⟩ := TopCat.Sheaf.exists_H'res_eq_zero F q c hx
  exact ⟨V, compactlyZero_of_res_eq_zero hVU hV, V.isOpen.mem_nhds hxV⟩

/-- **Merging along grids.** A class of positive degree on `U` is compactly zero on every product
of holed rectangles whose closure lies in `U`, provided sections of `F` split (degree one) or
classes one degree lower on products of holed rectangles are compactly zero. -/
theorem compactlyZero_prod [Finite ι] {q : ℕ} (hC : q = 0 → CousinSplitting F)
    (hZ : 0 < q → CompactlyZeroOnProd F q) {U : Opens 𝕏}
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) U) (s₀ : ι → HoledRect)
    (hs₀ : closure (prod s₀) ⊆ (U : Set (ι → ℂ))) :
    CompactlyZero F c (prod s₀) := by
  classical
  cases nonempty_fintype ι
  refine mem_of_merge {W | CompactlyZero F c W} compactlyZero_empty
    (fun W hW W' hW' ↦ CompactlyZero.mono hW hW') ?_ ?_ s₀
    fun x hx ↦ exists_mem_nhds_compactlyZero c (hs₀ hx)
  · intro s i t δ hδ h0 h1 hhole hA hB
    rw [← prod_cutRe_union s i hδ h0 h1]
    exact compactlyZero_union (cousinShrinkable_cutRe s i hδ h0 h1 hhole) hA hB hC hZ
  · intro s i t δ hδ h0 h1 hhole hA hB
    rw [← prod_cutIm_union s i hδ h0 h1]
    exact compactlyZero_union (cousinShrinkable_cutIm s i hδ h0 h1 hhole) hA hB hC hZ

/-- A class is compactly zero on `S ⊆ U` if every compact subset of `S` lies in a product of holed
rectangles with closure in `S` on which the class is compactly zero. -/
lemma compactlyZero_of_forall_prod {q : ℕ} {U : Opens 𝕏}
    {c : CategoryTheory.Sheaf.H'.{u} F q U} {S : Set (ι → ℂ)} (hSU : S ⊆ U)
    (hK : ∀ K, IsCompact K → K ⊆ S → ∃ s₀, K ⊆ prod s₀ ∧ closure (prod s₀) ⊆ S)
    (h : ∀ s₀, closure (prod s₀) ⊆ (U : Set (ι → ℂ)) → CompactlyZero F c (prod s₀)) :
    CompactlyZero F c S := by
  refine ⟨hSU, fun V hV hc hVS ↦ ?_⟩
  obtain ⟨s₀, hKs, hs₀⟩ := hK _ hc hVS
  exact (h s₀ (hs₀.trans hSU)).2 V hV hc hKs

/-- Compact subsets of a product of holed rectangles lie in a shrinking. -/
lemma exists_prod_of_isCompact_subset_prod [Finite ι] (s : ι → HoledRect) (K : Set (ι → ℂ))
    (hK : IsCompact K) (hKs : K ⊆ prod s) :
    ∃ s₀, K ⊆ prod s₀ ∧ closure (prod s₀) ⊆ prod s := by
  obtain ⟨ε, hε, hKε⟩ := exists_subset_prod_shrink hK hKs
  exact ⟨_, hKε, closure_prod_shrink_subset hε s⟩

/-- **(Z_q) on products**: if sections of `F` split, then for `q ≥ 1` every class of degree `q`
on a product of holed rectangles is compactly zero on it. -/
theorem compactlyZeroOnProd [Finite ι] (hC : CousinSplitting F) (q : ℕ) :
    CompactlyZeroOnProd F (q + 1) := by
  induction q with
  | zero =>
    intro s U hU c
    refine compactlyZero_of_forall_prod subset_rfl ?_ fun s₀ hs₀ ↦
      compactlyZero_prod (fun _ ↦ hC) (fun h ↦ absurd h (lt_irrefl 0)) c s₀ hs₀
    rw [hU]
    exact exists_prod_of_isCompact_subset_prod s
  | succ q ih =>
    intro s U hU c
    refine compactlyZero_of_forall_prod subset_rfl ?_ fun s₀ hs₀ ↦
      compactlyZero_prod (fun h ↦ absurd h q.succ_ne_zero) (fun _ ↦ ih) c s₀ hs₀
    rw [hU]
    exact exists_prod_of_isCompact_subset_prod s

/-- **(Z_q) on `(ℂ^×)^P × ℂ^{ι \ P}`**: if sections of `F` split, then for `q ≥ 1` every class
of degree `q` on `D = (ℂ^×)^P × ℂ^{ι \ P}` is compactly zero on it. -/
theorem compactlyZero_puncturedSet [Finite ι] (hC : CousinSplitting F) {P : Set ι} {U : Opens 𝕏}
    (hU : (U : Set (ι → ℂ)) = puncturedSet P) {q : ℕ}
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) U) : CompactlyZero F c U := by
  refine compactlyZero_of_forall_prod subset_rfl ?_ fun s₀ hs₀ ↦ ?_
  · rw [hU]
    exact fun K hK hKP ↦ exists_prod_of_isCompact P hK hKP
  · rcases q with _ | q
    · exact compactlyZero_prod (fun _ ↦ hC) (fun h ↦ absurd h (lt_irrefl 0)) c s₀ hs₀
    · exact compactlyZero_prod (fun h ↦ absurd h q.succ_ne_zero)
        (fun _ ↦ compactlyZeroOnProd hC q) c s₀ hs₀

/-- The exhaustion `prod (Complex.exhaustion P n)` of `(ℂ^×)^P × ℂ^{ι \ P}`, as opens. -/
def exhaustionOpens [Finite ι] [DecidableEq ι] (P : Finset ι) (n : ℕ) : Opens 𝕏 :=
  ⟨prod (exhaustion P n), isOpen_prod _⟩

lemma monotone_exhaustionOpens [Finite ι] [DecidableEq ι] (P : Finset ι) :
    Monotone (exhaustionOpens (ι := ι) P) :=
  fun _ _ h ↦ monotone_exhaustion P h

lemma iSup_exhaustionOpens [Finite ι] [DecidableEq ι] (P : Finset ι) :
    ((⨆ n, exhaustionOpens (ι := ι) P n : Opens 𝕏) : Set (ι → ℂ)) = puncturedSet (P : Set ι) := by
  rw [Opens.coe_iSup]
  exact iUnion_exhaustion P

/-- **Theorem B on `(ℂ^×)^P × ℂ^{ι \ P}`.** If sections of `F` split along Cousin splittings of
holomorphic functions and `lim¹ F = 0` along the standard exhaustion, then
`H'ᵠ(D, F) = 0` for `q ≥ 1` and `D = (ℂ^×)^P × ℂ^{ι \ P}`. -/
theorem eq_zero_of_eq_puncturedSet [Finite ι] [DecidableEq ι] (hC : CousinSplitting F)
    (hML : MittagLefflerExhaustion F) (P : Finset ι) {D : Opens 𝕏}
    (hD : (D : Set (ι → ℂ)) = puncturedSet (P : Set ι)) {q : ℕ}
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) D) : c = 0 := by
  set U := exhaustionOpens (ι := ι) P
  have hU : Monotone U := monotone_exhaustionOpens P
  obtain rfl : ⨆ n, U n = D := Opens.ext ((iSup_exhaustionOpens P).trans hD.symm)
  have hc : ∀ n, TopCat.Sheaf.H'res F (q + 1) (le_iSup U n) c = 0 := fun n ↦
    (compactlyZero_puncturedSet hC hD c).2 (U n) (le_iSup U n)
      (closure_exhaustion_subset P n).2
      ((closure_exhaustion_subset P n).1.trans fun _ hx ↦ le_iSup U (n + 1) hx)
  rcases q with _ | q
  · exact TopCat.Sheaf.H'_one_eq_zero_of_monotone hU F (hML P U hU fun _ ↦ rfl) c hc
  · refine TopCat.Sheaf.H'_eq_zero_of_monotone hU F (q + 1)
      (TopCat.Sheaf.LimOneVanishes.of_eq_zero fun n ↦ ?_) c hc
    ext x
    exact (compactlyZeroOnProd hC q (exhaustion P (n + 1)) (U (n + 1)) rfl x).2 (U n)
      (hU n.le_succ) (closure_exhaustion_subset P n).2 (closure_exhaustion_subset P n).1

end Complex.TheoremB

end
