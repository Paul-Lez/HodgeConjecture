/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreSurjectivitySkeleton
import KirovDolbeault.Dolbeault.SerreCupProduct
import KirovDolbeault.Dolbeault.CohomologicalRR

/-!
# Forster §17.8 — the `ψ`-action and its injectivity

This file CONSTRUCTS the `ψ`-action of the §17.9 surjectivity count and PROVES Forster's
Lemma 17.8 (injectivity for `λ ≠ 0`), inhabiting the `psiAct` / `psiAct_injective` fields of
`SurjectivityInputs` (`SerreSurjectivitySkeleton.lean`).

## The construction

For `ψ ∈ L(nP) = lSysModule (single P n)`, multiplication by `ψ` maps `𝒪_{D−nP}`-cochains to
`𝒪_D`-cochains (the order bound `div ψ ≥ −nP` cancels the extra poles), inducing
`ψ· : H¹(𝒪_{D−nP}) → H¹(𝒪_D)`.  This is EXACTLY the proven cup product
`cup (D−nP) D : lSysModule (D − (D−nP)) →ₗ (cechH1 (D−nP) →ₗ cechH1 D)`
(`SerreCupProduct.lean`), transported along `D − (D − nP) = nP` (`lSysCongr`).  Dualizing,

  `psiAct lam n : ψ ↦ lam ∘ (ψ·) : L(nP) →ₗ[ℂ] (H¹(𝒪_{D−nP}))*`,

ℂ-linear in `ψ` by construction (the cup product is bilinear).

## The injectivity proof (Forster 17.8)

For `lam ≠ 0` and `ψ ≠ 0`, `ψ·lam = lam ∘ (ψ·) ≠ 0` because **multiplication by a nonzero `ψ`
is SURJECTIVE on `H¹`** (`cupH1_surjective`).  The classical factorization: with `E := D' − div ψ`
(where `ψ ∈ L(K' − D')`, here `D' = D − nP`, `K' = D`),

* `ψ· : H¹(𝒪_{D'}) → H¹(𝒪_E)` is split-surjective — the germ-level inverse `1/ψ` multiplies
  `𝒪_E`-cochains back into `𝒪_{D'}`-cochains (order additivity is an equality), and
  `ψ·(1/ψ)·c = c` as `MGerm`s because the zero set of `ψ` is codiscrete (the identity theorem
  `orderW_ne_top_of_exists`: a germ-nonzero meromorphic function on the connected `X` has
  isolated zeros);
* the inclusion `H¹(𝒪_E) → H¹(𝒪_{K'})` (`E ≤ K'` since `div ψ ≥ D' − K'`) is surjective by the
  ITERATED skyscraper LES: each single-point jump `H¹(𝒪_F) → H¹(𝒪_{F+P})` is surjective
  (`surj₄` of `exists_skyscraperLES`, `CohomologicalRR.lean`), and `K' − E` is effective, so
  induction on `deg (K' − E)` exhausts the gap (`h1InclMono_surjective`).

## Main declarations

* `FiniteCover.h1InclMono` / `h1InclMono_surjective` — the monotone inclusion
  `H¹(𝒪_{D₁}) → H¹(𝒪_{D₂})` for `D₁ ≤ D₂` pointwise, surjective (iterated `surj₄`).
* `cupH1_surjective` / `cup_surjective_of_ne_zero` — multiplication by a germ-nonzero `f` is
  surjective on `H¹`.
* `FiniteCover.psiMul` — the multiplication map `L(nP) →ₗ (H¹(𝒪_{D−nP}) →ₗ H¹(𝒪_D))`.
* `FiniteCover.psiAct` — the §17.8 action `ψ ↦ lam ∘ (ψ·)`, matching the `SurjectivityInputs.psiAct`
  field type exactly.
* `FiniteCover.psiAct_injective` — **Forster 17.8**: injective for `lam ≠ 0` (needs
  `hR : 𝔘.LocallyRealizable` for the skyscraper LES).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.8–17.9.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MeromorphicFunction

/-! ## Part 0 — the divisor reads off the order

The reciprocal `f⁻¹` (with `inv_toFun` / `orderW_inv`) is already provided by
`SerreResidueRamifiedRealCover.lean`; here we only add the `div`/`orderW` bridge. -/

/-- The divisor of `f` reads off the (untopped) order: `div f x = (orderW f x).untop₀`. -/
theorem div_apply (f : MeromorphicFunction X) (x : X) :
    MeromorphicFunction.div X f x = (f.orderW x).untop₀ := by
  have h : MeromorphicFunction.div X f
      = Finsupp.ofSupportFinite (MeromorphicFunction.orderAtPoint f)
        ((MeromorphicFunction.orderLocallyFinsupp f).finiteSupport isCompact_univ) := rfl
  rw [h, Finsupp.ofSupportFinite_coe]
  rfl

/-- For a germ-nonzero `f` (`orderW` never `⊤`), the order IS the divisor coefficient. -/
theorem coe_div_eq_orderW {f : MeromorphicFunction X} (hne : ∀ x, f.orderW x ≠ ⊤) (x : X) :
    ((MeromorphicFunction.div X f x : ℤ) : WithTop ℤ) = f.orderW x := by
  rw [div_apply, WithTop.coe_untop₀_of_ne_top (hne x)]

end MeromorphicFunction

namespace Dolbeault

/-! ## Part 1 — the germ-level inverse: `globalGerm f U * globalGerm f.inv U = 1`

The zero set of a germ-nonzero meromorphic `f` is codiscrete (isolated zeros, by the identity
theorem on the connected `X`), so `f · (1/f) = 1` holds as `MGerm`s on every open. -/

/-- For a germ-nonzero `f`, the set where `f.toFun ≠ 0` is codiscrete in every open `U`
(zeros are isolated; transferred to the subtype along the open inclusion). -/
theorem ne_zero_mem_codiscrete {f : MeromorphicFunction X} (hne : ∀ x, f.orderW x ≠ ⊤)
    (U : Opens X) :
    {u : U | f.toFun u.1 ≠ 0} ∈ Filter.codiscreteWithin (Set.univ : Set U) := by
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro u _
  rw [Set.compl_univ, Set.union_empty]
  have hX : ∀ᶠ z in 𝓝[≠] u.1, f.toFun z ≠ 0 :=
    (f.orderW_ne_top_iff u.1).mp (hne u.1)
  have htend : Filter.Tendsto (Subtype.val : U → X) (𝓝[≠] u) (𝓝[≠] u.1) := by
    refine continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun z hz => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    exact fun hc => hz (Subtype.ext hc)
  exact htend.eventually hX

/-- **The germ-level inverse law**: for a germ-nonzero `f`,
`globalGerm f U * globalGerm f.inv U = 1` in `MGerm U`. -/
theorem globalGerm_mul_inv {f : MeromorphicFunction X} (hne : ∀ x, f.orderW x ≠ ⊤)
    (U : Opens X) :
    globalGerm f U * globalGerm f⁻¹ U = 1 := by
  have hkey : ((f.toFun ∘ Subtype.val) * ((f⁻¹).toFun ∘ Subtype.val) : U → ℂ)
      =ᶠ[Filter.codiscreteWithin (Set.univ : Set U)] (1 : U → ℂ) := by
    filter_upwards [ne_zero_mem_codiscrete hne U] with u hu
    simp only [Pi.mul_apply, Function.comp_apply, Pi.one_apply,
      MeromorphicFunction.inv_toFun, Pi.inv_apply]
    exact mul_inv_cancel₀ hu
  calc globalGerm f U * globalGerm f⁻¹ U
      = (((f.toFun ∘ Subtype.val) * ((f⁻¹).toFun ∘ Subtype.val) : U → ℂ) : MGerm U) := rfl
    _ = ((1 : U → ℂ) : MGerm U) := Filter.Germ.coe_eq.mpr hkey
    _ = 1 := rfl

/-! ## Part 2 — effective-divisor degree bookkeeping -/

private theorem deg_nonneg_of_le {E D : Divisor X} (h : ∀ x, E x ≤ D x) :
    0 ≤ Divisor.deg X (D - E) := by
  rw [show Divisor.deg X (D - E) = ∑ x ∈ (D - E).support, (D - E) x from
    Finsupp.degree_apply _]
  refine Finset.sum_nonneg fun x _ => ?_
  rw [Finsupp.sub_apply]
  have := h x
  omega

private theorem eq_of_le_of_deg_sub_eq_zero {E D : Divisor X} (h : ∀ x, E x ≤ D x)
    (hdeg : Divisor.deg X (D - E) = 0) : E = D := by
  have hsum : ∑ x ∈ (D - E).support, (D - E) x = 0 := by
    rw [← Finsupp.degree_apply]; exact hdeg
  have hz : ∀ x ∈ (D - E).support, (D - E) x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun x _ => by
      rw [Finsupp.sub_apply]; have := h x; omega).mp hsum
  have h0 : D - E = 0 := by
    ext x
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hx : x ∈ (D - E).support
    · exact hz x hx
    · exact Finsupp.notMem_support_iff.mp hx
  exact (sub_eq_zero.mp h0).symm

/-! ## Part 3 — the monotone inclusion `H¹(𝒪_{D₁}) → H¹(𝒪_{D₂})` (`D₁ ≤ D₂`) and its
surjectivity (the iterated skyscraper LES)

Generalizes the single-point order-weakening layer of `SkyscraperLESBase` from `D ↦ D + P` to an
arbitrary pointwise inequality `D₁ ≤ D₂`. -/

namespace FiniteCover

open FiniteFamily

/-- The order bound for `𝒪_{D₁}` implies that for `𝒪_{D₂}` when `D₁ ≤ D₂` pointwise. -/
theorem mem_OmegaD_of_le {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) {U : Opens X} {f : U → ℂ}
    (hf : f ∈ OmegaD D₁ U) : f ∈ OmegaD D₂ U := by
  refine ⟨hf.1, fun u => le_trans ?_ (hf.2 u)⟩
  exact_mod_cast neg_le_neg (h u.1)

/-- Germ-class sections inherit the monotone inclusion. -/
theorem OmegaDGerm_le_of_le {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) (U : Opens X) :
    OmegaDGerm D₁ U ≤ OmegaDGerm D₂ U := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, mem_OmegaD_of_le h hg, rfl⟩

/-- 0-sections are monotone in the divisor. -/
theorem sections0_le_of_le (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) :
    𝔘.sections0 D₁ ≤ 𝔘.sections0 D₂ :=
  fun _ hf i => OmegaDGerm_le_of_le h (𝔘.U i) (hf i)

/-- 1-sections are monotone in the divisor. -/
theorem sections1_le_of_le (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) :
    𝔘.sections1 D₁ ≤ 𝔘.sections1 D₂ :=
  fun _ hf p => OmegaDGerm_le_of_le h _ (hf p)

/-- 1-cocycles are monotone in the divisor. -/
theorem cocycles1_le_of_le (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) :
    𝔘.cocycles1 D₁ ≤ 𝔘.cocycles1 D₂ :=
  inf_le_inf_left _ (𝔘.sections1_le_of_le h)

/-- 1-coboundaries are monotone in the divisor. -/
theorem coboundaries1_le_of_le (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) :
    𝔘.coboundaries1 D₁ ≤ 𝔘.coboundaries1 D₂ :=
  Submodule.map_mono (𝔘.sections0_le_of_le h)

/-- The monotone 1-cocycle inclusion `Z¹(𝒪_{D₁}) ↪ Z¹(𝒪_{D₂})`. -/
noncomputable def cocyclesInclMono (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X}
    (h : ∀ x, D₁ x ≤ D₂ x) :
    ↥(𝔘.cocycles1 D₁) →ₗ[ℂ] ↥(𝔘.cocycles1 D₂) :=
  Submodule.inclusion (𝔘.cocycles1_le_of_le h)

@[simp] theorem cocyclesInclMono_coe (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X}
    (h : ∀ x, D₁ x ≤ D₂ x) (c : ↥(𝔘.cocycles1 D₁)) :
    (𝔘.cocyclesInclMono h c : 𝔘.Cochain1) = (c : 𝔘.Cochain1) := rfl

/-- **The monotone inclusion-induced arrow `H¹(𝒪_{D₁}) → H¹(𝒪_{D₂})`** for `D₁ ≤ D₂` pointwise
(the multi-point generalization of `h1Map`). -/
noncomputable def h1InclMono (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X}
    (h : ∀ x, D₁ x ≤ D₂ x) :
    𝔘.cechH1 D₁ →ₗ[ℂ] 𝔘.cechH1 D₂ := by
  refine Submodule.mapQ _ _ (𝔘.cocyclesInclMono h) ?_
  rintro ⟨c, _⟩ hcob
  exact 𝔘.coboundaries1_le_of_le h hcob

theorem h1InclMono_mk (𝔘 : FiniteCover X) {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x)
    (c : ↥(𝔘.cocycles1 D₁)) :
    𝔘.h1InclMono h (Submodule.Quotient.mk c)
      = Submodule.Quotient.mk (𝔘.cocyclesInclMono h c) := rfl

/-- Monotone inclusions compose. -/
theorem h1InclMono_comp (𝔘 : FiniteCover X) {D₁ D₂ D₃ : Divisor X}
    (h₁ : ∀ x, D₁ x ≤ D₂ x) (h₂ : ∀ x, D₂ x ≤ D₃ x) :
    (𝔘.h1InclMono h₂).comp (𝔘.h1InclMono h₁)
      = 𝔘.h1InclMono (fun x => (h₁ x).trans (h₂ x)) := by
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [LinearMap.comp_apply, 𝔘.h1InclMono_mk h₁, 𝔘.h1InclMono_mk h₂, 𝔘.h1InclMono_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- The single-point monotone inclusion IS `h1Map` (same `mapQ` of the same submodule
inclusion; proof-irrelevant). -/
theorem h1InclMono_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.h1InclMono (divisor_le_add_single D P) = 𝔘.h1Map D P := by
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rfl

/-- **Surjectivity of the monotone inclusion `H¹(𝒪_{D₁}) → H¹(𝒪_{D₂})` (iterated skyscraper
LES).**  Induction on `deg (D₂ − D₁) ≥ 0`: each single-point step is `surj₄` of
`exists_skyscraperLES` (the skyscraper sheaf has `H¹ = 0`). -/
theorem h1InclMono_surjective (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    {E D : Divisor X} (hED : ∀ x, E x ≤ D x) :
    Function.Surjective (𝔘.h1InclMono hED) := by
  suffices H : ∀ (n : ℕ) (E : Divisor X) (hED : ∀ x, E x ≤ D x),
      Divisor.deg X (D - E) = (n : ℤ) → Function.Surjective (𝔘.h1InclMono hED) by
    exact H (Divisor.deg X (D - E)).toNat E hED
      (Int.toNat_of_nonneg (deg_nonneg_of_le hED)).symm
  intro n
  induction n with
  | zero =>
    intro E hED hn
    obtain rfl : E = D := eq_of_le_of_deg_sub_eq_zero hED (by exact_mod_cast hn)
    intro ξ
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [𝔘.h1InclMono_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)
  | succ n ih =>
    intro E hED hn
    -- find a point where the gap is positive
    obtain ⟨a, ha⟩ : ∃ a, E a < D a := by
      by_contra hc
      simp only [not_exists, not_lt] at hc
      have hED' : E = D := by
        ext x
        exact le_antisymm (hED x) (hc x)
      rw [hED', sub_self, Divisor.deg_zero] at hn
      omega
    -- one single-point step
    have h₂ : ∀ x, (E + Finsupp.single a 1 : Divisor X) x ≤ D x := by
      classical
      intro x
      rw [Finsupp.add_apply, Finsupp.single_apply]
      by_cases hx : a = x
      · subst hx
        rw [if_pos rfl]
        omega
      · rw [if_neg hx, add_zero]
        exact hED x
    have hdeg' : Divisor.deg X (D - (E + Finsupp.single a 1)) = (n : ℤ) := by
      rw [sub_add_eq_sub_sub, Divisor.deg_sub, hn, Divisor.deg_single]
      push_cast
      ring
    -- step surjectivity from the skyscraper LES
    obtain ⟨S⟩ := exists_skyscraperLES 𝔘 hR E a
    have hstep : Function.Surjective (𝔘.h1InclMono (divisor_le_add_single E a)) := by
      rw [𝔘.h1InclMono_single E a]
      exact S.surj₄
    -- compose
    have heq : 𝔘.h1InclMono hED
        = (𝔘.h1InclMono h₂).comp (𝔘.h1InclMono (divisor_le_add_single E a)) :=
      (𝔘.h1InclMono_comp (divisor_le_add_single E a) h₂).symm
    rw [heq, LinearMap.coe_comp]
    exact (ih (E + Finsupp.single a 1) h₂ hdeg').comp hstep

end FiniteCover

/-! ## Part 4 — multiplication by a germ-nonzero `f` is surjective on `H¹` -/

/-- **Multiplication by a germ-nonzero `f ∈ L(K−D)` is surjective on `H¹`** (the key input of
Forster 17.8).  Factorization: with `E := D − div f ≤ K`, any class in `H¹(𝒪_K)` is represented
by an `𝒪_E`-cocycle (`h1InclMono_surjective`, iterated skyscraper), and `c ↦ (1/f)·c` lifts it
to `H¹(𝒪_D)` — `f·(1/f)·c = c` as germs (`globalGerm_mul_inv`). -/
theorem cupH1_surjective (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) (hf0 : ∃ x, f.orderW x ≠ ⊤) :
    Function.Surjective (cupH1 (𝔘 := 𝔘.toFiniteFamily) hf) := by
  have hne : ∀ x, f.orderW x ≠ ⊤ := f.orderW_ne_top_of_exists hf0
  -- the divisor bound `div f ≥ D − K` from `f ∈ L(K−D)`
  have hdivf : ∀ x, D x - K x ≤ MeromorphicFunction.div X f x := by
    intro x
    have h1 := hf x
    rw [← MeromorphicFunction.coe_div_eq_orderW hne x] at h1
    have h2 : -((K - D : Divisor X) x) ≤ MeromorphicFunction.div X f x := by
      exact_mod_cast h1
    rw [Finsupp.sub_apply] at h2
    omega
  -- the intermediate level `E := D − div f ≤ K`
  have hEK : ∀ x, (D - MeromorphicFunction.div X f : Divisor X) x ≤ K x := by
    intro x
    rw [Finsupp.sub_apply]
    have := hdivf x
    omega
  -- the reciprocal multiplies `𝒪_E` back into `𝒪_D`
  have hinv : f⁻¹ ∈ linearSystem (X := X) (D - (D - MeromorphicFunction.div X f)) := by
    intro x
    rw [sub_sub_cancel, MeromorphicFunction.orderW_inv,
      ← MeromorphicFunction.coe_div_eq_orderW hne x]
  intro ξ
  obtain ⟨ζ, hζ⟩ := 𝔘.h1InclMono_surjective hR hEK ξ
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ζ
  refine ⟨cupH1 hinv (Submodule.Quotient.mk c), ?_⟩
  rw [cupH1_mk, cupH1_mk, ← hζ, 𝔘.h1InclMono_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  funext p
  simp only [cupCocyclesMap_coe, cupCochain1_apply, FiniteCover.cocyclesInclMono_coe]
  rw [← mul_assoc, globalGerm_mul_inv hne, one_mul]

/-- **Multiplication by a nonzero junk-free class is surjective on `H¹`** (`cup`-level form of
`cupH1_surjective`: a nonzero element of `lSysModule (K−D)` has a germ-nonzero representative). -/
theorem cup_surjective_of_ne_zero (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (D K : Divisor X) (φ : lSysModule (X := X) (K - D)) (hφ : φ ≠ 0) :
    Function.Surjective (cup (𝔘 := 𝔘.toFiniteFamily) D K φ) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ φ
  have hf0 : ∃ x, (f : MeromorphicFunction X).orderW x ≠ ⊤ := by
    by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    exact hφ ((Submodule.Quotient.mk_eq_zero _).mpr fun x => hc x)
  intro ξ
  obtain ⟨η, hη⟩ := cupH1_surjective 𝔘 hR f.2 hf0 ξ
  exact ⟨η, by rw [cup_mk]; exact hη⟩

/-! ## Part 5 — the ψ-action and Forster 17.8 -/

/-- Transport of the junk-free linear system along an equality of divisors. -/
noncomputable def lSysCongr {D₁ D₂ : Divisor X} (h : D₁ = D₂) :
    lSysModule (X := X) D₁ ≃ₗ[ℂ] lSysModule (X := X) D₂ := by
  subst h
  exact LinearEquiv.refl ℂ _

namespace FiniteCover

/-- **The §17.8 multiplication map**: for `ψ ∈ L(nP)`, multiplication of Čech cochains by `ψ`
induces `ψ· : H¹(𝒪_{D−nP}) → H¹(𝒪_D)`; bundled ℂ-linearly in `ψ`.  This IS the proven cup
product `cup (D−nP) D` transported along `D − (D − nP) = nP`. -/
noncomputable def psiMul (𝔘 : FiniteCover X) (D : Divisor X) (P : X) (n : ℕ) :
    lSysModule (X := X) (Finsupp.single P (n : ℤ)) →ₗ[ℂ]
      (𝔘.cechH1 (D - Finsupp.single P (n : ℤ)) →ₗ[ℂ] 𝔘.cechH1 D) :=
  (cup (𝔘 := 𝔘.toFiniteFamily) (D - Finsupp.single P (n : ℤ)) D).comp
    (lSysCongr (sub_sub_cancel D (Finsupp.single P (n : ℤ))).symm).toLinearMap

@[simp] theorem psiMul_apply (𝔘 : FiniteCover X) (D : Divisor X) (P : X) (n : ℕ)
    (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ))) :
    𝔘.psiMul D P n ψ
      = cup (𝔘 := 𝔘.toFiniteFamily) (D - Finsupp.single P (n : ℤ)) D
          (lSysCongr (sub_sub_cancel D (Finsupp.single P (n : ℤ))).symm ψ) := rfl

/-- Multiplication by a NONZERO `ψ ∈ L(nP)` is surjective on `H¹` (the iterated-skyscraper
input of Forster 17.8). -/
theorem psiMul_surjective (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (D : Divisor X) (P : X) (n : ℕ)
    (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ))) (hψ : ψ ≠ 0) :
    Function.Surjective (𝔘.psiMul D P n ψ) := by
  rw [psiMul_apply]
  refine cup_surjective_of_ne_zero 𝔘 hR _ _ _ ?_
  exact (LinearEquiv.map_ne_zero_iff _).mpr hψ

/-- **The Forster §17.8 ψ-action** `ψ ↦ ψ·lam := lam ∘ (ψ·)`, as an ℂ-linear map
`L(nP) →ₗ[ℂ] (H¹(𝒪_{D−nP}))*` — exactly the `SurjectivityInputs.psiAct` field type. -/
noncomputable def psiAct (𝔘 : FiniteCover X) (D : Divisor X) (P : X)
    (lam : Module.Dual ℂ (𝔘.cechH1 D)) (n : ℕ) :
    lSysModule (X := X) (Finsupp.single P (n : ℤ)) →ₗ[ℂ]
      Module.Dual ℂ (𝔘.cechH1 (D - Finsupp.single P (n : ℤ))) :=
  (LinearMap.llcomp ℂ (𝔘.cechH1 (D - Finsupp.single P (n : ℤ))) (𝔘.cechH1 D) ℂ lam).comp
    (𝔘.psiMul D P n)

@[simp] theorem psiAct_apply (𝔘 : FiniteCover X) (D : Divisor X) (P : X)
    (lam : Module.Dual ℂ (𝔘.cechH1 D)) (n : ℕ)
    (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ))) :
    𝔘.psiAct D P lam n ψ = lam.comp (𝔘.psiMul D P n ψ) := rfl

/-- **Forster 17.8 — injectivity of the ψ-action.**  For `lam ≠ 0`, `ψ ↦ ψ·lam` is injective on
`L(nP)`: a nonzero `ψ` multiplies SURJECTIVELY on `H¹` (`psiMul_surjective`), so
`lam ∘ (ψ·) = 0` would force `lam = 0`. -/
theorem psiAct_injective (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (D : Divisor X) (P : X) (lam : Module.Dual ℂ (𝔘.cechH1 D)) (hlam : lam ≠ 0) (n : ℕ) :
    Function.Injective (𝔘.psiAct D P lam n) := by
  refine (injective_iff_map_eq_zero _).mpr fun ψ hψ => ?_
  by_contra hψ0
  refine hlam (LinearMap.ext fun ξ => ?_)
  obtain ⟨η, rfl⟩ := 𝔘.psiMul_surjective hR D P n ψ hψ0 ξ
  have h := DFunLike.congr_fun hψ η
  simpa using h

end FiniteCover

/-! ## Statement gate — the `SurjectivityInputs` slots

A `SurjectivityInputs R D` can be partially assembled from `psiAct` + `psiAct_injective`
(the `unwind` field — Forster 17.7, step S5 — is taken as a hypothesis). -/

example {𝔘 : FiniteCover X} {K : Divisor X} (R : SerreResidueRealization 𝔘 K)
    (D : Divisor X) (P : X) (hR : 𝔘.LocallyRealizable)
    (unwind : ∀ lam : Module.Dual ℂ (𝔘.cechH1 D), lam ≠ 0 →
      ∀ (n : ℕ) (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ)))
        (w : lSysModule (X := X) (K - (D - Finsupp.single P (n : ℤ)))),
        ψ ≠ 0 → 𝔘.psiAct D P lam n ψ = R.pairing (D - Finsupp.single P (n : ℤ)) w →
        lam ∈ Set.range (R.pairing D)) :
    SurjectivityInputs R D :=
  { P := P
    psiAct := fun lam n => 𝔘.psiAct D P lam n
    psiAct_injective := fun lam hlam n => 𝔘.psiAct_injective hR D P lam hlam n
    unwind := unwind }

end Dolbeault

end Jacobians

end
