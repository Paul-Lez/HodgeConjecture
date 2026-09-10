/-
  Riemann–Roch INTERFACE (the meet-in-the-middle).

  Goal: reduce the headline consumer `exists_singleSimplePole_of_genus_zero` to ONE genuine
  classical input — Riemann–Roch — by PROVING every step in between (no typeclass
  relocation). When the Dolbeault→Serre climb (G2–G4) discharges that single input, the
  headline theorem falls out.

  PROVEN (axiom-clean): the ℂ-module on `MeromorphicFunction X` (so `L(D)` can be a
  `Submodule ℂ`); `linearSystem D` as a `Submodule` + `lDim`.

  POST-FLIP STATUS: there are NO isolated inputs left here. `exists_riemannRoch_divisor`
  is the data-parametrized ladder composition (`riemannRoch_equality_of_data`) at the
  cover EXHIBITED by the unconditional ∃-cover keystone
  (`KeystonePackaging.exists_serreDualityData_cover`). The residue-theorem degree facts
  (`MeromorphicFunction.deg_div`, `lDim_eq_zero_of_deg_neg`) moved verbatim to
  `RiemannRochDegree.lean` (base-file split breaking the
  `KeystonePackaging → … → RiemannRoch` import cycle); they remain in scope here via the
  import.
-/
import KirovDolbeault.Abel
import KirovDolbeault.LinearSystem
import KirovDolbeault.MeromorphicLiouville
import KirovDolbeault.DegDivResidue
import KirovDolbeault.ProperMapDegreeSheets
import KirovDolbeault.RiemannRochDegree
import KirovDolbeault.Dolbeault.DolbeaultLadder
import KirovDolbeault.Dolbeault.LerayCoverExists
import KirovDolbeault.Dolbeault.SkyscraperProductWitness
import KirovDolbeault.Dolbeault.KeystonePackaging

-- Many declarations here are purely algebraic (the ℂ-module on `MeromorphicFunction`) and use
-- only `[ChartedSpace ℂ X]`, not the full compact-manifold hypotheses carried by the consumers.
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]


/-- **Riemann–Roch** (Forster Thm 16.9, Serre-dual form): a canonical divisor `K` with
`l(D) − l(K−D) = deg D + 1 − g` for every `D`.

**Now PROVEN, no isolated input.** The proof takes the cover EXHIBITED by the
unconditional ∃-cover keystone `KeystonePackaging.exists_serreDualityData_cover` (the
T-lane frame-trace construction through the #194 genus split and the #193 capstone) and
applies the data-parametrized ladder composition
`DolbeaultLadder.riemannRoch_equality_of_data` (cohomological RR + the `h⁰=l` bridge +
the bundled Serre duality `data.serre_eq` / `data.arithmeticGenus`). This is the agreed
∃-cover weakening + consumer re-pin (`docs/planning/COVER_WIRING.md`,
`docs/planning/FLIP_CHECKLIST.md`). -/
theorem exists_riemannRoch_divisor :
    ∃ K : Divisor X, ∀ D : Divisor X,
      (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
        = Divisor.deg X D + 1 - (kirovGenus X : ℤ) := by
  -- The keystone EXHIBITS a Leray, locally realizable cover carrying `SerreDualityData`.
  obtain ⟨𝔘, hL, hR, ⟨data⟩⟩ := Dolbeault.exists_serreDualityData_cover (X := X)
  -- The RR equality on that cover is the PROVEN data-parametrized ladder composition.
  exact Dolbeault.riemannRoch_equality_of_data 𝔘 hR data

/-! ## Part 3 (MOVED): `MeromorphicFunction.deg_div` + `lDim_eq_zero_of_deg_neg`

Both moved VERBATIM to `RiemannRochDegree.lean` (base-file split, keystone flip §1.1):
`SerreDualityGenus0` / `TailSerre` / `SerreSurjectivitySkeleton` consume only those two
degree facts from this file, and the flip's `KeystonePackaging` import above would
otherwise close an import cycle through them. They remain in scope here via
`import KirovDolbeault.RiemannRochDegree`. -/

/-! ## Part 4: standard RR consequences (pure arithmetic from RR + `l(0)=1`) -/

/-- `l(K) = g`, from Riemann–Roch at `D = 0` (and `l(0) = 1`). -/
theorem lDim_canonical_eq_genus {K : Divisor X}
    (hrr : ∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
      = Divisor.deg X D + 1 - (kirovGenus X : ℤ)) : lDim (X := X) K = kirovGenus X := by
  have h := hrr 0
  rw [sub_zero, Divisor.deg_zero, lDim_zero_eq_one] at h
  omega

/-- `deg K = 2g − 2`, from Riemann–Roch at `D = K`. -/
theorem deg_canonical {K : Divisor X}
    (hrr : ∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
      = Divisor.deg X D + 1 - (kirovGenus X : ℤ)) : Divisor.deg X K = 2 * (kirovGenus X : ℤ) - 2 := by
  have h := hrr K
  rw [sub_self, lDim_zero_eq_one, lDim_canonical_eq_genus hrr] at h
  omega

/-! ## Part 5: the meet-in-the-middle — discharge the consumer from RR -/

/-- **Touch point.** `kirovGenus X = 0` + Riemann–Roch ⟹ a meromorphic function with a single simple
pole. RR at `D = P` gives `l(P) = 2 > 1 = l(0)`, so `L(P)/germZero` is not spanned by the constant
class; a member outside that span is not germ-constant, hence (by Liouville's contrapositive
`germ_eq_const_of_mem_linearSystem_zero`) has a pole, necessarily a *simple* pole at `P` — the only
pole `L(P)` permits — and by faithfulness its order is finite everywhere. This discharges
`exists_singleSimplePole_of_genus_zero` modulo `{riemannRoch, deg_div}`. -/
theorem exists_singleSimplePole_of_genus_zero_of_rr (hg : kirovGenus X = 0) :
    ∃ (P : X) (f : MeromorphicFunction X), f.HasSingleSimplePole P := by
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  obtain ⟨K, hrr⟩ := exists_riemannRoch_divisor (X := X)
  refine ⟨P, ?_⟩
  set DP : Divisor X := Finsupp.single P 1 with hDP
  have hdegDP : Divisor.deg X DP = 1 := by rw [hDP, Divisor.deg_single]
  -- `l(P) = 2`.
  have hlKDP : lDim (X := X) (K - DP) = 0 := by
    apply lDim_eq_zero_of_deg_neg
    rw [Divisor.deg_sub, deg_canonical hrr, hdegDP, hg]; norm_num
  have hlDP : lDim (X := X) DP = 2 := by
    have h := hrr DP; rw [hlKDP, hdegDP, hg] at h; omega
  -- The constant `1` as a member of `L(P)`, with order `0`.
  have h1m : IsMeromorphic X (fun _ : X => (1 : ℂ)) := fun x => MeromorphicAt.const 1 _
  have horder1 : ∀ x, (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X).orderW x = 0 := by
    intro x
    show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
    rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (1 : ℂ)) from rfl,
      meromorphicOrderAt_const]; simp
  have hmem1 : (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) ∈ linearSystem (X := X) DP := by
    intro x; rw [horder1 x]
    have hge : (0 : ℤ) ≤ DP x := by
      classical rw [hDP, Finsupp.single_apply]; split <;> norm_num
    exact_mod_cast neg_nonpos.mpr hge
  set q1 : ↥(linearSystem (X := X) DP) := ⟨⟨fun _ => 1, h1m⟩, hmem1⟩ with hq1
  -- Work in the quotient `Q := L(P)/germZero`, of dimension `l(P) = 2`; pin its submodule once.
  set c1 : ↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP) :=
    Submodule.Quotient.mk q1 with hc1
  have hfr : Module.finrank ℂ (↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP)) = 2 := hlDP
  -- `[1] ≠ 0`, so `span {[1]}` has dimension 1 < 2 = `l(P)`, hence is not all of `L(P)/germZero`.
  have hq1ne : c1 ≠ 0 := by
    rw [hc1, Ne, Submodule.Quotient.mk_eq_zero]
    intro hmem
    have h := (Submodule.mem_comap.mp hmem) P
    have hP0 : (↑q1 : MeromorphicFunction X).orderW P = 0 := horder1 P
    have hbad : (0 : WithTop ℤ) = ⊤ := by rw [← hP0]; exact h
    exact absurd hbad (by simp)
  have hspan_ne : Submodule.span ℂ {c1} ≠ ⊤ := by
    intro htop
    have h1 := finrank_span_singleton (K := ℂ) hq1ne
    rw [htop, finrank_top, hfr] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span ℂ {c1} := by
    by_contra hall; push Not at hall; exact hspan_ne (Submodule.eq_top_iff'.mpr hall)
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  -- `f` is not germ-constant (else its class would lie in `span {[1]}`).
  have hnc : ¬ ∃ c, ∀ x, ∀ᶠ z in 𝓝[≠] x, (f : MeromorphicFunction X).toFun z = c := by
    rintro ⟨c, hgc⟩
    apply hv
    have hfc : Submodule.Quotient.mk f = c • c1 := by
      rw [hc1, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show ((f - c • q1 : ↥(linearSystem (X := X) DP)) : MeromorphicFunction X) ∈ germZeroSubmodule
      intro x
      rw [MeromorphicFunction.orderW_eq_top_iff]
      filter_upwards [hgc x] with z hz
      show (f : MeromorphicFunction X).toFun z - c • (1 : ℂ) = 0
      rw [hz]; simp
    rw [hfc]; exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  -- hence `f` has a pole, located at `P` with order exactly `-1`.
  have hpole : ∃ x₀, (f : MeromorphicFunction X).orderW x₀ < 0 := by
    by_contra hno; push Not at hno
    exact hnc (germ_eq_const_of_mem_linearSystem_zero (f : MeromorphicFunction X) (fun x => hno x))
  obtain ⟨x₀, hx₀⟩ := hpole
  have hx₀P : x₀ = P := by
    by_contra hne
    have hmemf := f.2 x₀
    have hDP0 : DP x₀ = 0 := by
      classical rw [hDP, Finsupp.single_apply, if_neg (fun h : P = x₀ => hne h.symm)]
    rw [hDP0] at hmemf
    have hge : (0 : WithTop ℤ) ≤ (f : MeromorphicFunction X).orderW x₀ := by simpa using hmemf
    exact absurd (lt_of_le_of_lt hge hx₀) (lt_irrefl _)
  rw [hx₀P] at hx₀
  have hPval : (f : MeromorphicFunction X).orderW P = -1 := by
    have hmemf := f.2 P
    have hDP1 : DP P = 1 := by rw [hDP, Finsupp.single_eq_same]
    rw [hDP1] at hmemf
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (lt_of_lt_of_le hx₀ le_top).ne
    rw [← hn] at hmemf hx₀ ⊢
    have hn1 : (-1 : ℤ) ≤ n := by exact_mod_cast hmemf
    have hn2 : n < 0 := by exact_mod_cast hx₀
    rw [show n = (-1 : ℤ) from by omega]; simp
  refine ⟨(f : MeromorphicFunction X), ?_, ?_⟩
  · show ((f : MeromorphicFunction X).orderW P).untop₀ = -1
    rw [hPval]; rfl
  · intro x hx
    show 0 ≤ ((f : MeromorphicFunction X).orderW x).untop₀
    have hmemf := f.2 x
    have hDP0 : DP x = 0 := by
      classical rw [hDP, Finsupp.single_apply, if_neg (fun h : P = x => hx h.symm)]
    rw [hDP0] at hmemf
    rw [untop₀_nonneg_iff]; simpa using hmemf

end Jacobians
