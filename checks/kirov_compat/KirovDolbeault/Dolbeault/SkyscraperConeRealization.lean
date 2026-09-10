/-
  Dolbeault ladder — the skyscraper local-realization datum on a *locally realizable* cover, via the
  cone (star-of-`P`) construction (the route that DROPS the impossible singleton-star `hstar`).

  ## What this file is for

  `SkyscraperAssembly` builds `LocalRealizationData 𝔘 D P` only under a singleton-star hypothesis
  `hstar : ∀ j, P ∈ 𝔘.U j → j = i`, which (as recorded on `CohomologicalRR.exists_localRealizationData`)
  **cannot hold** on a fixed finite cover of a compact connected `X` — overlap points always exist.

  This file replaces `hstar` by the *cone / star-of-`P`* argument.  The two skyscraper-irreducible
  pieces (`e0 : H⁰(Q) ≅ ℂ` and acyclicity `Subsingleton (H¹(Q))`) are built from a single hypothesis,
  **local Mittag–Leffler on each cover-set** (`LocallyRealizable`): the order-`(−D(P)−1)` principal-part
  coefficient `coeffGermLin` is surjective at *every* cover-set `U j ∋ P` (for every `D`, `P`).  This is
  the genuine analytic input; for the canonical chart-disk cover it is the explicit product witness
  (`SkyscraperProductWitness`).

  ## The cone construction (no simplicial machinery — just the apex and a triple)

  Fix the apex `i₀ := L.i ∋ P`.  Both pieces reduce to one builder: given a ℂ-valued cochain `c : ι → ℂ`
  on the star of `P` (the indices `j` with `P ∈ U j`) satisfying the apex ℂ-cocycle condition, build a
  `B0 = sections0(D+P)` cochain `b` with `coeffGermLin (b j) = c j` on the star (`0` off it) and
  `δ⁰b ∈ sections1(D)`.  The lift uses `LocallyRealizable` at each star vertex; the cocycle check uses:
    * **off the star** the `D` and `D+P` bounds coincide on the overlap (`OmegaDGerm_add_single_eq_…`);
    * **on the star** injectivity of `coeffGermLin` (`ker_coeffGermLin`) plus its
      **restriction-invariance at `P`** (`coeffGermLin_rawRestrictG`, the coefficient analogue of
      `ordU_comp_openIncl`).
  For `e0` surjectivity `c ≡ a` (constant); for `Subsingleton H¹(Q)` `c j = coeffGermLin (g_{i₀ j})`,
  whose apex cocycle identity is exactly the `(i₀,j,k)` component of `δ¹g ∈ sections2(D)`.

  Everything here is axiom-clean modulo the `LocallyRealizable` hypothesis (no finiteness, no gaps).
-/
import KirovDolbeault.Dolbeault.SkyscraperAssembly
import KirovDolbeault.Dolbeault.CechFinitenessDtwist
import KirovDolbeault.Dolbeault.CohomologicalH0Finiteness

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Restriction-invariance of the principal-part coefficient at `P`

The order-`k` coefficient at `P` is read in the open submanifold's own chart at `P`.  Restriction
`↥V → ↥W` (for `W ≤ V`, `P ∈ W`) reads `f` at the same ambient point near `P` (both charts are
`subtypeRestr`s of the *same* ambient `chartAt ℂ P`, `restrict_chart_aux`), so the coefficient is
unchanged.  This is the coefficient analogue of `CechSection.ordU_comp_openIncl`. -/

/-- **Restriction-invariance of `coeffWFn` at `P`.**  For `W ≤ V` and `P ∈ W`, the order-`k`
coefficient of `f ∘ openIncl` at `P` (read in `↥W`'s chart) equals that of `f` at `P` (read in `↥V`'s
chart). -/
theorem coeffWFn_comp_openIncl {V W : Opens X} (h : W ≤ V) (k : ℤ) (f : V → ℂ) (w : W) :
    coeffWFn k w (f ∘ openIncl h) = coeffWFn k (openIncl h w) f := by
  obtain ⟨hbase, hev⟩ := restrict_chart_aux h f w
  unfold coeffWFn
  rw [show (chartAt (H := ℂ) (openIncl h w)) (openIncl h w) = (chartAt (H := ℂ) w) w from hbase.symm]
  exact laurentCoeff_congr (hev.filter_mono nhdsWithin_le_nhds)

namespace FiniteCover

open FiniteFamily

variable (𝔘 : FiniteCover X) (D : Divisor X) (P : X)

/-- **Restriction-invariance of `coeffGermLin` at `P`** (germ-class form).  For `W ≤ V`, `P ∈ W`, and
a `𝒪_{D+P}`-germ `γ` on `V`, the coefficient of its restriction to `W` equals the coefficient of `γ`:
the value at `P` is read at the same ambient point in either chart (`coeffWFn_comp_openIncl`). -/
theorem coeffGermLin_rawRestrictG {V W : Opens X} (h : W ≤ V) (hPV : P ∈ V) (hPW : P ∈ W)
    (γ : OmegaDGerm (D + Finsupp.single P 1) V) :
    coeffGermLin hPW (D := D)
        ⟨rawRestrictG h (γ : MGerm V), rawRestrictG_omegaDGerm h γ.2⟩
      = coeffGermLin hPV (D := D) γ := by
  obtain ⟨f, hf, hfeq⟩ := γ.2
  -- read both sides on the representative `f`.
  have hγ : (γ : MGerm V) = toGerm V f := hfeq.symm
  show coeffGermFn (-(D P) - 1) ⟨P, hPW⟩ (rawRestrictG h (γ : MGerm V))
      = coeffGermFn (-(D P) - 1) ⟨P, hPV⟩ (γ : MGerm V)
  rw [hγ, rawRestrictG_coe, coeffGermFn_coe, coeffGermFn_coe]
  -- `coeffWFn` restriction-invariance, with `openIncl h ⟨P,hPW⟩ = ⟨P,hPV⟩`.
  rw [coeffWFn_comp_openIncl h (-(D P) - 1) f ⟨P, hPW⟩]
  rfl

end FiniteCover

/-! ### Local Mittag–Leffler — the analytic input the cone construction consumes -/

/-- **Local realizability of a cover** (local Mittag–Leffler): at every cover-set `U j ∋ P`, the
order-`(−D(P)−1)` principal-part coefficient `coeffGermLin` is *surjective* onto `ℂ`, for every
divisor `D` and every point `P`.  Equivalently: every prescribed top Laurent coefficient at `P` is
realised by some `𝒪_{D+P}(U j)`-germ.  This is the genuine analytic content of the skyscraper SES,
isolated at the level of a single cover-set; for the canonical chart-disk cover it is the explicit
product witness (`SkyscraperProductWitness.locallyRealizable_chartDiskCover`). -/
def FiniteCover.LocallyRealizable (𝔘 : FiniteCover X) : Prop :=
  ∀ (D : Divisor X) (P : X) (j : 𝔘.ι) (hP : P ∈ 𝔘.U j),
    Function.Surjective (coeffGermLin hP (D := D))

namespace FiniteCover

open FiniteFamily

variable (𝔘 : FiniteCover X) (D : Divisor X) (P : X)

/-! ### The cone builder: realising a star ℂ-cochain by a `B0`-cochain

Given a target 1-cochain `g ∈ sections1(D+P)` and a star ℂ-cochain `cw` compatible with `g` on the
star overlaps (`cw k − cw j = coeff g_{jk}` whenever `P ∈ U j ⊓ U k`), the builder produces a
`B0 = sections0(D+P)` cochain `b` whose coefficient on the star is `cw` (and `0` off it) and with
`δ⁰b − g ∈ sections1(D)`.  Both `e0` surjectivity (`g = 0`, `cw ≡ a`) and `Subsingleton H¹(Q)`
(`g` a `Q`-cocycle, `cw j = coeff g_{i₀ j}`) are instances. -/

open Classical in
/-- The lifted witness germ at a star vertex `U j ∋ P` realising the prescribed coefficient `t`
(extracted from `LocallyRealizable`); `0` off the star.  `coneLift` is the underlying `MGerm`. -/
noncomputable def coneLift (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ) (j : 𝔘.ι) : MGerm (𝔘.U j) :=
  if hj : P ∈ 𝔘.U j then ((Classical.choose (hR D P j hj (cw j))).1 : MGerm (𝔘.U j)) else 0

theorem coneLift_mem (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ) (j : 𝔘.ι) :
    𝔘.coneLift D P hR cw j ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U j) := by
  classical
  unfold coneLift
  by_cases hj : P ∈ 𝔘.U j
  · rw [dif_pos hj]; exact (Classical.choose (hR D P j hj (cw j))).2
  · rw [dif_neg hj]; exact Submodule.zero_mem _

/-- On the star (`P ∈ U j`) the lifted germ has the prescribed coefficient `cw j`. -/
theorem coeffGermLin_coneLift (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ) {j : 𝔘.ι}
    (hj : P ∈ 𝔘.U j) :
    coeffGermLin hj (D := D) ⟨𝔘.coneLift D P hR cw j, 𝔘.coneLift_mem D P hR cw j⟩ = cw j := by
  have hspec := Classical.choose_spec (hR D P j hj (cw j))
  -- `coneLift = choose …` on the star; the membership proofs are irrelevant to `coeffGermLin`.
  have hval : 𝔘.coneLift D P hR cw j = ((Classical.choose (hR D P j hj (cw j))).1 : MGerm (𝔘.U j)) := by
    classical
    unfold coneLift
    rw [dif_pos hj]
  rw [← hspec]
  congr 1
  exact Subtype.ext hval

/-- The lifted cochain `coneB0`, as an element of `B0 = sections0(D+P)`. -/
noncomputable def coneB0 (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ) :
    (𝔘.skyscraperTwoStep D P).B0 :=
  ⟨fun j => 𝔘.coneLift D P hR cw j, fun j => 𝔘.coneLift_mem D P hR cw j⟩

@[simp] theorem coneB0_coe (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ) (j : 𝔘.ι) :
    ((𝔘.coneB0 D P hR cw).1 j) = 𝔘.coneLift D P hR cw j := rfl

/-- The component of `δ⁰(coneB0)` on the overlap `(j,k)` is the difference of the two restricted
lifted germs (the `cechDelta0` formula, with the lifted components plugged in). -/
theorem cechDelta0_coneB0_component (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ) (j k : 𝔘.ι) :
    𝔘.cechDelta0 (𝔘.coneB0 D P hR cw).1 (j, k)
      = rawRestrictG (inf_le_right : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U k) (𝔘.coneLift D P hR cw k)
        - rawRestrictG (inf_le_left : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j) (𝔘.coneLift D P hR cw j) := by
  simp only [cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, coneB0_coe]

/-- **The cone cocycle property.**  If the star ℂ-cochain `cw` is compatible with the target cochain
`g ∈ sections1(D+P)` on every star overlap (`cw k − cw j = coeffGermLin g_{jk}` whenever
`P ∈ U j ⊓ U k`), then `δ⁰(coneB0 cw) − g` is an `𝒪_D`-cochain.  Off the star the `D`/`D+P` bounds
coincide on the overlap; on the star the coefficient at `P` of the difference vanishes
(restriction-invariance + linearity + compatibility), so injectivity (`ker_coeffGermLin`) gives
`𝒪_D`-membership. -/
theorem cechDelta0_coneB0_sub_mem_sections1 (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ)
    {g : 𝔘.Cochain1} (hg : g ∈ 𝔘.sections1 (D + Finsupp.single P 1))
    (hcompat : ∀ (j k : 𝔘.ι) (hjk : P ∈ 𝔘.U j ⊓ 𝔘.U k),
      cw k - cw j = coeffGermLin (D := D) hjk ⟨g (j, k), hg (j, k)⟩) :
    𝔘.cechDelta0 (𝔘.coneB0 D P hR cw).1 - g ∈ 𝔘.sections1 D := by
  intro p
  obtain ⟨j, k⟩ := p
  -- the `(j,k)`-component of `δ⁰(coneB0) − g`.
  have hcomp : (𝔘.cechDelta0 (𝔘.coneB0 D P hR cw).1 - g) (j, k)
      = (rawRestrictG (inf_le_right : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U k) (𝔘.coneLift D P hR cw k)
          - rawRestrictG (inf_le_left : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j) (𝔘.coneLift D P hR cw j))
        - g (j, k) := by
    rw [Pi.sub_apply, 𝔘.cechDelta0_coneB0_component D P hR cw j k]
  rw [hcomp]
  by_cases hPjk : P ∈ 𝔘.U j ⊓ 𝔘.U k
  · -- on the star: show the coefficient at `P` of the difference vanishes, then `ker_coeffGermLin`.
    show (rawRestrictG (inf_le_right : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U k) (𝔘.coneLift D P hR cw k)
          - rawRestrictG (inf_le_left : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j) (𝔘.coneLift D P hR cw j))
        - g (j, k) ∈ OmegaDGerm D (𝔘.U j ⊓ 𝔘.U k)
    obtain ⟨hPj, hPk⟩ := TopologicalSpace.Opens.mem_inf.mp hPjk
    -- name the three germ summands and their `OmegaDGerm (D+P)`-memberships.
    set γk := rawRestrictG (inf_le_right : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U k) (𝔘.coneLift D P hR cw k) with hγk
    set γj := rawRestrictG (inf_le_left : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j) (𝔘.coneLift D P hR cw j) with hγj
    have hmemk : γk ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U j ⊓ 𝔘.U k) :=
      rawRestrictG_omegaDGerm _ (𝔘.coneLift_mem D P hR cw k)
    have hmemj : γj ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U j ⊓ 𝔘.U k) :=
      rawRestrictG_omegaDGerm _ (𝔘.coneLift_mem D P hR cw j)
    have hmemg : g (j, k) ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U j ⊓ 𝔘.U k) := hg (j, k)
    -- the difference lies in `OmegaDGerm (D+P) (U j ⊓ U k)`.
    have hmemDP : (γk - γj) - g (j, k) ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U j ⊓ 𝔘.U k) :=
      sub_mem (sub_mem hmemk hmemj) hmemg
    -- the two restricted-lift coefficients equal `cw k`, `cw j` (restriction-invariance).
    have hck : coeffGermLin hPjk (D := D) ⟨γk, hmemk⟩ = cw k := by
      have h1 := coeffGermLin_rawRestrictG D P (inf_le_right : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U k) hPk hPjk
        ⟨𝔘.coneLift D P hR cw k, 𝔘.coneLift_mem D P hR cw k⟩
      -- `h1`'s LHS subtype equals `⟨γk, hmemk⟩` up to proof irrelevance of the membership.
      exact h1.trans (𝔘.coeffGermLin_coneLift D P hR cw hPk)
    have hcj : coeffGermLin hPjk (D := D) ⟨γj, hmemj⟩ = cw j := by
      have h1 := coeffGermLin_rawRestrictG D P (inf_le_left : 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j) hPj hPjk
        ⟨𝔘.coneLift D P hR cw j, 𝔘.coneLift_mem D P hR cw j⟩
      exact h1.trans (𝔘.coeffGermLin_coneLift D P hR cw hPj)
    -- the coefficient of the difference at `P` is `0`.
    have hcoeff0 : coeffGermLin hPjk (D := D) ⟨(γk - γj) - g (j, k), hmemDP⟩ = 0 := by
      have hsub : (⟨(γk - γj) - g (j, k), hmemDP⟩ :
            OmegaDGerm (D + Finsupp.single P 1) (𝔘.U j ⊓ 𝔘.U k))
          = (⟨γk, hmemk⟩ - ⟨γj, hmemj⟩) - ⟨g (j, k), hmemg⟩ := by
        apply Subtype.ext; rfl
      rw [hsub, map_sub, map_sub, hck, hcj, ← hcompat j k hPjk]
      ring
    -- vanishing coefficient ⟹ `𝒪_D`-membership (`ker_coeffGermLin`).
    have hmemD := (ker_coeffGermLin hPjk (D := D)).le (LinearMap.mem_ker.mpr hcoeff0)
    rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hmemD
    exact hmemD
  · -- off the star: the `D` and `D+P` bounds coincide on the overlap.
    rw [← OmegaDGerm_add_single_eq_of_not_mem hPjk]
    exact sub_mem (sub_mem (rawRestrictG_omegaDGerm _ (𝔘.coneLift_mem D P hR cw k))
      (rawRestrictG_omegaDGerm _ (𝔘.coneLift_mem D P hR cw j))) (hg (j, k))

/-! ### `e0` surjectivity from local realizability (the cone, constant cochain) -/

/-- The `coneB0` class lies in `H0Q = ker dQ0` when `cw` is `g = 0`-compatible (so `δ⁰(coneB0) ∈
sections1 D`). -/
theorem coneB0_mk_mem_H0Q (hR : 𝔘.LocallyRealizable) (cw : 𝔘.ι → ℂ)
    (hcompat : ∀ (j k : 𝔘.ι) (_hjk : P ∈ 𝔘.U j ⊓ 𝔘.U k), cw k - cw j = 0) :
    Submodule.Quotient.mk (𝔘.coneB0 D P hR cw) ∈ (𝔘.skyscraperTwoStep D P).H0Q := by
  rw [TwoStepSES.H0Q, LinearMap.mem_ker, TwoStepSES.dQ0_mk, Submodule.Quotient.mk_eq_zero,
    mem_submoduleOf]
  -- `δ⁰(coneB0) = δ⁰(coneB0) − 0 ∈ sections1 D` via the cone cocycle lemma with `g = 0`.
  have hg0 : (0 : 𝔘.Cochain1) ∈ 𝔘.sections1 (D + Finsupp.single P 1) := Submodule.zero_mem _
  have h := 𝔘.cechDelta0_coneB0_sub_mem_sections1 D P hR cw hg0 (by
    intro j k hjk
    rw [hcompat j k hjk]
    -- `coeffGermLin ⟨0, _⟩ = 0`.
    symm
    rw [show (⟨(0 : 𝔘.Cochain1) (j, k), hg0 (j, k)⟩ :
        OmegaDGerm (D + Finsupp.single P 1) (𝔘.U j ⊓ 𝔘.U k)) = 0 from by apply Subtype.ext; rfl,
      map_zero])
  -- `(𝔘.skyscraperTwoStep D P).dB0 (coneB0) = δ⁰(coneB0)`, and `δ⁰(coneB0) − 0 = δ⁰(coneB0)`.
  have hsub0 : 𝔘.cechDelta0 (𝔘.coneB0 D P hR cw).1 - (0 : 𝔘.Cochain1)
      = 𝔘.cechDelta0 (𝔘.coneB0 D P hR cw).1 := by rw [sub_zero]
  rw [hsub0] at h
  exact h

/-- **`e0Lin` surjectivity from local realizability.**  For the apex `U i ∋ P`, every `a : ℂ` is
realised by the constant-`a` cone cochain (`coneB0`): its class lies in `H0Q` and reads coefficient
`a` at `U i`.  Replaces `SkyscraperAssembly.e0Lin_surjective` (which needed the singleton-star
`hstar`). -/
theorem e0Lin_surjective_of_realizable (hR : 𝔘.LocallyRealizable) {i : 𝔘.ι} (hP : P ∈ 𝔘.U i) :
    Function.Surjective (𝔘.e0Lin D P hP) := by
  intro a
  -- the constant cochain `cw ≡ a` is trivially `g = 0`-compatible.
  set cw : 𝔘.ι → ℂ := fun _ => a with hcw
  refine ⟨⟨Submodule.Quotient.mk (𝔘.coneB0 D P hR cw),
    𝔘.coneB0_mk_mem_H0Q D P hR cw (fun j k _ => by rw [hcw]; ring)⟩, ?_⟩
  rw [e0Lin_apply]
  show 𝔘.coeffQ0 D P hP (Submodule.Quotient.mk (𝔘.coneB0 D P hR cw)) = a
  rw [coeffQ0_mk, coeffB0_apply]
  -- the coefficient at the apex `i` is `cw i = a`.
  have := 𝔘.coeffGermLin_coneLift D P hR cw hP
  -- align the membership proof (`coeffGermLin` depends only on the germ).
  exact this

/-! ### `Subsingleton H¹(Q)` from local realizability (the cone, apex cochain `coeff g_{i₀ j}`) -/

open Classical in
/-- The apex ℂ-cochain for acyclicity: `cwOf gB j = coeffGermLin (gB_{i j})` on the star (`P ∈ U j`),
`0` off it.  Here `i ∋ P` is the apex; `P ∈ U i ⊓ U j` whenever `P ∈ U j`. -/
noncomputable def cwOf {i : 𝔘.ι} (hPi : P ∈ 𝔘.U i)
    {gB : 𝔘.Cochain1} (hgB : gB ∈ 𝔘.sections1 (D + Finsupp.single P 1)) (j : 𝔘.ι) : ℂ :=
  if hj : P ∈ 𝔘.U j then
    coeffGermLin (D := D) (TopologicalSpace.Opens.mem_inf.mpr ⟨hPi, hj⟩)
      ⟨gB (i, j), hgB (i, j)⟩
  else 0

theorem cwOf_star {i : 𝔘.ι} (hPi : P ∈ 𝔘.U i)
    {gB : 𝔘.Cochain1} (hgB : gB ∈ 𝔘.sections1 (D + Finsupp.single P 1)) {j : 𝔘.ι}
    (hj : P ∈ 𝔘.U j) :
    𝔘.cwOf D P hPi hgB j
      = coeffGermLin (D := D) (TopologicalSpace.Opens.mem_inf.mpr ⟨hPi, hj⟩)
          ⟨gB (i, j), hgB (i, j)⟩ := by
  classical
  rw [cwOf, dif_pos hj]

/-- **Apex compatibility** (the `δ¹gB` triple identity).  For a `Q`-cocycle `gB` (`δ¹gB ∈ sections2 D`)
and star indices `j, k` (`P ∈ U j ⊓ U k`), the apex cochain satisfies
`cwOf k − cwOf j = coeffGermLin gB_{jk}`.  Read at `P` on the triple overlap `U i ⊓ U j ⊓ U k` (which
contains `P`), the `(i,j,k)` component of `δ¹gB ∈ 𝒪_D` has coefficient `0`
(`coeffGermFn_eq_zero_of_mem_OmegaDGerm`), giving (via restriction-invariance)
`coeff gB_{jk} − coeff gB_{ik} + coeff gB_{ij} = 0`. -/
theorem cwOf_compat {i : 𝔘.ι} (hPi : P ∈ 𝔘.U i)
    {gB : 𝔘.Cochain1} (hgB : gB ∈ 𝔘.sections1 (D + Finsupp.single P 1))
    (hcoc : 𝔘.cechDelta1 gB ∈ 𝔘.sections2 D) (j k : 𝔘.ι) (hjk : P ∈ 𝔘.U j ⊓ 𝔘.U k) :
    𝔘.cwOf D P hPi hgB k - 𝔘.cwOf D P hPi hgB j
      = coeffGermLin (D := D) hjk ⟨gB (j, k), hgB (j, k)⟩ := by
  obtain ⟨hPj, hPk⟩ := TopologicalSpace.Opens.mem_inf.mp hjk
  -- `P` lies in the triple overlap `U i ⊓ U j ⊓ U k`.
  have hPijk : P ∈ 𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k :=
    TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨hPi, hPj⟩, hPk⟩
  -- the `(i,j,k)` component of `δ¹gB` lies in `OmegaDGerm D (triple)`.
  have hmemD : 𝔘.cechDelta1 gB (i, j, k) ∈ OmegaDGerm D (𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k) := hcoc (i, j, k)
  have hmemDP : 𝔘.cechDelta1 gB (i, j, k)
      ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k) :=
    (OmegaDGerm_le_add_single (D := D) (P := P) (U := 𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k)) hmemD
  -- its coefficient at `P` is `0` (a `𝒪_D`-germ has vanishing top coefficient).
  have hcoeff0 : coeffGermLin (D := D) hPijk ⟨𝔘.cechDelta1 gB (i, j, k), hmemDP⟩ = 0 := by
    show coeffGermFn (-(D P) - 1) ⟨P, hPijk⟩ (𝔘.cechDelta1 gB (i, j, k)) = 0
    exact coeffGermFn_eq_zero_of_mem_OmegaDGerm hPijk hmemD
  -- expand `(δ¹gB)_{ijk}` into the three restricted components.
  have hexp : 𝔘.cechDelta1 gB (i, j, k)
      = rawRestrictG (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j ⊓ 𝔘.U k) (gB (j, k))
        - rawRestrictG (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U i ⊓ 𝔘.U k) (gB (i, k))
        + rawRestrictG (inf_le_left : 𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U i ⊓ 𝔘.U j) (gB (i, j)) := by
    simp only [cechDelta1, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
  -- memberships of the three restricted components in `OmegaDGerm (D+P) (triple)`.
  have hmjk : rawRestrictG (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j ⊓ 𝔘.U k) (gB (j, k))
      ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k) :=
    rawRestrictG_omegaDGerm _ (hgB (j, k))
  have hmik : rawRestrictG (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U i ⊓ 𝔘.U k) (gB (i, k))
      ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k) :=
    rawRestrictG_omegaDGerm _ (hgB (i, k))
  have hmij : rawRestrictG (inf_le_left : 𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U i ⊓ 𝔘.U j) (gB (i, j))
      ∈ OmegaDGerm (D + Finsupp.single P 1) (𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k) :=
    rawRestrictG_omegaDGerm _ (hgB (i, j))
  -- the overlap memberships for the three `(R)` applications.
  have hPik : P ∈ 𝔘.U i ⊓ 𝔘.U k := TopologicalSpace.Opens.mem_inf.mpr ⟨hPi, hPk⟩
  have hPij : P ∈ 𝔘.U i ⊓ 𝔘.U j := TopologicalSpace.Opens.mem_inf.mpr ⟨hPi, hPj⟩
  -- restriction-invariance of each of the three coefficients (down to the natural double overlaps).
  have hRjk := coeffGermLin_rawRestrictG D P
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U j ⊓ 𝔘.U k) hjk hPijk ⟨gB (j, k), hgB (j, k)⟩
  have hRik := coeffGermLin_rawRestrictG D P
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U i ⊓ 𝔘.U k) hPik hPijk ⟨gB (i, k), hgB (i, k)⟩
  have hRij := coeffGermLin_rawRestrictG D P
    (inf_le_left : 𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k ≤ 𝔘.U i ⊓ 𝔘.U j) hPij hPijk ⟨gB (i, j), hgB (i, j)⟩
  -- the two apex values, via `cwOf_star`.
  have hcwk : 𝔘.cwOf D P hPi hgB k = coeffGermLin (D := D) hPik ⟨gB (i, k), hgB (i, k)⟩ :=
    𝔘.cwOf_star D P hPi hgB hPk
  have hcwj : 𝔘.cwOf D P hPi hgB j = coeffGermLin (D := D) hPij ⟨gB (i, j), hgB (i, j)⟩ :=
    𝔘.cwOf_star D P hPi hgB hPj
  -- the subtype `⟨(δ¹gB)_{ijk}, hmemDP⟩` is the linear combination of the three restricted germs.
  have hsplit : (⟨𝔘.cechDelta1 gB (i, j, k), hmemDP⟩ :
        OmegaDGerm (D + Finsupp.single P 1) (𝔘.U i ⊓ 𝔘.U j ⊓ 𝔘.U k))
      = (⟨_, hmjk⟩ - ⟨_, hmik⟩) + ⟨_, hmij⟩ := by
    apply Subtype.ext; exact hexp
  rw [hsplit, map_add, map_sub] at hcoeff0
  -- now `hcoeff0 : coeff(R jk) − coeff(R ik) + coeff(R ij) = 0`; substitute `(R)` and rearrange.
  rw [hRjk, hRik, hRij] at hcoeff0
  rw [hcwk, hcwj]
  linear_combination -hcoeff0

/-- A `Q`-1-cocycle `mk gB` (`δ¹gB ∈ sections2 D`) lies in `range dQ0`: the cone builder with apex
`i ∋ P` and cochain `cwOf gB` produces `b` with `δ⁰b − gB ∈ sections1 D`, so `dQ0 (mk b) = mk gB`. -/
theorem mk_mem_range_dQ0_of_cocycle (hR : 𝔘.LocallyRealizable) {i : 𝔘.ι} (hPi : P ∈ 𝔘.U i)
    (gB : (𝔘.skyscraperTwoStep D P).B1)
    (hcoc : 𝔘.cechDelta1 (gB.1 : 𝔘.Cochain1) ∈ 𝔘.sections2 D) :
    (Submodule.Quotient.mk gB : (𝔘.skyscraperTwoStep D P).Q1)
      ∈ LinearMap.range (𝔘.skyscraperTwoStep D P).dQ0 := by
  -- the apex cochain and the cone-built `b`.
  set cw := 𝔘.cwOf D P hPi gB.2 with hcw
  refine ⟨Submodule.Quotient.mk (𝔘.coneB0 D P hR cw), ?_⟩
  rw [TwoStepSES.dQ0_mk]
  -- `dQ0 (mk b) = mk (dB0 b) = mk (δ⁰b)`; need `mk (δ⁰b) = mk gB` in Q1, i.e. `δ⁰b − gB ∈ sections1 D`.
  rw [Submodule.Quotient.eq, mem_submoduleOf, Submodule.coe_sub, TwoStepSES.dB0_coe]
  -- the underlying cochain difference is `δ⁰(coneB0) − gB`; apply the cone cocycle lemma.
  exact 𝔘.cechDelta0_coneB0_sub_mem_sections1 D P hR cw gB.2
    (fun j k hjk => 𝔘.cwOf_compat D P hPi gB.2 hcoc j k hjk)

/-- **`Subsingleton (H¹(Q))` from local realizability** (the cone, apex `i ∋ P`).  Every `Q`-1-cocycle
class is a coboundary (`mk_mem_range_dQ0_of_cocycle`), so `(range dQ0).submoduleOf (ker dQ1) = ⊤` and
`H¹(Q) = ker dQ1 ⧸ range dQ0` is trivial.  Replaces `SkyscraperAssembly.subsingleton_H1Q` (singleton
star). -/
theorem subsingleton_H1Q_of_realizable (hR : 𝔘.LocallyRealizable) {i : 𝔘.ι} (hPi : P ∈ 𝔘.U i) :
    Subsingleton (𝔘.skyscraperTwoStep D P).H1Q := by
  rw [TwoStepSES.H1Q]
  -- it suffices that `(range dQ0).submoduleOf (ker dQ1) = ⊤`.
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  rintro ⟨q, hq⟩
  -- `q ∈ ker dQ1`; lift to `gB ∈ B1` and read the cocycle condition `δ¹gB ∈ sections2 D`.
  obtain ⟨gB, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearMap.mem_ker, TwoStepSES.dQ1_mk, Submodule.Quotient.mk_eq_zero, mem_submoduleOf] at hq
  have hcoc : 𝔘.cechDelta1 (gB.1 : 𝔘.Cochain1) ∈ 𝔘.sections2 D := hq
  rw [mem_submoduleOf]
  exact 𝔘.mk_mem_range_dQ0_of_cocycle D P hR hPi gB hcoc

/-! ### Assembling `LocalRealizationData` (the `hstar`-free, cone form) -/

/-- **The local-realization isomorphism `e0 : H0Q ≃ₗ[ℂ] ℂ`** from local realizability (no singleton
star).  The coefficient `e0Lin` is injective (`e0Lin_injective`, always) and surjective
(`e0Lin_surjective_of_realizable`, the cone). -/
noncomputable def e0Cone (hR : 𝔘.LocallyRealizable) {i : 𝔘.ι} (hP : P ∈ 𝔘.U i) :
    (𝔘.skyscraperTwoStep D P).H0Q ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (𝔘.e0Lin D P hP)
    ⟨𝔘.e0Lin_injective D P hP, 𝔘.e0Lin_surjective_of_realizable D P hR hP⟩

@[simp] theorem e0Cone_apply (hR : 𝔘.LocallyRealizable) {i : 𝔘.ι} (hP : P ∈ 𝔘.U i)
    (x : (𝔘.skyscraperTwoStep D P).H0Q) :
    𝔘.e0Cone D P hR hP x = 𝔘.e0Lin D P hP x := rfl

/-- **Compatibility of `e0Cone` with the principal-part arrow `h0ToSky`**: `h0ToSky = e0Cone ∘ h0Map`
(same proof as `SkyscraperAssembly.e0_hcompat`: both sides read the order-`(−D(P)−1)` coefficient of the
component on `U i`; `h0Map` is `mkQ`, `e0Cone` the descended coefficient). -/
theorem e0Cone_hcompat (hR : 𝔘.LocallyRealizable) {i : 𝔘.ι} (hP : P ∈ 𝔘.U i) :
    𝔘.h0ToSky D P hP
      = (𝔘.e0Cone D P hR hP : (𝔘.skyscraperTwoStep D P).H0Q →ₗ[ℂ] ℂ).comp
          (𝔘.skyscraperTwoStep D P).h0Map := by
  ext s
  show coeffGermLin hP (𝔘.restrictToCoverSet (D + Finsupp.single P 1) i s)
    = 𝔘.e0Cone D P hR hP ((𝔘.skyscraperTwoStep D P).h0Map s)
  rw [e0Cone_apply, e0Lin_apply]
  show coeffGermLin hP (𝔘.restrictToCoverSet (D + Finsupp.single P 1) i s)
    = 𝔘.coeffQ0 D P hP (((𝔘.skyscraperTwoStep D P).h0Map s) : (𝔘.skyscraperTwoStep D P).Q0)
  rw [show (((𝔘.skyscraperTwoStep D P).h0Map s) : (𝔘.skyscraperTwoStep D P).Q0)
      = Submodule.Quotient.mk (⟨(s : 𝔘.Cochain0), (Submodule.mem_inf.mp s.2).2⟩ :
          (𝔘.skyscraperTwoStep D P).B0) from rfl,
    coeffQ0_mk, coeffB0_apply]
  congr 1

/-- **`LocalRealizationData` from local realizability** — the cone/`hstar`-free assembly, fully
self-contained.  Given an apex `U i ∋ P` and `LocallyRealizable 𝔘`, the realization datum exists.
`e0`/`hcompat`/`hQac` are the cone pieces (axiom-clean); `finH1D`/`finH1DP` come from
`finiteDimensional_cechH1_general` (axiom-clean) and `finH0DP` from the
`finiteDimensional_globalSections` instance (axiom-clean), so NO finiteness hypothesis is needed. -/
noncomputable def localRealizationData_of_realizable (hR : 𝔘.LocallyRealizable) {i : 𝔘.ι}
    (hP : P ∈ 𝔘.U i) :
    𝔘.LocalRealizationData D P :=
  { i := i
    hP := hP
    e0 := 𝔘.e0Cone D P hR hP
    hcompat := 𝔘.e0Cone_hcompat D P hR hP
    hQac := 𝔘.subsingleton_H1Q_of_realizable D P hR hP
    finH1D := finiteDimensional_cechH1_general 𝔘 D
    finH1DP := finiteDimensional_cechH1_general 𝔘 (D + Finsupp.single P 1)
    finH0DP := finiteDimensional_globalSections 𝔘 (D + Finsupp.single P 1) }

end FiniteCover

end Jacobians.Dolbeault
