/-
  Dolbeault ladder — local realizability of the canonical chart-disk cover (the product witness /
  local Mittag–Leffler), the single analytic input the cone skyscraper construction
  (`SkyscraperConeRealization`) consumes.

  ## What this file is for

  `SkyscraperConeRealization` reduces the skyscraper local-realization datum (and hence the whole
  χ-side of cohomological Riemann–Roch) to one hypothesis on the cover, `LocallyRealizable 𝔘`: the
  order-`(−D(P)−1)` principal-part coefficient `coeffGermLin` is *surjective* at every cover-set
  `U j ∋ P`, for every divisor `D`.  Equivalently (`coeffGermLin` is ℂ-linear into `ℂ`): there is a
  section `g ∈ 𝒪_{D+P}(U j)` whose order at `P` is *exactly* `k = −(D P) − 1`, so its top Laurent
  coefficient is nonzero.

  This holds for the **canonical chart-disk cover** `chartDiskCover` because each cover-set `U j` sits
  inside the source of a single chart `φ = chartAt (center j)` (`ChartDiskCover.subset_chart_source`),
  on which the **product witness**

      `g = ∏_{Q ∈ supp(D+P) ∩ U j} (φ − φ(Q))^{−(D+P)(Q)}`

  is meromorphic with `ord_Q g = −(D+P)(Q)` at each support point `Q` (the other factors being analytic
  and nonzero there) and `ord_x g = 0 ≥ −(D+P)(x)` elsewhere.  In particular `ord_P g = −(D+P)(P) = k`
  exactly, so `coeffGermLin [g] ≠ 0` and `coeffGermLin` is onto `ℂ`.

  ## Status

  The product witness is the genuine local-analytic core (a finite-product order computation plus the
  chart-change relating the center chart `φ` to the open-submanifold chart at `P` that `ordU`/`coeffGermLin`
  use).  It is isolated here as the single named obligation `locallyRealizable_chartDiskCover`; closing
  it makes the entire χ-side (`cohomological_riemannRoch`) fully complete on the canonical cover.
-/
import KirovDolbeault.Dolbeault.SkyscraperConeRealization
import KirovDolbeault.Dolbeault.LerayCoverExists
import KirovDolbeault.Dolbeault.CechModelManifold
import Mathlib.Analysis.Meromorphic.FactorizedRational

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter Function

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Surjectivity of `coeffGermLin` from a single nonzero coefficient

`coeffGermLin` is ℂ-linear into `ℂ`; if some germ has nonzero coefficient, scaling realises every
value, so the map is onto. -/

/-- **`coeffGermLin` is surjective once it is nonzero.**  Given `γ₀ ∈ 𝒪_{D+P}(W)` with
`coeffGermLin γ₀ = c ≠ 0`, every `a : ℂ` is `coeffGermLin ((a/c) • γ₀)`. -/
theorem coeffGermLin_surjective_of_ne_zero {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)
    {γ₀ : OmegaDGerm (D + Finsupp.single P 1) W} (hc : coeffGermLin hP (D := D) γ₀ ≠ 0) :
    Function.Surjective (coeffGermLin hP (D := D)) := by
  intro a
  refine ⟨(a / coeffGermLin hP (D := D) γ₀) • γ₀, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hc]

/-- **A section of order *exactly* `−(D P)−1` at `P` has nonzero coefficient.**  For
`g ∈ 𝒪_{D+P}(W)` with `ordU g ⟨P,hP⟩ = −(D P)−1` (the minimal allowed order, a genuine pole of that
exact order), the order-`(−D(P)−1)` coefficient is nonzero (`coeffWFn_eq_zero_iff`: it vanishes iff
the order is *strictly* larger). -/
theorem coeffGermLin_ne_zero_of_ordU_eq {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)
    {g : W → ℂ} (hg : g ∈ OmegaD (D + Finsupp.single P 1) W)
    (hord : ordU g ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ)) :
    coeffGermLin hP (D := D) ⟨toGerm W g, ⟨g, hg, rfl⟩⟩ ≠ 0 := by
  show coeffGermFn (-(D P) - 1) ⟨P, hP⟩ (toGerm W g) ≠ 0
  rw [coeffGermFn_coe, Ne, coeffWFn_eq_zero_iff hg.1 (le_of_eq hord.symm)]
  -- `¬ (k < ordU g P)` since `ordU g P = k`.
  rw [hord]
  exact lt_irrefl _

/-- **Per-cover-set realizability from a witness of exact order.**  If for every `D` and `P ∈ W` there
is a section of `𝒪_{D+P}(W)` of order *exactly* `−(D P)−1` at `P`, then `coeffGermLin` is surjective at
`W` (the local Mittag–Leffler condition).  The product witness supplies such a section on a chart-disk. -/
theorem coeffGermLin_surjective_of_exists_witness {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)
    (hwit : ∃ g : W → ℂ, ∃ _hg : g ∈ OmegaD (D + Finsupp.single P 1) W,
      ordU g ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ)) :
    Function.Surjective (coeffGermLin hP (D := D)) := by
  obtain ⟨g, hg, hord⟩ := hwit
  exact coeffGermLin_surjective_of_ne_zero hP (coeffGermLin_ne_zero_of_ordU_eq hP hg hord)

/-! ### The product-witness existence (the local-analytic core)

The cover-set-level input the surjectivity reduction (`coeffGermLin_surjective_of_exists_witness`)
needs: on a chart-disk cover-set `U j`, a section of `𝒪_{D+P}` of order *exactly* `−(D P)−1` at `P`.
This is the **product witness / local Mittag–Leffler** (Forster §16) and is the genuine
local-analytic core. -/

/-- **Order transfer through the center chart.**  The intrinsic order on `↥U` (`ordU`) of the
chart-pullback witness `g = F ∘ φ` (with `φ = chartAt c` and `U ⊆ φ.source`) at a point `x ∈ U`
equals the *planar* order of `F` at `φ x`.

`ordU g ⟨x⟩` is read in the *ambient* chart at `x` (`CechH0.ordU_eq_orderAt_Gext`), where `Gext g`
agrees with `F ∘ φ`; the chart-transition `φ ∘ (chartAt x).symm` is an analytic biholomorphism
(`transition_analyticAt_of_mem` + `transition_deriv_ne_zero`), so
`meromorphicOrderAt_comp_of_deriv_ne_zero` collapses the composition to `meromorphicOrderAt F (φ x)`. -/
theorem ordU_comp_chart_eq {c : X} {U : Opens X}
    (hU : (U : Set X) ⊆ (chartAt (H := ℂ) c).source) (F : ℂ → ℂ) {x : X} (hx : x ∈ U) :
    ordU (fun w : U => F ((chartAt (H := ℂ) c) w.1)) ⟨x, hx⟩ =
      meromorphicOrderAt F ((chartAt (H := ℂ) c) x) := by
  set φ := chartAt (H := ℂ) c with hφ
  set g : U → ℂ := fun w => F (φ w.1) with hg
  rw [ordU_eq_orderAt_Gext g hx]
  have hxx : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  have hxc : x ∈ φ.source := hU hx
  -- Near `chartAt x x`, `Gext g ∘ (chartAt x).symm` agrees with `F ∘ (φ ∘ (chartAt x).symm)`.
  have hmemU : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) x) x), (chartAt (H := ℂ) x).symm w ∈ (U : Set X) := by
    have hwx_tgt : (chartAt (H := ℂ) x) x ∈ (chartAt (H := ℂ) x).target :=
      (chartAt (H := ℂ) x).map_source hxx
    have hcont : ContinuousAt (chartAt (H := ℂ) x).symm ((chartAt (H := ℂ) x) x) :=
      (chartAt (H := ℂ) x).continuousAt_symm hwx_tgt
    have hh : (chartAt (H := ℂ) x).symm ((chartAt (H := ℂ) x) x) ∈ (U : Set X) := by
      rw [(chartAt (H := ℂ) x).left_inv hxx]; exact hx
    exact hcont.preimage_mem_nhds (U.isOpen.mem_nhds hh)
  have heq : (Gext g ∘ (chartAt (H := ℂ) x).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) x) x)]
      (F ∘ (φ ∘ (chartAt (H := ℂ) x).symm)) := by
    filter_upwards [hmemU] with w hw
    show Gext g ((chartAt (H := ℂ) x).symm w) = F (φ ((chartAt (H := ℂ) x).symm w))
    rw [Gext_apply_mem g hw]
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds)]
  -- The transition `φ ∘ (chartAt x).symm` is an analytic biholomorphism at `chartAt x x`.
  have hψ : AnalyticAt ℂ (φ ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) :=
    transition_analyticAt_of_mem (y := x) (z := c) hxx hxc
  have hψ_deriv : deriv (φ ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) ≠ 0 :=
    transition_deriv_ne_zero (y := x) (z := c) hxx hxc
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero hψ hψ_deriv]
  congr 1
  show φ ((chartAt (H := ℂ) x).symm ((chartAt (H := ℂ) x) x)) = φ x
  rw [(chartAt (H := ℂ) x).left_inv hxx]

/-- **Meromorphy of the chart-pullback witness on `↥U`.**  If `F` is meromorphic on all of `ℂ` and
`U ⊆ φ.source` (`φ = chartAt c`), then `g = F ∘ φ` is meromorphic on the open submanifold `↥U`: in
each point's own chart it agrees with `F ∘ (φ ∘ chart.symm)` (an analytic-precomposition of the
meromorphic `F`). -/
theorem isMeromorphic_comp_chart {c : X} {U : Opens X}
    (hU : (U : Set X) ⊆ (chartAt (H := ℂ) c).source) {F : ℂ → ℂ} (hF : ∀ z : ℂ, MeromorphicAt F z) :
    IsMeromorphic (U : Type _) (fun w : U => F ((chartAt (H := ℂ) c) w.1)) := by
  set φ := chartAt (H := ℂ) c with hφ
  set g : U → ℂ := fun w => F (φ w.1) with hg
  intro u
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g u.2
  have hxx : (u : X) ∈ (chartAt (H := ℂ) (u : X)).source := mem_chart_source ℂ _
  have hxc : (u : X) ∈ φ.source := hU u.2
  have hψ : AnalyticAt ℂ (φ ∘ (chartAt (H := ℂ) (u : X)).symm)
      ((chartAt (H := ℂ) (u : X)) (u : X)) :=
    transition_analyticAt_of_mem (y := (u : X)) (z := c) hxx hxc
  have hψpt : (φ ∘ (chartAt (H := ℂ) (u : X)).symm) ((chartAt (H := ℂ) (u : X)) (u : X)) =
      φ (u : X) := by simp only [Function.comp_apply, (chartAt (H := ℂ) (u : X)).left_inv hxx]
  have hmer : MeromorphicAt (F ∘ (φ ∘ (chartAt (H := ℂ) (u : X)).symm))
      ((chartAt (H := ℂ) (u : X)) (u : X)) := (hψpt ▸ hF (φ (u : X))).comp_analyticAt hψ
  -- Transfer `MeromorphicAt` back to `g ∘ (chartAt u).symm` at `chartAt u u`.
  have hmemU : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) (u : X)) (u : X)),
      (chartAt (H := ℂ) (u : X)).symm w ∈ (U : Set X) := by
    have hwx_tgt : (chartAt (H := ℂ) (u : X)) (u : X) ∈ (chartAt (H := ℂ) (u : X)).target :=
      (chartAt (H := ℂ) (u : X)).map_source hxx
    have hcont : ContinuousAt (chartAt (H := ℂ) (u : X)).symm ((chartAt (H := ℂ) (u : X)) (u : X)) :=
      (chartAt (H := ℂ) (u : X)).continuousAt_symm hwx_tgt
    have hh : (chartAt (H := ℂ) (u : X)).symm ((chartAt (H := ℂ) (u : X)) (u : X)) ∈ (U : Set X) := by
      rw [(chartAt (H := ℂ) (u : X)).left_inv hxx]; exact u.2
    exact hcont.preimage_mem_nhds (U.isOpen.mem_nhds hh)
  have heq2 : (Gext g ∘ (chartAt (H := ℂ) (u : X)).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) (u : X)) (u : X))]
      (F ∘ (φ ∘ (chartAt (H := ℂ) (u : X)).symm)) := by
    filter_upwards [hmemU] with w hw
    show Gext g ((chartAt (H := ℂ) (u : X)).symm w) = F (φ ((chartAt (H := ℂ) (u : X)).symm w))
    rw [Gext_apply_mem g hw]
  rw [hbase]
  -- `g ∘ (chartAt u).symm =ᶠ Gext g ∘ (chartAt u.1).symm =ᶠ F ∘ (φ ∘ (chartAt u.1).symm)`.
  exact hmer.congr (((hev.trans heq2).filter_mono nhdsWithin_le_nhds).symm)

/-- **Existence of an exact-order witness on each chart-disk cover-set** — the local-analytic core of
the χ-side (Forster §16, Mittag–Leffler).

For each chart-disk cover-set `U j ∋ P` and divisor `D`, there is a section `g ∈ 𝒪_{D+P}(U j)` of order
*exactly* `−(D P)−1` at `P`.

The witness is the **factorized rational** `g = (∏ᶠ u, (· − u)^{dz u}) ∘ φ` read through the *center*
chart `φ = chartAt (center j)` (`U j ⊆ φ.source`), with exponent
`dz w = −(D+P)(φ.symm w)` on `φ.target` (zero off it) — so `dz (φ x) = −(D+P)(x)` for every `x ∈ U j`.
The Mathlib `FactorizedRational` API supplies the planar facts (`meromorphicNFOn_univ` — meromorphic
everywhere; `meromorphicOrderAt_eq` — order `dz z` at `z`), and `ordU_comp_chart_eq` /
`isMeromorphic_comp_chart` transfer them through the chart to `↥(U j)`.  Hence `ordU g ⟨x⟩ = −(D+P)(x)`
for every `x ∈ U j`: this meets the `𝒪_{D+P}` bound with equality everywhere, and at `P` gives the
exact order `−(D+P)(P) = −(D P)−1`. -/
theorem exists_orderExact_witness_chartDisk (D : Divisor X)
    (j : (chartDiskCover (X := X)).ι) (P : X) (hP : P ∈ (chartDiskCover (X := X)).U j) :
    ∃ g : (chartDiskCover (X := X)).U j → ℂ,
      ∃ _ : g ∈ OmegaD (D + Finsupp.single P 1) ((chartDiskCover (X := X)).U j),
      ordU g ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ) := by
  classical
  set U := (chartDiskCover (X := X)).U j with hU
  set c := (chartDiskCover (X := X)).center j with hc
  set φ := chartAt (H := ℂ) c with hφ
  have hUsrc : (U : Set X) ⊆ φ.source := Set.inter_subset_left
  set DP : Divisor X := D + Finsupp.single P 1 with hDP
  -- The exponent function `dz` realising the prescribed pole/zero orders, with finite support.
  set dz : ℂ → ℤ := fun w => if w ∈ φ.target then -(DP (φ.symm w)) else 0 with hdz
  have hdz_fin : Function.HasFiniteSupport dz := by
    apply Set.Finite.subset (DP.support.finite_toSet.image φ)
    intro w hw
    simp only [Function.mem_support, ne_eq, hdz] at hw
    by_cases hwt : w ∈ φ.target
    · have hne : DP (φ.symm w) ≠ 0 := by intro h; apply hw; simp [hwt, h]
      exact ⟨φ.symm w, by simpa [Finsupp.mem_support_iff] using hne, φ.right_inv hwt⟩
    · exact absurd (by simp [hwt]) hw
  have hdz_eval : ∀ {x : X}, x ∈ φ.source → dz (φ x) = -(DP x) := fun {x} hx => by
    simp only [hdz, φ.map_source hx, if_true, φ.left_inv hx]
  -- The factorized-rational witness `F` and its planar meromorphy/order.
  set F : ℂ → ℂ := ∏ᶠ u, (· - u) ^ dz u with hF
  have hFmer : ∀ z : ℂ, MeromorphicAt F z := fun z =>
    (FactorizedRational.meromorphicNFOn_univ dz).meromorphicOn z (Set.mem_univ z)
  have hForder : ∀ z : ℂ, meromorphicOrderAt F z = (dz z : WithTop ℤ) := fun _ =>
    FactorizedRational.meromorphicOrderAt_eq dz hdz_fin
  set g : U → ℂ := fun w => F (φ w.1) with hg
  -- `ordU g ⟨x⟩ = −DP(x)` for every `x ∈ U` (exact equality everywhere).
  have hgord : ∀ {x : X} (hx : x ∈ U), ordU g ⟨x, hx⟩ = ((-(DP x) : ℤ) : WithTop ℤ) := fun {x} hx => by
    rw [ordU_comp_chart_eq hUsrc F hx, hForder, hdz_eval (hUsrc hx)]
  refine ⟨g, ?_, ?_⟩
  · rw [mem_OmegaD]
    refine ⟨isMeromorphic_comp_chart hUsrc hFmer, fun x => ?_⟩
    rw [hgord x.2]; norm_cast
  · rw [hgord hP]
    congr 1
    show -(DP P) = -(D P) - 1
    rw [hDP, Finsupp.add_apply, Finsupp.single_eq_same]; ring

/-- **Local realizability of the canonical chart-disk cover** (the product witness / local
Mittag–Leffler).  At every chart-disk cover-set `U j ∋ P`, the order-`(−D(P)−1)` principal-part
coefficient `coeffGermLin` is surjective onto `ℂ`, for every divisor `D` — the single analytic input
the cone skyscraper construction consumes.  PROVEN from the exact-order witness
(`exists_orderExact_witness_chartDisk`) via `coeffGermLin_surjective_of_exists_witness`. -/
theorem locallyRealizable_chartDiskCover :
    (chartDiskCover (X := X)).toFiniteCover.LocallyRealizable := by
  intro D P j hP
  exact coeffGermLin_surjective_of_exists_witness hP
    (exists_orderExact_witness_chartDisk D j P hP)

/-- **A realizable Leray cover exists** — the canonical chart-disk cover is both Leray (simply
connected sets, `chartDiskCover_simplyConnected`) and locally realizable
(`locallyRealizable_chartDiskCover`).  This unlocks the ladder→headline wiring with the cone
skyscraper construction. -/
theorem exists_realizableLerayCover :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable :=
  ⟨(chartDiskCover (X := X)).toFiniteCover,
    ⟨fun i => by simpa using chartDiskCover_simplyConnected (X := X) i,
      locallyRealizable_chartDiskCover⟩⟩

end Jacobians.Dolbeault
