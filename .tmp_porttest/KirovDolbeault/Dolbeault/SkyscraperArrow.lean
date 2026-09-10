/-
  Dolbeault ladder — the skyscraper coefficient arrow `h0ToSky` and exactness `exact₁₂`.

  This builds the `f₂`-half of `CohomologicalRR.exists_skyscraperLES` on top of the local-realization
  germ-class coefficient `LocalRealization.coeffGermLin`:

    * `h0ToSky 𝔘 D P hP_i : H⁰(𝒪_{D+P}) →ₗ[ℂ] ℂ` (the order-`(−D(P)−1)` principal-part coefficient at
      `P`): restrict a global section to the cover-set `U i ∋ P` (a germ in `OmegaDGerm (D+P) (U i)`),
      then apply `coeffGermLin`.
    * `exact₁₂`: `range (h0Incl D P) = ker h0ToSky` — a section lies in `𝒪_D` iff its order-`(−D(P)−1)`
      coefficient at `P` vanishes; transported from `ker_coeffGermLin` across the cover-set restriction
      via the Čech matching condition (the genuine sheaf-theoretic content: vanishing at the one chosen
      cover-set forces membership at every cover-set).

  Sorry-free.  The snake-lemma data (`f₃`, `exact₂`, `exact₃`, `surj₄`) and the final
  `exists_skyscraperLES` assembly are OUT OF SCOPE here.
-/
import KirovDolbeault.Dolbeault.LocalRealization
import KirovDolbeault.Dolbeault.SkyscraperLESBase

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Order/membership transport — the sheaf-theoretic glue for `exact₁₂`

The genuine content of `exact₁₂` (backward: vanishing of the coefficient at the chosen cover-set `U i`
forces membership in `𝒪_D` at *every* cover-set `U j`) reduces, via `mem_OmegaD_iff_ordU_at_P`, to a
single order comparison at `P`, transported across the overlap `U i ⊓ U j` (the Čech matching). The
order at `P` is `𝓝[≠]`-germ-invariant and restriction-invariant, so it is the same whether read on
`U i` or on `U j`. When `P ∉ U j` the two order bounds (`D` vs `D+P`) coincide on all of `U j`, so the
component is automatically an `𝒪_D`-germ. -/

/-- **`ordU` is `𝓝[≠]`-germ-invariant** on the open submanifold `↥U`: two functions agreeing off a
discrete set near `u` have equal order at `u` (chart-transport via `eventually_comp_chart_iff'` +
`meromorphicOrderAt_congr`). -/
theorem ordU_congr {U : Opens X} {f g : U → ℂ} {u : U} (h : f =ᶠ[𝓝[≠] u] g) :
    ordU f u = ordU g u := by
  refine meromorphicOrderAt_congr ?_
  have hkey := eventually_comp_chart_iff' (f - g) u (· = 0)
  have h' : ∀ᶠ z in 𝓝[≠] u, (f - g) z = 0 := by
    filter_upwards [h] with z hz; simp only [Pi.sub_apply, sub_eq_zero]; exact hz
  filter_upwards [hkey.2 h'] with w hw
  simp only [Function.comp_apply, Pi.sub_apply, sub_eq_zero] at hw
  exact hw

/-- On an open `U` not containing `P`, the order bounds for `𝒪_D` and `𝒪_{D+P}` coincide pointwise
(`single P 1` is supported at `P ∉ U`), so the section submodules agree: `𝒪_{D+P}(U) = 𝒪_D(U)`. -/
theorem OmegaD_add_single_eq_of_not_mem {U : Opens X} {D : Divisor X} {P : X} (hP : P ∉ U) :
    OmegaD (D + Finsupp.single P 1) U = OmegaD D U := by
  ext f
  simp only [mem_OmegaD]
  refine and_congr_right fun _ => forall_congr' fun u => ?_
  have hPne : P ≠ u.1 := fun h => hP (h.symm ▸ u.2)
  have hu : (Finsupp.single P 1 : Divisor X) u.1 = 0 := Finsupp.single_eq_of_ne hPne.symm
  rw [Finsupp.add_apply, hu, add_zero]

/-- Germ version: on an open `U` not containing `P`, `OmegaDGerm (D+P) U = OmegaDGerm D U`. -/
theorem OmegaDGerm_add_single_eq_of_not_mem {U : Opens X} {D : Divisor X} {P : X} (hP : P ∉ U) :
    OmegaDGerm (D + Finsupp.single P 1) U = OmegaDGerm D U := by
  unfold OmegaDGerm
  rw [OmegaD_add_single_eq_of_not_mem hP]

/-- **Overlap membership transport** (the case `P ∈ V`).  If on the overlap `U ⊓ V` two matching
germs (`hmatch`) come from `γU ∈ OmegaDGerm D U` and `γV ∈ OmegaDGerm (D+P) V`, then `γV` already lies
in the *smaller* `OmegaDGerm D V`.  Reason: the order of `γV` at `P` (read on `V`) equals the order of
`γU` at `P` (read on `U`, via the overlap — orders are `𝓝[≠]`-germ- and restriction-invariant), and
`γU ∈ 𝒪_D` bounds that order by `−(D P)`; `mem_OmegaD_iff_ordU_at_P` then upgrades `γV`'s `𝒪_{D+P}`-
membership to `𝒪_D`-membership.  This is the genuine sheaf-theoretic content of `exact₁₂`. -/
theorem mem_OmegaDGerm_of_overlap_match {U V : Opens X} {D : Divisor X} {P : X}
    (hPU : P ∈ U) (hPV : P ∈ V) {γU : MGerm U} {γV : MGerm V}
    (hγU : γU ∈ OmegaDGerm D U) (hγV : γV ∈ OmegaDGerm (D + Finsupp.single P 1) V)
    (hmatch : rawRestrictG (inf_le_right : U ⊓ V ≤ V) γV
      = rawRestrictG (inf_le_left : U ⊓ V ≤ U) γU) :
    γV ∈ OmegaDGerm D V := by
  obtain ⟨fU, hfU, hfUeq⟩ := hγU
  obtain ⟨fV, hfV, hfVeq⟩ := hγV
  -- The overlap point `P` and the two open inclusions.
  set Q : (U ⊓ V : Opens X) := ⟨P, ⟨hPU, hPV⟩⟩ with hQ
  -- Rewrite the matching condition into a `𝓝[≠]`-agreement of the restricted representatives.
  rw [← hfUeq, ← hfVeq, rawRestrictG_coe, rawRestrictG_coe, toGerm_eq_iff] at hmatch
  have hagree : (fV ∘ openIncl (inf_le_right : U ⊓ V ≤ V))
      =ᶠ[𝓝[≠] Q] (fU ∘ openIncl (inf_le_left : U ⊓ V ≤ U)) := hmatch Q
  -- Order transport `ordU fV ⟨P,hPV⟩ = ordU fU ⟨P,hPU⟩` through the overlap.
  have hpV : openIncl (inf_le_right : U ⊓ V ≤ V) Q = ⟨P, hPV⟩ := rfl
  have hpU : openIncl (inf_le_left : U ⊓ V ≤ U) Q = ⟨P, hPU⟩ := rfl
  have hord : ordU fV ⟨P, hPV⟩ = ordU fU ⟨P, hPU⟩ := by
    have := ordU_congr hagree
    rwa [ordU_comp_openIncl (inf_le_right : U ⊓ V ≤ V) fV Q,
        ordU_comp_openIncl (inf_le_left : U ⊓ V ≤ U) fU Q, hpV, hpU] at this
  -- `γV = [fV]` lies in `OmegaDGerm D V` since `fV ∈ OmegaD D V`.
  refine ⟨fV, ?_, hfVeq⟩
  have hfVmem : fV ∈ OmegaD (D + Finsupp.single P 1) V := hfV
  rw [SetLike.mem_coe, mem_OmegaD_iff_ordU_at_P hPV hfVmem, hord]
  exact_mod_cast hfU.2 ⟨P, hPU⟩

namespace FiniteCover

open FiniteFamily

variable (𝔘 : FiniteCover X) (D : Divisor X) (P : X)

/-! ### Restriction of a global section to a single cover-set germ -/

/-- Restrict a global `𝒪_D`-section to its component germ on the cover-set `U i`, as an element of
the subtype `↥(OmegaDGerm D (U i))`.  The underlying map is `s ↦ s.1 i`; the codomain-restriction
membership `s.1 i ∈ OmegaDGerm D (U i)` is the `sections0` half of `globalSections = ker δ⁰ ⊓ sections0`. -/
noncomputable def restrictToCoverSet (i : 𝔘.ι) :
    ↥(𝔘.globalSections D) →ₗ[ℂ] ↥(OmegaDGerm D (𝔘.U i)) :=
  (((LinearMap.proj i).comp (𝔘.globalSections D).subtype).codRestrict (OmegaDGerm D (𝔘.U i))
    (fun s => (Submodule.mem_inf.mp s.2).2 i))

@[simp] theorem restrictToCoverSet_coe (i : 𝔘.ι) (s : ↥(𝔘.globalSections D)) :
    (𝔘.restrictToCoverSet D i s : MGerm (𝔘.U i)) = (s : 𝔘.Cochain0) i := rfl

/-- The Čech matching condition extracted from `s ∈ ker δ⁰`: on each overlap `U i ⊓ U j` the
component germs `s i` and `s j` restrict to the same germ. -/
theorem globalSections_matching {s : 𝔘.Cochain0} (hs : s ∈ LinearMap.ker 𝔘.cechDelta0)
    (i j : 𝔘.ι) :
    rawRestrictG (inf_le_right : 𝔘.U i ⊓ 𝔘.U j ≤ 𝔘.U j) (s j)
      = rawRestrictG (inf_le_left : 𝔘.U i ⊓ 𝔘.U j ≤ 𝔘.U i) (s i) := by
  rw [LinearMap.mem_ker] at hs
  have hp := congrFun hs (i, j)
  simp only [cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.zero_apply] at hp
  rwa [sub_eq_zero] at hp

/-- **The per-section core of `exact₁₂`.** For a global `𝒪_{D+P}`-section `s` and a cover-set
`U i ∋ P`, the component on `U i` lies in `𝒪_D` iff *every* component lies in `𝒪_D` (equivalently, iff
`s` is a global `𝒪_D`-section).  Forward is trivial (specialise to `i`); backward is the genuine sheaf
content: at any `U j`, if `P ∉ U j` the `D` and `D+P` bounds coincide (`OmegaDGerm_add_single_eq_…`),
and if `P ∈ U j` the order at `P` transports from `U i` across the overlap
(`mem_OmegaDGerm_of_overlap_match`). -/
theorem component_mem_iff_all {i : 𝔘.ι} (hP : P ∈ 𝔘.U i)
    (s : ↥(𝔘.globalSections (D + Finsupp.single P 1))) :
    (s : 𝔘.Cochain0) i ∈ OmegaDGerm D (𝔘.U i)
      ↔ ∀ j, (s : 𝔘.Cochain0) j ∈ OmegaDGerm D (𝔘.U j) := by
  obtain ⟨hker, hsec⟩ := Submodule.mem_inf.mp s.2
  refine ⟨fun hi j => ?_, fun hall => hall i⟩
  by_cases hPj : P ∈ 𝔘.U j
  · -- `P ∈ U j`: transport the order at `P` from `U i` across the overlap.
    exact mem_OmegaDGerm_of_overlap_match hP hPj hi (hsec j)
      (𝔘.globalSections_matching hker i j)
  · -- `P ∉ U j`: the `D` and `D+P` section spaces agree on `U j`.
    rw [← OmegaDGerm_add_single_eq_of_not_mem hPj]
    exact hsec j

/-! ### The skyscraper coefficient arrow `h0ToSky` (`f₂`) -/

/-- **The skyscraper coefficient arrow** `f₂ : H⁰(𝒪_{D+P}) → ℂ_P` at `P`, given a cover-set `U i ∋ P`:
restrict the global section to its component germ on `U i` (in `OmegaDGerm (D+P) (U i)`), then read its
order-`(−D(P)−1)` principal-part coefficient at `P` (`coeffGermLin`).  The codomain `Skyscraper D P` is
`ℂ`.  Not surjective in general (its image is the H⁰-cokernel). -/
noncomputable def h0ToSky {i : 𝔘.ι} (hP : P ∈ 𝔘.U i) :
    ↥(𝔘.globalSections (D + Finsupp.single P 1)) →ₗ[ℂ] 𝔘.Skyscraper D P :=
  (coeffGermLin hP).comp (𝔘.restrictToCoverSet (D + Finsupp.single P 1) i)

@[simp] theorem h0ToSky_apply {i : 𝔘.ι} (hP : P ∈ 𝔘.U i)
    (s : ↥(𝔘.globalSections (D + Finsupp.single P 1))) :
    𝔘.h0ToSky D P hP s
      = coeffGermLin hP (𝔘.restrictToCoverSet (D + Finsupp.single P 1) i s) := rfl

/-- `h0ToSky s = 0` iff the component germ `s i` on `U i` lies in `OmegaDGerm D (U i)` (the order-
`(−D(P)−1)` coefficient at `P` vanishes — the kernel characterization `ker_coeffGermLin`). -/
theorem h0ToSky_eq_zero_iff {i : 𝔘.ι} (hP : P ∈ 𝔘.U i)
    (s : ↥(𝔘.globalSections (D + Finsupp.single P 1))) :
    𝔘.h0ToSky D P hP s = 0 ↔ (s : 𝔘.Cochain0) i ∈ OmegaDGerm D (𝔘.U i) := by
  rw [h0ToSky_apply, ← LinearMap.mem_ker, ker_coeffGermLin, Submodule.submoduleOf,
    Submodule.mem_comap, Submodule.coe_subtype, restrictToCoverSet_coe]

/-! ### Exactness at `H⁰(𝒪_{D+P})`: `range (h0Incl) = ker (h0ToSky)` (`exact₁₂`) -/

/-- **Exactness at `H⁰(𝒪_{D+P})`** (`exact₁₂` of the skyscraper LES): `range f₁ = ker f₂`, i.e. a
global section lies in the image of `𝒪_D ↪ 𝒪_{D+P}` iff its order-`(−D(P)−1)` principal-part
coefficient at `P` vanishes.  Combines the kernel characterization at the chosen cover-set
(`h0ToSky_eq_zero_iff` ⟶ `ker_coeffGermLin`) with the sheaf-theoretic propagation
(`component_mem_iff_all`: vanishing at `U i` forces `𝒪_D`-membership at every cover-set). -/
theorem exact_h0Incl_h0ToSky {i : 𝔘.ι} (hP : P ∈ 𝔘.U i) :
    Function.Exact (𝔘.h0Incl D P) (𝔘.h0ToSky D P hP) := by
  rw [LinearMap.exact_iff, h0Incl, Submodule.range_inclusion]
  ext s
  rw [LinearMap.mem_ker, h0ToSky_eq_zero_iff, Submodule.mem_comap, Submodule.coe_subtype]
  -- `↑s ∈ globalSections D ⟺ (↑s ∈ ker δ⁰) ∧ (∀ j, ↑s j ∈ 𝒪_D(U j))`; the `ker δ⁰` part is free.
  rw [show ((s : 𝔘.Cochain0) ∈ 𝔘.globalSections D)
      ↔ ((s : 𝔘.Cochain0) ∈ LinearMap.ker 𝔘.cechDelta0
          ∧ ∀ j, (s : 𝔘.Cochain0) j ∈ OmegaDGerm D (𝔘.U j)) from Submodule.mem_inf]
  rw [𝔘.component_mem_iff_all D P hP s]
  exact ⟨fun hall => ⟨(Submodule.mem_inf.mp s.2).1, hall⟩, fun h => h.2⟩

end FiniteCover

/-! ### Witness global-membership on a chart-disk (discharges `hwit`)

`coeffGermLin_surjective`/`localRealizationGermEquiv` need the witness section
`(chart − chart P)^k` (with `k = −(D P) − 1`) to lie globally in `OmegaD (D+P) W`.  This is the genuine
*chart-disk* hypothesis: `W` sits inside the source of `↥W`'s chart at `P` (so the witness is
chart-analytic everywhere on `W`), and `D` is supported on `W` only at `P`.  Then away from `P` the
witness is analytic and nonvanishing (order `0 = −D = −(D+P)`), and at `P` it has order exactly
`k = −(D+P)(P)` (`ordU_witnessFn`). -/

/-! Compactness-free chart-transition analyticity (the open submanifold `↥W` is neither compact nor
connected, so the `CechH0` versions — stated over the ambient `X` with those instances — do not apply;
we re-prove them for a generic `ℂ`-charted `ω`-manifold `Y`, using only `contMDiffOn_chart`). -/

/-- The chart transition `chartAt y ∘ (chartAt z).symm` is analytic at `chartAt z z` (for `z` in the
source of `chartAt y`), on a generic `ℂ`-charted `ω`-manifold `Y`. Compactness-free copy of
`CechH0.transition_analyticAt`. -/
theorem transition_analyticAt' {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {y z : Y} (hz : z ∈ (chartAt (H := ℂ) y).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := by
  have hsrc_z : z ∈ (chartAt (H := ℂ) z).source := mem_chart_source ℂ z
  have hcz_tgt : (chartAt (H := ℂ) z) z ∈ (chartAt (H := ℂ) z).target :=
    (chartAt (H := ℂ) z).map_source hsrc_z
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := z)) _ hcz_tgt).contMDiffAt
      ((chartAt (H := ℂ) z).open_target.mem_nhds hcz_tgt)
  have hez : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) = z :=
    (chartAt (H := ℂ) z).left_inv hsrc_z
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) y)
      ((chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z)) := by
    rw [hez]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := y)) _ hz).contMDiffAt
      ((chartAt (H := ℂ) y).open_source.mem_nhds hz)
  exact (contMDiffAt_iff_contDiffAt.1
    (ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt (H := ℂ) z) z) h2 h1)).analyticAt

/-- **Chart-invariance of analyticity** on a generic `ℂ`-charted `ω`-manifold `Y` (compactness-free
copy of `CechH0.analyticAt_chart_change`): if `h` read in the chart at `y` is analytic at the image of
`z` (with `z` in that chart's source), then `h` read in its own chart at `z` is analytic. -/
theorem analyticAt_chart_change' {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {h : Y → ℂ} {y z : Y} (hz : z ∈ (chartAt (H := ℂ) y).source)
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) z)) :
    AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := by
  have hcz_tgt : (chartAt (H := ℂ) z) z ∈ (chartAt (H := ℂ) z).target :=
    (chartAt (H := ℂ) z).map_source (mem_chart_source ℂ z)
  have hez : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) = z :=
    (chartAt (H := ℂ) z).left_inv (mem_chart_source ℂ z)
  have hφ := transition_analyticAt' (y := y) (z := z) hz
  have hφ_pt : ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z)
      = (chartAt (H := ℂ) y) z := by simp only [Function.comp_apply, hez]
  have hcomp : AnalyticAt ℂ ((h ∘ (chartAt (H := ℂ) y).symm) ∘
      ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)) ((chartAt (H := ℂ) z) z) :=
    AnalyticAt.comp (hφ_pt ▸ ha) hφ
  have hmem : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) z) z),
      (chartAt (H := ℂ) z).symm w ∈ (chartAt (H := ℂ) y).source := by
    have hcont : ContinuousAt (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) :=
      (chartAt (H := ℂ) z).continuousAt_symm hcz_tgt
    have hh : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) ∈ (chartAt (H := ℂ) y).source := by
      rw [hez]; exact hz
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) y).open_source.mem_nhds hh)
  have heq : (h ∘ (chartAt (H := ℂ) z).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) z) z)]
      ((h ∘ (chartAt (H := ℂ) y).symm) ∘ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)) := by
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hw]
  rw [analyticAt_congr heq]; exact hcomp

section Witness

variable {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)

/-- Away from `P`, the witness `(chart − chart P)^k` is analytic in `↥W`'s chart at `Q` (chart-change
of the analytic `(chart_P − c)^k` via the analytic transition map; needs `Q` in the `P`-chart source
and `Q ≠ P`). -/
theorem witnessFn_analyticAt_of_ne (k : ℤ) {Q : W} (hQne : Q ≠ ⟨P, hP⟩)
    (hQsrc : Q ∈ (chartAt (H := ℂ) (⟨P, hP⟩ : W)).source) :
    AnalyticAt ℂ (witnessFn (⟨P, hP⟩ : W) k ∘ (chartAt (H := ℂ) Q).symm)
      ((chartAt (H := ℂ) Q) Q) := by
  set Pw : W := ⟨P, hP⟩ with hPw
  set c := (chartAt (H := ℂ) Pw) Pw with hc
  -- Read in `P`'s chart, the witness is `w ↦ (w − c)^k`; analytic at `chart_P Q` since `chart_P Q ≠ c`.
  have hval_ne : (chartAt (H := ℂ) Pw) Q ≠ c := by
    rw [hc]
    exact fun heq => hQne ((chartAt (H := ℂ) Pw).injOn hQsrc (mem_chart_source ℂ Pw) heq)
  have hsub : AnalyticAt ℂ (fun w : ℂ => w - c) ((chartAt (H := ℂ) Pw) Q) := by fun_prop
  have hzpow : AnalyticAt ℂ (fun w : ℂ => (w - c) ^ k) ((chartAt (H := ℂ) Pw) Q) :=
    (hsub.zpow (by simpa [sub_eq_zero] using hval_ne))
  -- The witness in `P`'s OWN chart is `(chart_P ∘ chart_P.symm) - c)^k = (id − c)^k` near `chart_P Q`.
  have hwit_Pchart : AnalyticAt ℂ (witnessFn Pw k ∘ (chartAt (H := ℂ) Pw).symm)
      ((chartAt (H := ℂ) Pw) Q) := by
    have heqf : (witnessFn Pw k ∘ (chartAt (H := ℂ) Pw).symm)
        =ᶠ[𝓝 ((chartAt (H := ℂ) Pw) Q)] (fun w : ℂ => (w - c) ^ k) := by
      have htgt : (chartAt (H := ℂ) Pw).target ∈ 𝓝 ((chartAt (H := ℂ) Pw) Q) :=
        (chartAt (H := ℂ) Pw).open_target.mem_nhds ((chartAt (H := ℂ) Pw).map_source hQsrc)
      filter_upwards [htgt] with w hw
      simp only [witnessFn, Function.comp_apply, (chartAt (H := ℂ) Pw).right_inv hw, hc]
    rw [analyticAt_congr heqf]; exact hzpow
  -- Transport to `Q`'s own chart (chart-change; `Q ∈ chart_P.source`).
  exact analyticAt_chart_change' (h := witnessFn Pw k) (y := Pw) (z := Q) hQsrc hwit_Pchart

/-- Away from `P`, the witness has order `0` (analytic and nonvanishing at `Q`). -/
theorem ordU_witnessFn_eq_zero_of_ne (k : ℤ) {Q : W} (hQne : Q ≠ ⟨P, hP⟩)
    (hQsrc : Q ∈ (chartAt (H := ℂ) (⟨P, hP⟩ : W)).source) :
    ordU (witnessFn (⟨P, hP⟩ : W) k) Q = 0 := by
  set Pw : W := ⟨P, hP⟩ with hPw
  have hana := witnessFn_analyticAt_of_ne hP k hQne hQsrc
  -- The witness value at `Q` is `(chart_P Q − chart_P Pw)^k ≠ 0` (`chart_P Q ≠ chart_P Pw`).
  have hval_ne : ((chartAt (H := ℂ) Pw) Q - (chartAt (H := ℂ) Pw) Pw) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun heq => hQne ((chartAt (H := ℂ) Pw).injOn hQsrc (mem_chart_source ℂ Pw) heq)
  have hne0 : (witnessFn Pw k ∘ (chartAt (H := ℂ) Q).symm) ((chartAt (H := ℂ) Q) Q) ≠ 0 := by
    simp only [Function.comp_apply, (chartAt (H := ℂ) Q).left_inv (mem_chart_source ℂ Q),
      witnessFn]
    exact zpow_ne_zero k hval_ne
  rw [ordU, hana.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hne0)]
  rfl

/-- **Witness global membership on a chart-disk** (discharges `hwit`).  On a `W` contained in the
source of `↥W`'s chart at `P` (`hWsrc`) where `D` is supported only at `P` (`hDsupp`), the witness
section `(chart − chart P)^k` (with `k = −(D P) − 1`) lies in `OmegaD (D + single P 1) W`: at `P` its
order is exactly `k = −(D+P)(P)` (`ordU_witnessFn`), and away from `P` it is analytic and nonvanishing
(order `0 = −(D Q) = −(D+P)(Q)`, `ordU_witnessFn_eq_zero_of_ne`).  This is exactly the geometric input
the local-realization surjectivity (`coeffGermLin_surjective`/`localRealizationGermEquiv`) needs. -/
theorem witnessFn_mem_OmegaD_add_single
    (hWsrc : ∀ Q : W, Q ∈ (chartAt (H := ℂ) (⟨P, hP⟩ : W)).source)
    (hDsupp : ∀ Q : W, Q ≠ ⟨P, hP⟩ → D Q.1 = 0) :
    witnessFn (⟨P, hP⟩ : W) (-(D P) - 1) ∈ OmegaD (D + Finsupp.single P 1) W := by
  classical
  set Pw : W := ⟨P, hP⟩ with hPw
  set k : ℤ := -(D P) - 1 with hk
  refine ⟨?_, ?_⟩
  · -- Meromorphic on `↥W`: analytic (hence meromorphic) away from `P`, and meromorphic at `P`.
    intro Q
    by_cases hQ : Q = Pw
    · subst hQ
      exact witnessFn_meromorphicAt_center Pw k
    · exact (witnessFn_analyticAt_of_ne hP k hQ (hWsrc Q)).meromorphicAt
  · -- Order bound `−(D+P)(Q) ≤ ordU witness Q` at every `Q`.
    intro Q
    by_cases hQ : Q = Pw
    · -- At `P`: order is exactly `k = −(D+P)(P)`.
      subst hQ
      rw [ordU_witnessFn]
      have hval : ((D + Finsupp.single P 1 : Divisor X) (Pw : X)) = D P + 1 := by
        simp only [show (Pw : X) = P from rfl, Finsupp.add_apply, Finsupp.single_eq_same]
      rw [hval, hk]
      norm_cast
      omega
    · -- Away from `P`: order `0`, and `−(D+P)(Q) = −(D Q) = 0` (`D` supported only at `P`).
      rw [ordU_witnessFn_eq_zero_of_ne hP k hQ (hWsrc Q)]
      have hQne : (Q : X) ≠ P := fun h => hQ (Subtype.ext h)
      have hsingle : (Finsupp.single P 1 : Divisor X) Q.1 = 0 := Finsupp.single_eq_of_ne hQne
      have hval : ((D + Finsupp.single P 1 : Divisor X) (Q : X)) = 0 := by
        rw [Finsupp.add_apply, hsingle, hDsupp Q hQ, add_zero]
      rw [hval]
      simp

end Witness

end Jacobians.Dolbeault
