/-
  Dolbeault ladder — the `h⁰ = l(D)` bridge leaf (`h0Dim_eq_lDim`).

  The Čech `H⁰(𝔘, 𝒪_D)` (global matching germ-class sections over a finite cover) is identified with
  the Riemann–Roch linear system `L(D) = linearSystem D` modulo its germ-zero junk. Concretely we
  build a `ℂ`-linear equivalence `L(D) ⧸ germZero ≃ₗ globalSections D` and read off the `finrank`s.

  Math content (the two non-formal pieces):
  * **keystone** `ordU_val_eq_orderW`: the order of a global meromorphic `F` restricted to the open
    submanifold `↥U` (computed in `↥U`'s own chart, `ordU`) equals its global order `orderW F`. Both
    charts are `subtypeRestr`s of the *same* ambient `chartAt ℂ x` (`Opens.chartAt_eq`), exactly as
    `CechSection.restrict_chart_aux`.
  * **gluing** (surjectivity): a matching family of germ-classes glues to a global `MeromorphicFunction`.
    NOTE (correctness): the naive pointwise patch `x ↦ g (idx x) x` is *not* meromorphic at
    cover-boundary points (the per-overlap disagreement set is only codiscrete *within* the overlap, so
    it can accumulate at a boundary point `y ∉ U j`). The fix is to rigidify the representatives via the
    meromorphic normal form read in the shared ambient chart, so they agree *honestly* (not just
    codiscretely) on overlaps; the patch is then chart-locally a single normal-form function.
-/
import KirovDolbeault.Dolbeault.CechComplex

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Keystone: local order on `↥U` = global order on `X` -/

/-- Base-point and chart-pullback agreement between `↥U`'s chart at `u` and `X`'s chart at `u.1`:
`↥U`'s chart is the `subtypeRestr` of the *same* ambient chart `chartAt ℂ u.1` (`Opens.chartAt_eq`),
so it reads any `F : X → ℂ` at the same ambient point near `u`. The `↥U ↪ X` analogue of
`restrict_chart_aux`. -/
private theorem incl_chart_aux {U : Opens X} (F : X → ℂ) (u : U) :
    (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) u.1) u.1 ∧
    ((F ∘ Subtype.val) ∘ (chartAt (H := ℂ) u).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) u) u)]
      (F ∘ (chartAt (H := ℂ) u.1).symm) := by
  have hbase : (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) u.1) u.1 := by
    simp only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
      Set.restrict_apply]
  refine ⟨hbase, ?_⟩
  have ht1 : (chartAt (H := ℂ) u).target ∈ 𝓝 ((chartAt (H := ℂ) u) u) :=
    (chartAt (H := ℂ) u).open_target.mem_nhds
      ((chartAt (H := ℂ) u).map_source (mem_chart_source ℂ u))
  refine Filter.eventuallyEq_of_mem ht1 fun w hw => ?_
  show F (((chartAt (H := ℂ) u).symm w : U) : X) = F ((chartAt (H := ℂ) u.1).symm w)
  congr 1
  have e1 : ((chartAt (H := ℂ) u).symm w).1 = (chartAt (H := ℂ) u.1).symm w := by
    simpa [Function.comp] using
      OpenPartialHomeomorph.subtypeRestr_symm_apply (e := chartAt (H := ℂ) u.1) ⟨u⟩ hw
  rw [e1]

/-- **Keystone.** The order of `F` restricted to the open submanifold `↥U` (in `↥U`'s chart) equals
the global order `orderW F` at the corresponding point. -/
theorem ordU_val_eq_orderW {U : Opens X} (F : MeromorphicFunction X) (u : U) :
    ordU (F.toFun ∘ Subtype.val) u = F.orderW u.1 := by
  obtain ⟨hbase, hev⟩ := incl_chart_aux F.toFun u
  rw [ordU, MeromorphicFunction.orderW, hbase]
  exact meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)

/-- `F : X → ℂ` meromorphic on `X` restricts to a meromorphic function on the open submanifold `↥U`. -/
theorem isMeromorphic_val {U : Opens X} (F : MeromorphicFunction X) :
    IsMeromorphic (U : Type _) (F.toFun ∘ Subtype.val) := by
  intro u
  obtain ⟨hbase, hev⟩ := incl_chart_aux F.toFun u
  have hmer := F.meromorphic u.1
  rw [← hbase] at hmer
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds).symm

/-! ### Germ-vanishing ↔ order `⊤` (the kernel characterisation) -/

/-- Chart-transport of an eventually-property across `𝓝[≠]`, for *any* `ℂ`-charted space `Y` (the
repo's `eventually_comp_chart_iff` carries spurious `CompactSpace`/`ConnectedSpace`; the open
submanifold `↥U` has neither). Proof copied verbatim — uses only the chart's local-homeo structure. -/
theorem eventually_comp_chart_iff' {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (g : Y → ℂ) (y : Y) (P : ℂ → Prop) :
    (∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) y) y), P ((g ∘ (chartAt (H := ℂ) y).symm) w))
      ↔ ∀ᶠ z in 𝓝[≠] y, P (g z) := by
  have hy : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
  have hyt : (chartAt (H := ℂ) y) y ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hy
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) = y :=
    (chartAt (H := ℂ) y).left_inv hy
  rw [eventually_nhdsWithin_iff, eventually_nhdsWithin_iff]
  constructor
  · intro h
    have h2 := ((chartAt (H := ℂ) y).continuousAt hy).eventually h
    filter_upwards [h2, (chartAt (H := ℂ) y).open_source.mem_nhds hy] with z hz hz_src
    intro hz_mem
    have hz_ne : z ≠ y := hz_mem
    have hchart : (chartAt (H := ℂ) y) z ∈ ({(chartAt (H := ℂ) y) y} : Set ℂ)ᶜ :=
      fun heq => hz_ne ((chartAt (H := ℂ) y).injOn hz_src hy heq)
    have := hz hchart
    rwa [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hz_src] at this
  · intro h
    have hsymm : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) :=
      (chartAt (H := ℂ) y).continuousAt_symm hyt
    have h2 := hsymm.eventually (p := fun z => z ∈ ({y} : Set Y)ᶜ → P (g z)) (by rw [hey]; exact h)
    filter_upwards [h2, (chartAt (H := ℂ) y).open_target.mem_nhds hyt] with w hw hw_tgt
    intro hw_mem
    have hw_ne : w ≠ (chartAt (H := ℂ) y) y := hw_mem
    have hsymm_ne : (chartAt (H := ℂ) y).symm w ∈ ({y} : Set Y)ᶜ := by
      intro heq
      apply hw_ne
      have hr := (chartAt (H := ℂ) y).right_inv hw_tgt
      rw [Set.mem_singleton_iff.mp heq] at hr
      exact hr.symm
    have := hw hsymm_ne
    rw [Function.comp_apply]; exact this

/-- `ordU g u = ⊤` iff `g` vanishes throughout a punctured neighbourhood of `u` on `↥U`. -/
theorem ordU_eq_top_iff {U : Opens X} (g : U → ℂ) (u : U) :
    ordU g u = ⊤ ↔ ∀ᶠ z in 𝓝[≠] u, g z = 0 := by
  rw [ordU, meromorphicOrderAt_eq_top_iff]
  exact eventually_comp_chart_iff' g u (· = 0)

/-- The germ-class of `g` is `0` iff `g` vanishes near every point (punctured) — i.e. `g` is
germ-zero junk. This is the codiscrete ⟺ `∀ 𝓝[≠]` bridge (here on `T = univ`, so it needs no
meromorphy). -/
theorem toGerm_eq_zero_iff {U : Opens X} (g : U → ℂ) :
    toGerm U g = 0 ↔ ∀ u : U, ∀ᶠ z in 𝓝[≠] u, g z = 0 := by
  show (g : MGerm U) = 0 ↔ _
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  simp only [Pi.zero_apply, Set.mem_univ, forall_const, Set.compl_univ, Set.union_empty]
  rfl

/-- Two germ-classes are equal iff their representatives agree off a discrete set near every point.
The two-function form of `toGerm_eq_zero_iff` (same codiscrete ⟺ `∀ 𝓝[≠]` bridge). -/
theorem toGerm_eq_iff {U : Opens X} (a b : U → ℂ) :
    toGerm U a = toGerm U b ↔ ∀ u : U, a =ᶠ[𝓝[≠] u] b := by
  show (a : MGerm U) = (b : MGerm U) ↔ _
  rw [Filter.Germ.coe_eq, Filter.EventuallyEq, Filter.Eventually,
    mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  simp only [Set.mem_univ, forall_const, Set.compl_univ, Set.union_empty]
  rfl

/-! ### Extension-by-zero of an `↥U`-section and the `↥U ↔ X` chart bridge

For the gluing crux we need to talk about a section `g : ↥U → ℂ` as a function on the *ambient* `X`,
so that the per-point normal form (read in `X`'s chart) makes sense. `Gext g` extends `g` by `0`;
`Gext_chart_bridge` is the `↥U ↔ X` chart-pullback agreement (the `Gext` analogue of
`incl_chart_aux`), from which meromorphy / order / normal-form on `X` all transfer from `↥U`. -/

open Classical in
/-- Extend a section on the open submanifold `↥U` by `0` to a function on the whole space `X`. -/
noncomputable def Gext {U : Opens X} (g : U → ℂ) : X → ℂ :=
  fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0

theorem Gext_comp_val {U : Opens X} (g : U → ℂ) :
    (Gext g) ∘ (Subtype.val : U → X) = g := by
  funext u; simp only [Function.comp_apply, Gext, dif_pos u.2]

theorem Gext_apply_mem {U : Opens X} (g : U → ℂ) {x : X} (hx : x ∈ U) :
    Gext g x = g ⟨x, hx⟩ := by simp only [Gext, dif_pos hx]

/-- The base point and chart-pullback agree between `↥U`'s chart at `⟨y⟩` and `X`'s chart at `y` for
`y ∈ U`: both are `subtypeRestr`s of the *same* ambient chart `chartAt ℂ y` (`Opens.chartAt_eq`), and
`Gext g` agrees with `g` near `y` (the point and its neighbours lie in `U`). The `Gext` analogue of
`incl_chart_aux`. -/
theorem Gext_chart_bridge {U : Opens X} (g : U → ℂ) {y : X} (hy : y ∈ U) :
    (chartAt (H := ℂ) (⟨y, hy⟩ : U)) ⟨y, hy⟩ = (chartAt (H := ℂ) y) y ∧
    (g ∘ (chartAt (H := ℂ) (⟨y, hy⟩ : U)).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) y) y)]
      (Gext g ∘ (chartAt (H := ℂ) y).symm) := by
  set u : U := ⟨y, hy⟩ with hu
  have hbase : (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) y) y := by
    simp only [hu, TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
      Set.restrict_apply]
  refine ⟨hbase, ?_⟩
  have ht1 : (chartAt (H := ℂ) u).target ∈ 𝓝 ((chartAt (H := ℂ) u) u) :=
    (chartAt (H := ℂ) u).open_target.mem_nhds
      ((chartAt (H := ℂ) u).map_source (mem_chart_source ℂ u))
  rw [hbase] at ht1
  refine Filter.eventuallyEq_of_mem ht1 fun w hw => ?_
  show g ((chartAt (H := ℂ) u).symm w) = Gext g ((chartAt (H := ℂ) y).symm w)
  have e1 : ((chartAt (H := ℂ) u).symm w).1 = (chartAt (H := ℂ) y).symm w := by
    simpa [Function.comp] using
      OpenPartialHomeomorph.subtypeRestr_symm_apply (e := chartAt (H := ℂ) y) ⟨u⟩ hw
  have hmem : (chartAt (H := ℂ) y).symm w ∈ U := e1 ▸ ((chartAt (H := ℂ) u).symm w).2
  rw [show Gext g ((chartAt (H := ℂ) y).symm w) = g ⟨(chartAt (H := ℂ) y).symm w, hmem⟩ from by
    simp only [Gext, dif_pos hmem]]
  congr 1
  exact Subtype.ext e1

/-- `Gext g` is meromorphic at `y ∈ U` (in `X`'s chart), given `g` meromorphic on `↥U`. -/
theorem Gext_meromorphicAt {U : Opens X} {g : U → ℂ} (hg : IsMeromorphic (U : Type _) g)
    {y : X} (hy : y ∈ U) :
    MeromorphicAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) := by
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g hy
  have hmer := hg ⟨y, hy⟩
  rw [hbase] at hmer
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds)

/-- The intrinsic order on `↥U` (`ordU g`) equals the order of `Gext g` read in `X`'s chart. -/
theorem ordU_eq_orderAt_Gext {U : Opens X} (g : U → ℂ) {y : X} (hy : y ∈ U) :
    ordU g ⟨y, hy⟩ =
      meromorphicOrderAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) := by
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g hy
  rw [ordU, hbase]
  exact meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)

/-- A local `𝒪₀` representative has nonnegative meromorphic order when read in the ambient chart.
This is the order half of the chart-disk germ/function bridge; raw representatives may still carry
removable point-value junk, so analyticity is stated for the normal form below. -/
theorem meromorphicOrderAt_Gext_nonneg_of_mem_OmegaD_zero {U : Opens X} {g : U → ℂ}
    (hg : g ∈ OmegaD (0 : Divisor X) U) {y : X} (hy : y ∈ U) :
    0 ≤ meromorphicOrderAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) := by
  have h := ((mem_OmegaD).1 hg).2 ⟨y, hy⟩
  simpa [ordU_eq_orderAt_Gext g hy] using h

/-- The normal-form representative of a local `𝒪₀` section is analytic in the ambient chart.  This is
the holomorphic half of the single-section germ/function bridge used by the chart-disk acyclicity
route: first replace the representative by its meromorphic normal form, then use nonnegative order. -/
theorem analyticAt_toMeromorphicNFAt_Gext_of_mem_OmegaD_zero {U : Opens X} {g : U → ℂ}
    (hg : g ∈ OmegaD (0 : Divisor X) U) {y : X} (hy : y ∈ U) :
    AnalyticAt ℂ
      (toMeromorphicNFAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y))
      ((chartAt (H := ℂ) y) y) := by
  set F := Gext g ∘ (chartAt (H := ℂ) y).symm
  set c := (chartAt (H := ℂ) y) y
  have hmer : MeromorphicAt F c := by
    simpa [F, c] using Gext_meromorphicAt ((mem_OmegaD).1 hg).1 hy
  have hNF : MeromorphicNFAt (toMeromorphicNFAt F c) c := meromorphicNFAt_toMeromorphicNFAt
  have hnonnegF : 0 ≤ meromorphicOrderAt F c := by
    simpa [F, c] using meromorphicOrderAt_Gext_nonneg_of_mem_OmegaD_zero hg hy
  have hnonnegNF : 0 ≤ meromorphicOrderAt (toMeromorphicNFAt F c) c := by
    rwa [← meromorphicOrderAt_congr hmer.eq_nhdsNE_toMeromorphicNFAt]
  exact hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 hnonnegNF

/-- The "normal form at `y`" predicate intrinsic to `X`: `h` read in `X`'s chart at `y` has
meromorphic normal form at the chart centre. -/
def nfX (h : X → ℂ) (y : X) : Prop :=
  MeromorphicNFAt (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)

/-- `Gext g` is in normal form at `y ∈ U` iff `g` is (read in `↥U`'s chart at `⟨y⟩`). -/
theorem nfX_Gext_iff {U : Opens X} (g : U → ℂ) {y : X} (hy : y ∈ U) :
    nfX (Gext g) y ↔
      MeromorphicNFAt (g ∘ (chartAt (H := ℂ) (⟨y, hy⟩ : U)).symm)
        ((chartAt (H := ℂ) (⟨y, hy⟩ : U)) ⟨y, hy⟩) := by
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g hy
  rw [nfX, hbase, meromorphicNFAt_congr hev]

/-- Transport a punctured-neighbourhood property from the open submanifold `↥V` to the ambient `X`:
since `↥V ↪ X` is an open embedding and `V ∈ 𝓝 x`, a `𝓝[≠] ⟨x⟩`-statement on `↥V` becomes the
corresponding `𝓝[≠] x`-statement on `X`. (`Subtype.val` maps `𝓝[≠] ⟨x⟩` to `𝓝[V\{x}] x = 𝓝[≠] x`.) -/
theorem eventually_nhdsNE_of_subtype {V : Opens X} {x : X} (hx : x ∈ V) (P : X → Prop)
    (h : ∀ᶠ w in 𝓝[≠] (⟨x, hx⟩ : V), P w.1) :
    ∀ᶠ z in 𝓝[≠] x, P z := by
  have hemb : Topology.IsEmbedding (Subtype.val : V → X) := Topology.IsEmbedding.subtypeVal
  have hmap : Filter.map (Subtype.val : V → X) (𝓝[≠] (⟨x, hx⟩ : V)) = 𝓝[≠] x := by
    rw [hemb.map_nhdsWithin_eq]
    have himg : (Subtype.val : V → X) '' ({(⟨x, hx⟩ : V)}ᶜ) = (V : Set X) \ {x} := by
      ext z
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_diff,
        SetLike.mem_coe]
      refine ⟨?_, ?_⟩
      · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, fun hc => hw (Subtype.ext hc)⟩
      · rintro ⟨hzV, hzx⟩; exact ⟨⟨z, hzV⟩, fun hc => hzx (congrArg Subtype.val hc), rfl⟩
    rw [himg, Set.diff_eq]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hx))
  have h2 : ∀ᶠ z in Filter.map (Subtype.val : V → X) (𝓝[≠] (⟨x, hx⟩ : V)), P z := by
    rw [Filter.eventually_map]; exact h
  rwa [hmap] at h2

/-- **Overlap agreement.** If two representatives' germs match after restriction to the overlap (the
Čech matching condition, via `rawRestrictG`), their extensions-by-zero `Gext` agree off a discrete
set near every overlap point. This is what makes the per-point normal forms glue *honestly*. -/
theorem Gext_overlap_eventuallyEq {U V : Opens X} (gU : U → ℂ) (gV : V → ℂ)
    (hmatch : rawRestrictG (inf_le_right : U ⊓ V ≤ V) (toGerm V gV)
      = rawRestrictG (inf_le_left : U ⊓ V ≤ U) (toGerm U gU))
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) :
    Gext gU =ᶠ[𝓝[≠] x] Gext gV := by
  rw [rawRestrictG_coe, rawRestrictG_coe, toGerm_eq_iff] at hmatch
  have hxUV : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  refine eventually_nhdsNE_of_subtype hxUV (fun z => Gext gU z = Gext gV z) ?_
  filter_upwards [hmatch ⟨x, hxUV⟩] with w hw
  rw [Gext_apply_mem gU w.2.1, Gext_apply_mem gV w.2.2]
  simp only [Function.comp_apply, openIncl] at hw
  exact hw.symm

/-! ### Per-point normal form: chart-transport and chart-invariance

The glued function is the per-point meromorphic *normal form* read in `X`'s chart at each point. Two
facts are needed: the normal-form *value* at the chart centre is germ-determined
(`toMeromorphicNFAt_chart_val_congr`), and *analyticity* (hence normal-form-ness) is chart-invariant
(`analyticAt_chart_change`, via the analytic transition maps of the `ω`-manifold `X`). -/

/-- Transport an `=ᶠ[𝓝[≠]]` from `X` to `X`'s chart at `x` (precompose with `chartAt x`'s inverse). -/
theorem eventuallyEq_comp_chart {a b : X → ℂ} {x : X} (h : a =ᶠ[𝓝[≠] x] b) :
    (a ∘ (chartAt (H := ℂ) x).symm) =ᶠ[𝓝[≠] ((chartAt (H := ℂ) x) x)]
      (b ∘ (chartAt (H := ℂ) x).symm) := by
  have key := (eventually_comp_chart_iff' (a - b) x (· = 0)).2
  simp only [Pi.sub_apply, sub_eq_zero] at key
  filter_upwards [key h] with w hw
  simp only [Function.comp_apply, Pi.sub_apply, sub_eq_zero] at hw ⊢
  exact hw

/-- The normal-form *value* at the chart centre depends only on the germ: if `a` and `b` agree off a
discrete set near `x` (and `a` is meromorphic in the chart), their per-point normal forms (read in
`X`'s chart at `x`) take equal value at the chart centre. The `MeromorphicNFAt` local-identity
theorem upgrades the punctured-neighbourhood agreement to a full-neighbourhood one. -/
theorem toMeromorphicNFAt_chart_val_congr {a b : X → ℂ} {x : X} (h : a =ᶠ[𝓝[≠] x] b)
    (hma : MeromorphicAt (a ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) :
    toMeromorphicNFAt (a ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
        ((chartAt (H := ℂ) x) x)
      = toMeromorphicNFAt (b ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
        ((chartAt (H := ℂ) x) x) := by
  set c := (chartAt (H := ℂ) x) x with hc
  set fa := a ∘ (chartAt (H := ℂ) x).symm with hfa
  set fb := b ∘ (chartAt (H := ℂ) x).symm with hfb
  have hab : fa =ᶠ[𝓝[≠] c] fb := eventuallyEq_comp_chart h
  have hmb : MeromorphicAt fb c := hma.congr hab
  have hnfa : MeromorphicNFAt (toMeromorphicNFAt fa c) c := meromorphicNFAt_toMeromorphicNFAt
  have hnfb : MeromorphicNFAt (toMeromorphicNFAt fb c) c := meromorphicNFAt_toMeromorphicNFAt
  have e1 : toMeromorphicNFAt fa c =ᶠ[𝓝[≠] c] fa := (hma.eq_nhdsNE_toMeromorphicNFAt).symm
  have e2 : fb =ᶠ[𝓝[≠] c] toMeromorphicNFAt fb c := hmb.eq_nhdsNE_toMeromorphicNFAt
  have echain : toMeromorphicNFAt fa c =ᶠ[𝓝[≠] c] toMeromorphicNFAt fb c :=
    e1.trans (hab.trans e2)
  exact ((hnfa.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hnfb).1 echain).eq_of_nhds

/-- The chart transition `chartAt y ∘ (chartAt z).symm` is analytic at `chartAt z z` (for `z` in the
source of `chartAt y`): chart and inverse-chart are `C^ω` (`contMDiffOn_chart`), and `C^ω = analytic`
(`ContDiffAt.analyticAt`) since the model `𝓘(ℂ)` is the identity. -/
theorem transition_analyticAt {y z : X} (hz : z ∈ (chartAt (H := ℂ) y).source) :
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

/-- The reverse of `eventually_nhdsNE_of_subtype`: pull a punctured-neighbourhood property on `X`
back to the open submanifold `↥V` (precompose with `Subtype.val`, which is continuous and injective
so tends `𝓝[≠] u → 𝓝[≠] u.1`). -/
theorem eventually_subtype_of_nhdsNE {V : Opens X} {u : V} (P : X → Prop)
    (h : ∀ᶠ z in 𝓝[≠] u.1, P z) : ∀ᶠ w : V in 𝓝[≠] u, P w.1 := by
  have htend : Filter.Tendsto (Subtype.val : V → X) (𝓝[≠] u) (𝓝[≠] u.1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨continuous_subtype_val.continuousAt.continuousWithinAt.tendsto, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards with w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
    exact fun hc => hw (Subtype.ext hc)
  exact htend.eventually h

/-- **Chart-invariance of analyticity.** If `h` read in the chart at `y` is analytic at the image of
`z` (with `z` in that chart's source), then `h` read in its *own* chart at `z` is analytic. Composes
with the analytic transition map (`transition_analyticAt`). -/
theorem analyticAt_chart_change {h : X → ℂ} {y z : X} (hz : z ∈ (chartAt (H := ℂ) y).source)
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) z)) :
    AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := by
  have hcz_tgt : (chartAt (H := ℂ) z) z ∈ (chartAt (H := ℂ) z).target :=
    (chartAt (H := ℂ) z).map_source (mem_chart_source ℂ z)
  have hez : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) = z :=
    (chartAt (H := ℂ) z).left_inv (mem_chart_source ℂ z)
  have hφ := transition_analyticAt (y := y) (z := z) hz
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

/-! ### The forward map `L(D) → H⁰(𝔘, 𝒪_D)` -/

namespace FiniteCover

-- The Čech complex (`cechDelta0`, `globalSections`, `h0Dim`, …) lives on the parent `FiniteFamily`;
-- open it so the unqualified `rw`/`simp` unfold-lemma references below resolve.
open FiniteFamily

variable (𝔘 : FiniteCover X) (D : Divisor X)

/-- Restrict a global meromorphic function to the cover's germ-class 0-cochains:
`F ↦ (i ↦ [F|_{U i}])`. `ℂ`-linear (depends only on the cover, not on `D`). -/
noncomputable def cechRestrict : MeromorphicFunction X →ₗ[ℂ] 𝔘.Cochain0 where
  toFun F i := toGerm (𝔘.U i) (F.toFun ∘ Subtype.val)
  map_add' F G := by funext i; exact (map_add (toGerm (𝔘.U i)) _ _)
  map_smul' c F := by funext i; exact (map_smul (toGerm (𝔘.U i)) _ _)

@[simp] theorem cechRestrict_apply (F : MeromorphicFunction X) (i : 𝔘.ι) :
    𝔘.cechRestrict F i = toGerm (𝔘.U i) (F.toFun ∘ Subtype.val) := rfl

/-- The restriction of `F ∈ L(D)` is a global matching `𝒪_D`-section: each component is an
`𝒪_D`-germ (keystone: `ordU = orderW ≥ −D`), and the components match on overlaps automatically
(both restrict the *same* `F`). -/
theorem cechRestrict_mem_globalSections {F : MeromorphicFunction X}
    (hF : F ∈ linearSystem D) : 𝔘.cechRestrict F ∈ 𝔘.globalSections D := by
  rw [globalSections, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · -- matching: `cechRestrict F ∈ ker δ⁰`
    rw [LinearMap.mem_ker]
    funext p
    obtain ⟨i, j⟩ := p
    simp only [cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, cechRestrict_apply, rawRestrictG_coe, Pi.zero_apply]
    rw [sub_eq_zero]
    rfl
  · -- sections: each component is an `𝒪_D`-germ
    intro i
    refine ⟨F.toFun ∘ Subtype.val, ⟨isMeromorphic_val F, fun u => ?_⟩, rfl⟩
    rw [ordU_val_eq_orderW]
    exact hF u.1

/-- The forward map `Φ : L(D) →ₗ globalSections D` (domain/codomain restriction of `cechRestrict`). -/
noncomputable def cechRestrictL :
    linearSystem (X := X) D →ₗ[ℂ] ↥(𝔘.globalSections D) :=
  ((𝔘.cechRestrict).domRestrict (linearSystem D)).codRestrict (𝔘.globalSections D)
    fun F => 𝔘.cechRestrict_mem_globalSections D F.2

@[simp] theorem cechRestrictL_coe (F : linearSystem (X := X) D) :
    (𝔘.cechRestrictL D F : 𝔘.Cochain0) = 𝔘.cechRestrict (F : MeromorphicFunction X) := rfl

/-- The restriction of `F` is the zero cochain iff `F` is germ-zero junk everywhere (`orderW ≡ ⊤`).
Uses the keystone (`ordU = orderW`), the germ-zero bridge, and that the `U i` cover `X`. -/
theorem cechRestrict_eq_zero_iff (F : MeromorphicFunction X) :
    𝔘.cechRestrict F = 0 ↔ ∀ x, F.orderW x = ⊤ := by
  rw [funext_iff]
  simp only [cechRestrict_apply, Pi.zero_apply, toGerm_eq_zero_iff, ← ordU_eq_top_iff,
    ordU_val_eq_orderW]
  constructor
  · intro h x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (𝔘.covers ▸ Set.mem_univ x :
      x ∈ ⨆ i, 𝔘.U i)
    exact h i ⟨x, hi⟩
  · intro h i u
    exact h u.1

/-- The kernel of the descended forward map is exactly the germ-zero junk: `Φ` descends to an
*injective* map `L(D) ⧸ germZero ↪ H⁰`. -/
theorem ker_cechRestrictL :
    LinearMap.ker (𝔘.cechRestrictL D) = (germZeroSubmodule).submoduleOf (linearSystem D) := by
  ext F
  rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero, cechRestrictL_coe,
    𝔘.cechRestrict_eq_zero_iff]
  exact Iff.rfl

/-! ### Gluing (surjectivity) — the crux -/

/-- The per-point glued function: at `x`, the meromorphic *normal-form* value of the local member
`G (idx x)` read in `X`'s chart at `x`. -/
noncomputable def gluedFun (G : 𝔘.ι → X → ℂ) (idx : X → 𝔘.ι) : X → ℂ :=
  fun x => toMeromorphicNFAt (G (idx x) ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
    ((chartAt (H := ℂ) x) x)

/-- **NF-codiscreteness on `X`.** Near every `y ∈ U i`, the extension `Gext g` is in normal form
(`nfX`, intrinsic to `X`'s per-point charts) off a discrete set: `Gext g` is meromorphic at `y`, so
analytic at codiscretely-many nearby chart points, and analyticity is chart-invariant
(`analyticAt_chart_change`), giving `nfX` at the point's own chart. -/
theorem nfX_Gext_codiscrete {i : 𝔘.ι} {g : 𝔘.U i → ℂ} (hg : IsMeromorphic (𝔘.U i : Type _) g)
    {y : X} (hy : y ∈ 𝔘.U i) :
    ∀ᶠ z in 𝓝[≠] y, nfX (Gext g) z := by
  have hmer : MeromorphicAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) :=
    Gext_meromorphicAt hg hy
  have hana : ∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) y) y),
      AnalyticAt ℂ (Gext g ∘ (chartAt (H := ℂ) y).symm) w := hmer.eventually_analyticAt
  have htend : Filter.Tendsto (chartAt (H := ℂ) y) (𝓝[≠] y) (𝓝[≠] ((chartAt (H := ℂ) y) y)) := by
    have hy' : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
    rw [tendsto_nhdsWithin_iff]
    refine ⟨((chartAt (H := ℂ) y).continuousAt hy').continuousWithinAt.tendsto, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [(chartAt (H := ℂ) y).open_source.mem_nhds hy'] with z hz hzne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hzne ⊢
    exact fun hc => hzne ((chartAt (H := ℂ) y).injOn hz hy' hc)
  have hana' : ∀ᶠ z in 𝓝[≠] y,
      AnalyticAt ℂ (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) z) :=
    htend.eventually hana
  have hsrc : ∀ᶠ z in 𝓝[≠] y, z ∈ (chartAt (H := ℂ) y).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt (H := ℂ) y).open_source.mem_nhds (mem_chart_source ℂ y))
  filter_upwards [hana', hsrc] with z hz hzsrc
  exact (analyticAt_chart_change hzsrc hz).meromorphicNFAt

/-- **Central gluing property.** The glued function agrees off a discrete set near every point with
the local family member `G i` whose patch `U i` contains that point. Hence (downstream) `gluedFun` is
meromorphic, satisfies the order bound, and restricts to the prescribed germ on each `U i`.

Needs: every point lies in `U (idx ·)` (`hidx`); each `G i` meromorphic on `U i` (`hmer`); the family
agrees off a discrete set on overlaps (`hoverlap`); and `G i` is normal-form-codiscrete near `U i`
(`hnf`). The proof: on the `𝓝[≠] y` set where `z ∈ U i` and `G i` is `nfX` at `z`, idx-independence
(`toMeromorphicNFAt_chart_val_congr` + `hoverlap`) rewrites `gluedFun z` to the normal form of `G i`,
which (being already normal form) equals `G i z` (`toMeromorphicNFAt_eq_self`). -/
theorem gluedFun_eventuallyEq (G : 𝔘.ι → X → ℂ) (idx : X → 𝔘.ι)
    (hidx : ∀ x, x ∈ 𝔘.U (idx x))
    (hmer : ∀ i, ∀ y, y ∈ 𝔘.U i →
      MeromorphicAt (G i ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y))
    (hoverlap : ∀ i j, ∀ x, x ∈ 𝔘.U i → x ∈ 𝔘.U j → G i =ᶠ[𝓝[≠] x] G j)
    (hnf : ∀ i, ∀ y, y ∈ 𝔘.U i → ∀ᶠ z in 𝓝[≠] y, nfX (G i) z)
    {y : X} {i : 𝔘.ι} (hy : y ∈ 𝔘.U i) :
    𝔘.gluedFun G idx =ᶠ[𝓝[≠] y] G i := by
  have hUi : ∀ᶠ z in 𝓝[≠] y, z ∈ 𝔘.U i :=
    eventually_nhdsWithin_of_eventually_nhds ((𝔘.U i).isOpen.mem_nhds hy)
  filter_upwards [hUi, hnf i y hy] with z hz hznf
  show toMeromorphicNFAt (G (idx z) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z)
      ((chartAt (H := ℂ) z) z) = G i z
  rw [toMeromorphicNFAt_chart_val_congr (hoverlap (idx z) i z (hidx z) hz)
    (hmer (idx z) z (hidx z))]
  have hnfz : MeromorphicNFAt (G i ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := hznf
  rw [toMeromorphicNFAt_eq_self.mpr hnfz]
  simp only [Function.comp_apply, OpenPartialHomeomorph.left_inv _ (mem_chart_source ℂ z)]

/-- **Gluing.** Every global matching `𝒪_D`-section over the cover glues to a single global
meromorphic function in `L(D)`.

CONSTRUCTION (rigidified normal-form gluing; the naive pointwise patch `x ↦ g_{idx x} x` is *not*
meromorphic at cover-boundary points because the per-overlap disagreement set is only codiscrete
*within* the overlap). Extract honest representatives `g i ∈ OmegaD D (U i)` with `[g i] = f i`
(choice on `OmegaDGerm = map toGerm`). Extend each by `0` to `Gext i : X → ℂ`. Define

  `F.toFun x := toMeromorphicNFAt (Gext (idx x) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) (chartAt ℂ x x)`

(the per-point normal-form value; `idx x` any index with `x ∈ U i`).
  * **idx-independent**: the nf value at `x` depends only on the germ at `x`; the matching gives
    `Gext i =ᶠ[𝓝[≠] x] Gext j` on overlaps, so (read in the shared chart `chartAt ℂ x`) the nf values
    agree by NF-uniqueness (`MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`).
  * **`F =ᶠ[𝓝[≠] y] Gext i` for `y ∈ U i`**: the normal form repairs only a *codiscrete* set
    (`analyticAt_mem_codiscreteWithin`; `toMeromorphicNFAt = id` on nf-points,
    `eq_nhdsNE_toMeromorphicNFAt`), so `F` and `Gext i` agree off a discrete set ⟹ `F` meromorphic at
    `y` and (keystone `ordU = orderW`) `orderW F ≥ −D` ⟹ `F ∈ L(D)`; and `[F|_{U i}] = [g i] = f i`. -/
theorem cechRestrictL_surjective : Function.Surjective (𝔘.cechRestrictL D) := by
  intro f
  obtain ⟨fc, hfc⟩ := f
  rw [globalSections, Submodule.mem_inf] at hfc
  obtain ⟨hker, hsec⟩ := hfc
  -- Extract honest representatives `g i ∈ OmegaD D (U i)` with `[g i] = fc i`.
  have hchoose : ∀ i, ∃ g : 𝔘.U i → ℂ, g ∈ OmegaD D (𝔘.U i) ∧ toGerm (𝔘.U i) g = fc i :=
    fun i => let ⟨g, hg, hgeq⟩ := hsec i; ⟨g, hg, hgeq⟩
  choose g hg_mem hg_rep using hchoose
  have hg_mer : ∀ i, IsMeromorphic (𝔘.U i : Type _) (g i) := fun i => ((mem_OmegaD).1 (hg_mem i)).1
  have hg_ord : ∀ i, ∀ u : 𝔘.U i, (-(D u.1) : WithTop ℤ) ≤ ordU (g i) u :=
    fun i => ((mem_OmegaD).1 (hg_mem i)).2
  -- A choice of patch index for each point.
  have hcov : ∀ x : X, ∃ i, x ∈ 𝔘.U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (𝔘.covers ▸ Set.mem_univ x : x ∈ ⨆ i, 𝔘.U i)
  choose idx hidx using hcov
  -- The matching condition (from `ker δ⁰`).
  rw [LinearMap.mem_ker] at hker
  have hmatch : ∀ i j, rawRestrictG (inf_le_right : 𝔘.U i ⊓ 𝔘.U j ≤ 𝔘.U j) (fc j)
      = rawRestrictG (inf_le_left : 𝔘.U i ⊓ 𝔘.U j ≤ 𝔘.U i) (fc i) := by
    intro i j
    have hp := congrFun hker (i, j)
    simp only [cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Pi.zero_apply] at hp
    rwa [sub_eq_zero] at hp
  -- The family of extensions-by-zero, and the four hypotheses of `gluedFun_eventuallyEq`.
  set G : 𝔘.ι → X → ℂ := fun i => Gext (g i) with hG
  have Hmer : ∀ i, ∀ y, y ∈ 𝔘.U i →
      MeromorphicAt (G i ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) :=
    fun i y hy => Gext_meromorphicAt (hg_mer i) hy
  have Hoverlap : ∀ i j, ∀ x, x ∈ 𝔘.U i → x ∈ 𝔘.U j → G i =ᶠ[𝓝[≠] x] G j := by
    intro i j x hxi hxj
    have hm := hmatch i j
    rw [← hg_rep i, ← hg_rep j] at hm
    exact Gext_overlap_eventuallyEq (g i) (g j) hm hxi hxj
  have Hnf : ∀ i, ∀ y, y ∈ 𝔘.U i → ∀ᶠ z in 𝓝[≠] y, nfX (G i) z :=
    fun i y hy => 𝔘.nfX_Gext_codiscrete (hg_mer i) hy
  -- The glued function and its central agreement property.
  have hF_ev : ∀ {y : X} {i : 𝔘.ι}, y ∈ 𝔘.U i → 𝔘.gluedFun G idx =ᶠ[𝓝[≠] y] G i :=
    fun {y i} hy => 𝔘.gluedFun_eventuallyEq G idx hidx Hmer Hoverlap Hnf hy
  -- `gluedFun` is meromorphic on `X` (it agrees with a meromorphic `G i` near every point).
  have hmer_F : IsMeromorphic X (𝔘.gluedFun G idx) := fun x =>
    (Hmer (idx x) x (hidx x)).congr (eventuallyEq_comp_chart (hF_ev (hidx x))).symm
  refine ⟨⟨⟨𝔘.gluedFun G idx, hmer_F⟩, ?_⟩, ?_⟩
  · -- `F ∈ linearSystem D`: at each `x`, `orderW F x = ordU (g (idx x)) ⟨x⟩ ≥ -(D x)`.
    intro x
    show (-(D x) : WithTop ℤ) ≤ MeromorphicFunction.orderW ⟨𝔘.gluedFun G idx, hmer_F⟩ x
    rw [MeromorphicFunction.orderW,
      meromorphicOrderAt_congr (eventuallyEq_comp_chart (hF_ev (hidx x)))]
    simp only [hG]
    rw [← ordU_eq_orderAt_Gext (g (idx x)) (hidx x)]
    exact hg_ord (idx x) ⟨x, hidx x⟩
  · -- `cechRestrict ↑F = fc`: each component's germ is `[g i] = fc i`.
    apply Subtype.ext
    rw [cechRestrictL_coe]
    funext i
    rw [cechRestrict_apply]
    show toGerm (𝔘.U i) ((𝔘.gluedFun G idx) ∘ Subtype.val) = fc i
    rw [← hg_rep i, toGerm_eq_iff]
    intro u
    have hsub := eventually_subtype_of_nhdsNE (fun z => 𝔘.gluedFun G idx z = G i z)
      (hF_ev (y := u.1) (i := i) u.2)
    filter_upwards [hsub] with w hw
    simp only [Function.comp_apply, hG] at hw ⊢
    rw [hw, Gext_apply_mem (g i) w.2]

/-- `H⁰(𝔘, 𝒪_D) ≅ L(D) ⧸ germZero` as `ℂ`-modules (first isomorphism theorem + `ker = germZero`). -/
noncomputable def globalSectionsEquivQuot :
    (linearSystem (X := X) D ⧸ (germZeroSubmodule (X := X)).submoduleOf (linearSystem D))
      ≃ₗ[ℂ] ↥(𝔘.globalSections D) :=
  (Submodule.quotEquivOfEq _ _ (𝔘.ker_cechRestrictL D).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (𝔘.cechRestrictL_surjective D))

/-- **The bridge leaf** `h⁰(𝔘, 𝒪_D) = l(D)` — Čech global sections agree with the linear system. -/
theorem h0Dim_eq_lDim (D : Divisor X) : 𝔘.h0Dim D = lDim D := by
  rw [h0Dim, lDim]
  exact ((𝔘.globalSectionsEquivQuot D).finrank_eq).symm

end FiniteCover

end Jacobians.Dolbeault
