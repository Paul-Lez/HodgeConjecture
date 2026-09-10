/-
  Čech finiteness — the germ ↔ sup-norm comparison ("K-bridge"), manifold side.

  Part of discharging `exists_cechModel` (Forster 14.9).
  Companion to `CechModelBridge.lean` (the `BddHol` codomain side). Here: the chart-pullback of a
  holomorphic `𝒪`-section is `AnalyticOn` the chart-image — the analyticity hypothesis that
  `BddHol.ofAnalyticOn` consumes.

  The natural holomorphy datum is stated in each point's OWN chart (matching `ordU`/`OmegaD`), so we
  first build the missing **point-level** chart-change: `CechH0.analyticAt_chart_change` and
  `transition_analyticAt` only act at a chart's *centre*; we need analyticity transported to a fixed
  cover-chart `y` at an arbitrary point `x` of the overlap. `transition_analyticAt_of_mem` (the
  transition map analytic at any overlap point) and `analyticAt_chart_change_to` (own-chart →
  cover-chart `y`) provide that, then `analyticOn_pullback_of_holo` packages it.

  Sorry-free; reuses only the axiom-clean chart machinery (`contMDiffOn_chart`, `ContDiffAt.analyticAt`).
-/
import KirovDolbeault.Dolbeault.CechH0
import KirovDolbeault.Dolbeault.CechModelBridge
import KirovDolbeault.Dolbeault.CechDiskAcyclicAssembly

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- **The chart transition `chartAt z ∘ (chartAt y).symm` is analytic at `chartAt y x`** for any
point `x` in the overlap of the two chart sources (generalizes `transition_analyticAt`, which is the
case `x = z` = chart centre). Chart and inverse-chart are `C^ω`, composition `C^ω`, `C^ω = analytic`. -/
theorem transition_analyticAt_of_mem {y z x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxz : x ∈ (chartAt (H := ℂ) z).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  have hw_tgt : (chartAt (H := ℂ) y) x ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hxy
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := y)) _ hw_tgt).contMDiffAt
      ((chartAt (H := ℂ) y).open_target.mem_nhds hw_tgt)
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) = x :=
    (chartAt (H := ℂ) y).left_inv hxy
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) z)
      ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x)) := by
    rw [hey]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := z)) _ hxz).contMDiffAt
      ((chartAt (H := ℂ) z).open_source.mem_nhds hxz)
  exact (contMDiffAt_iff_contDiffAt.1
    (ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt (H := ℂ) y) x) h2 h1)).analyticAt

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- **The chart transition `chartAt z ∘ (chartAt y).symm` has nonvanishing derivative at `chartAt y x`**
for any point `x` in the overlap of the two chart sources.  The transition is a biholomorphism: its
inverse `chartAt y ∘ (chartAt z).symm` (analytic by `transition_analyticAt_of_mem`) composes with it to
the identity near `chartAt y x`, so the chain rule forces the derivative to be nonzero.  Companion to
`transition_analyticAt_of_mem`; the pair is exactly the hypothesis bundle of Mathlib's
`meromorphicOrderAt_comp_of_deriv_ne_zero`. -/
theorem transition_deriv_ne_zero {y z x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxz : x ∈ (chartAt (H := ℂ) z).source) :
    deriv ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) ≠ 0 := by
  set yc := (chartAt (H := ℂ) y) x with hyc
  have hψ : AnalyticAt ℂ ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) yc :=
    transition_analyticAt_of_mem hxy hxz
  have hψ_pt : ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) yc = (chartAt (H := ℂ) z) x := by
    simp only [hyc, Function.comp_apply, (chartAt (H := ℂ) y).left_inv hxy]
  have hψ' : AnalyticAt ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)
      ((chartAt (H := ℂ) z) x) := transition_analyticAt_of_mem hxz hxy
  -- `(chartAt y ∘ (chartAt z).symm) ∘ (chartAt z ∘ (chartAt y).symm) =ᶠ id` near `yc`.
  have hwy_tgt : yc ∈ (chartAt (H := ℂ) y).target := hyc ▸ (chartAt (H := ℂ) y).map_source hxy
  have hmem : ∀ᶠ w in 𝓝 yc, (chartAt (H := ℂ) y).symm w ∈ (chartAt (H := ℂ) z).source := by
    have hcont : ContinuousAt (chartAt (H := ℂ) y).symm yc :=
      (chartAt (H := ℂ) y).continuousAt_symm hwy_tgt
    have hh : (chartAt (H := ℂ) y).symm yc ∈ (chartAt (H := ℂ) z).source := by
      rw [hyc, (chartAt (H := ℂ) y).left_inv hxy]; exact hxz
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) z).open_source.mem_nhds hh)
  have hmem_tgt : ∀ᶠ w in 𝓝 yc, w ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).open_target.mem_nhds hwy_tgt
  have hcomp_id : (((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm) ∘
      ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm)) =ᶠ[𝓝 yc] id := by
    filter_upwards [hmem, hmem_tgt] with w hw hwt
    show (chartAt (H := ℂ) y) ((chartAt (H := ℂ) z).symm
        ((chartAt (H := ℂ) z) ((chartAt (H := ℂ) y).symm w))) = w
    rw [(chartAt (H := ℂ) z).left_inv hw, (chartAt (H := ℂ) y).right_inv hwt]
  intro hderiv0
  have hdiff_inner : DifferentiableAt ℂ ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) yc :=
    hψ.differentiableAt
  have hdiff_outer : DifferentiableAt ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)
      (((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) yc) := hψ_pt ▸ hψ'.differentiableAt
  have hchain := deriv_comp yc hdiff_outer hdiff_inner
  rw [hcomp_id.deriv_eq, deriv_id, hderiv0, mul_zero] at hchain
  exact one_ne_zero hchain

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- **Own-chart → cover-chart analyticity.** If `h` read in its *own* chart at `x` is analytic, then
`h` read in the cover-chart `y` is analytic at `chartAt y x` (for `x` in that chart's source). The
reverse of `CechH0.analyticAt_chart_change`, at a general point. -/
theorem analyticAt_chart_change_to {h : X → ℂ} {y x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source)
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) :
    AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  have hxx : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  have hwy_tgt : (chartAt (H := ℂ) y) x ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hxy
  have hφ := transition_analyticAt_of_mem (y := y) (z := x) hxy hxx
  have hφ_pt : ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x)
      = (chartAt (H := ℂ) x) x := by
    simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hxy]
  have hcomp : AnalyticAt ℂ ((h ∘ (chartAt (H := ℂ) x).symm) ∘
      ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm)) ((chartAt (H := ℂ) y) x) :=
    AnalyticAt.comp (hφ_pt ▸ ha) hφ
  have hmem : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) x),
      (chartAt (H := ℂ) y).symm w ∈ (chartAt (H := ℂ) x).source := by
    have hcont : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) :=
      (chartAt (H := ℂ) y).continuousAt_symm hwy_tgt
    have hh : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) ∈ (chartAt (H := ℂ) x).source := by
      rw [(chartAt (H := ℂ) y).left_inv hxy]; exact hxx
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) x).open_source.mem_nhds hh)
  have heq : (h ∘ (chartAt (H := ℂ) y).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) y) x)]
      ((h ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ (chartAt (H := ℂ) y).symm)) := by
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv hw]
  rw [analyticAt_congr heq]; exact hcomp
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- **The chart-pullback of a holomorphic section is `AnalyticOn` the chart-image.**  If `h` is
holomorphic on `V ⊆ (chartAt y).source` (analytic in each point's own chart), then `h ∘ (chartAt y).symm`
is analytic on `(chartAt y) '' V`.  This is the analyticity input to `BddHol.ofAnalyticOn`. -/
theorem analyticOn_pullback_of_holo {y : X} {V : Set X} (hV : V ⊆ (chartAt (H := ℂ) y).source)
    {h : X → ℂ} (hh : ∀ x ∈ V, AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) :
    AnalyticOn ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) '' V) := by
  rintro w ⟨x, hxV, rfl⟩
  exact (analyticAt_chart_change_to (hV hxV) (hh x hxV)).analyticWithinAt

/-- **The single-section K-bridge.**  A holomorphic `𝒪₀` section `h` on `V ⊆ (chartAt y).source`,
read through the cover-chart `y` and restricted to a relatively-compact open `U' ⋐ (chartAt y) '' V`,
is a `BddHol U'` element (analytic via `analyticOn_pullback_of_holo`, bounded via the
relatively-compact shrinking).  The value is the section's chart-pullback `h ∘ (chartAt y).symm`.
This is the per-overlap building block of the germ→`BddHol` cochain map (`exists_cechModel`). -/
noncomputable def holoSectionToBddHol {y : X} {V : Set X} (hV : V ⊆ (chartAt (H := ℂ) y).source)
    {h : X → ℂ} (hh : ∀ x ∈ V, AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x))
    {U' : Set ℂ} (hsub : closure U' ⊆ (chartAt (H := ℂ) y) '' V) (hcpt : IsCompact (closure U')) :
    BddHol U' :=
  BddHol.ofAnalyticOnOfRelCompact (analyticOn_pullback_of_holo hV hh) hsub hcpt

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
@[simp] theorem holoSectionToBddHol_toFun_of_mem {y : X} {V : Set X}
    (hV : V ⊆ (chartAt (H := ℂ) y).source) {h : X → ℂ}
    (hh : ∀ x ∈ V, AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x))
    {U' : Set ℂ} (hsub : closure U' ⊆ (chartAt (H := ℂ) y) '' V) (hcpt : IsCompact (closure U'))
    {z : ℂ} (hz : z ∈ U') :
    (holoSectionToBddHol hV hh hsub hcpt).toFun z = h ((chartAt (H := ℂ) y).symm z) :=
  BddHol.ofAnalyticOnOfRelCompact_toFun_of_mem _ _ _ hz

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- **Inverse local K-bridge atom.** A bounded holomorphic function on an open chart-image `U'`
pulls back along a chart to a function that is analytic in each point's own chart, provided the
chart value lands in `U'`. This is the local analytic input for the `BddHol → OmegaD 0` direction. -/
theorem bddHol_pullback_analyticAt {y x : X} {U' : Set ℂ} (hU' : IsOpen U')
    (g : BddHol U') (hx : x ∈ (chartAt (H := ℂ) y).source)
    (hmem : (chartAt (H := ℂ) y) x ∈ U') :
    AnalyticAt ℂ
      ((fun z : X => g.toFun ((chartAt (H := ℂ) y) z)) ∘ (chartAt (H := ℂ) x).symm)
      ((chartAt (H := ℂ) x) x) := by
  have hga : AnalyticAt ℂ g.toFun ((chartAt (H := ℂ) y) x) :=
    g.analyticOn.analyticAt (hU'.mem_nhds hmem)
  have htrans : AnalyticAt ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) x).symm)
      ((chartAt (H := ℂ) x) x) :=
    transition_analyticAt_of_mem (y := x) (z := y) (x := x) (mem_chart_source ℂ x) hx
  have hpt :
      ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) =
        (chartAt (H := ℂ) y) x := by
    simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv (mem_chart_source ℂ x)]
  have hcomp :
      AnalyticAt ℂ (g.toFun ∘ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) x).symm))
        ((chartAt (H := ℂ) x) x) :=
    AnalyticAt.comp (hpt ▸ hga) htrans
  simpa [Function.comp, Function.comp_assoc] using hcomp

/-- **Inverse K-bridge to `OmegaD 0`.** A bounded holomorphic function on an open chart-image can be
pulled back along a chart to a holomorphic section on the corresponding open domain in `X`. This is
the missing inverse atom for the `BddHol ↔ OmegaD 0` comparison direction. -/
theorem bddHol_pullback_mem_OmegaD_zero {y : X} {V : Opens X} {U' : Set ℂ}
    (hV : (V : Set X) ⊆ (chartAt (H := ℂ) y).source) (hU' : IsOpen U')
    (himg : (chartAt (H := ℂ) y) '' (V : Set X) ⊆ U') (g : BddHol U') :
    ((fun x : X => g.toFun ((chartAt (H := ℂ) y) x)) ∘ (Subtype.val : V → X)) ∈
      OmegaD (0 : Divisor X) V := by
  refine omegaD_zero_of_chart_analyticAt ?_
  intro v hv
  have hmem : (chartAt (H := ℂ) y) (v : X) ∈ U' := himg ⟨v, hv, rfl⟩
  simpa using bddHol_pullback_analyticAt (y := y) (x := v) (U' := U') hU' g (hV hv) hmem

/-- **Exact-image inverse K-bridge.** If the `BddHol` domain is exactly the chart image of an open
`V`, then pulling back along the chart gives a holomorphic `OmegaD 0`-section on `V`. This is the
clean local inverse on exact chart-image domains. -/
theorem bddHol_pullback_mem_OmegaD_zero_image {y : X} {V : Opens X}
    (hV : (V : Set X) ⊆ (chartAt (H := ℂ) y).source)
    (g : BddHol ((chartAt (H := ℂ) y) '' (V : Set X))) :
    ((fun x : X => g.toFun ((chartAt (H := ℂ) y) x)) ∘ (Subtype.val : V → X)) ∈
      OmegaD (0 : Divisor X) V := by
  refine bddHol_pullback_mem_OmegaD_zero (y := y) (V := V)
      hV (U' := (chartAt (H := ℂ) y) '' (V : Set X))
      (show IsOpen ((chartAt (H := ℂ) y) '' (V : Set X)) from
        (chartAt (H := ℂ) y).isOpen_image_of_subset_source V.isOpen hV)
      (by
        intro z hz
        exact hz) g

/-- **Inverse exact-image K-bridge as a linear map.**  Pulling a `BddHol` function back along the
chart on the exact image of `V` yields an `OmegaD 0` section of `V`. -/
noncomputable def bddHolToOmegaD_zero_image {y : X} {V : Opens X}
    (hV : (V : Set X) ⊆ (chartAt (H := ℂ) y).source) :
    BddHol ((chartAt (H := ℂ) y) '' (V : Set X)) →ₗ[ℂ] OmegaD (0 : Divisor X) V where
  toFun g :=
    ⟨fun x : V => g.toFun ((chartAt (H := ℂ) y) x),
      bddHol_pullback_mem_OmegaD_zero_image (y := y) hV g⟩
  map_add' g₁ g₂ := by
    ext x
    rfl
  map_smul' c g := by
    ext x
    rfl

/-- **Inverse exact-image K-bridge at the germ level.** Pulling a `BddHol` function back along the
chart on the exact image of `V` yields an `OmegaDGerm 0` section of `V`. This is the germ-class
version of `bddHolToOmegaD_zero_image`, and the bridge the cochain comparison can consume. -/
noncomputable def bddHolToOmegaDGerm_zero_image {y : X} {V : Opens X}
    (hV : (V : Set X) ⊆ (chartAt (H := ℂ) y).source) :
    BddHol ((chartAt (H := ℂ) y) '' (V : Set X)) →ₗ[ℂ] OmegaDGerm (0 : Divisor X) V where
  toFun g :=
    ⟨toGerm V (fun x : V => g.toFun ((chartAt (H := ℂ) y) x)),
      ⟨fun x : V => g.toFun ((chartAt (H := ℂ) y) x),
        bddHol_pullback_mem_OmegaD_zero_image (y := y) hV g, rfl⟩⟩
  map_add' g₁ g₂ := by
    ext
    rfl
  map_smul' c g := by
    ext
    rfl

/-- **Inverse exact-image K-bridge as a linear map.**  Pulling a `BddHol` function back along the
chart on the exact image of `V` yields an `OmegaD 0` section of `V`. -/
noncomputable def bddHolToOmegaD_zero {y : X} {V : Opens X}
    (hV : (V : Set X) ⊆ (chartAt (H := ℂ) y).source) :
    BddHol ((chartAt (H := ℂ) y) '' (V : Set X)) →ₗ[ℂ] OmegaD (0 : Divisor X) V where
  toFun g :=
    ⟨fun x : V => g.toFun ((chartAt (H := ℂ) y) x),
      bddHol_pullback_mem_OmegaD_zero_image (y := y) hV g⟩
  map_add' g₁ g₂ := by
    ext x
    rfl
  map_smul' c g := by
    ext x
    rfl

end Jacobians.Dolbeault
