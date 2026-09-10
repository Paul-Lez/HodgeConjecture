/-
  Čech finiteness — the germ → `BddHol` cochain map (forward direction of `cechH1 ≃ supH1`).

  Part of discharging `exists_cechModel` (Forster 14.9).
  The comparison `cechH1 𝔘 D ≃ supH1` translates germ-class `𝒪_D` cochains (the `cechH1`
  representation) into `BddHol` cochains on chart-images (the `supH1`/Montel representation). This file
  builds its **forward direction at the section/cochain level**: from a germ-class holomorphic section
  on an overlap to a `BddHol` element on the (relatively-compact) chart-image, packaged as a `ℂ`-linear
  map, together with the assembled cochain map into a `DiskOverlapData.Ccov` indexed by a geometric
  overlap model.

  Design.  A germ-class section `g ∈ OmegaDGerm 0 V` (`V` an open `⊆ (chartAt y).source`) has a
  choice-free analytic representative `holoFn hg : X → ℂ` (`DolbeaultComparisonInverse`), chart-analytic
  at every point of `V` (`gextLimRep_chart_analyticAt`) and depending only on the germ class
  (`holoFn_congr`, `holoFn_add`, `holoFn_smul`).  Restricted to a relatively-compact open
  `U' ⋐ (chartAt y) '' V`, its chart-pullback is the K-bridge atom `holoSectionToBddHol`
  (`CechModelManifold`).  Because `holoFn` is additive/homogeneous/germ-invariant, this assignment is a
  `ℂ`-linear map on the germ-class section module — the per-overlap building block of the forward
  cochain map.

  Sorry-free; depends only on the axiom-clean K-bridge atom (`holoSectionToBddHol`), the analytic
  representative API (`holoFn`), and the geometric overlap data (`chartCoverOverlapData`).
-/
import KirovDolbeault.Dolbeault.CechModelGeometry
import KirovDolbeault.Dolbeault.CechModelManifold
import KirovDolbeault.Dolbeault.CechFinitenessBallSolve

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Per-overlap atom: a germ-class holomorphic section ↦ a `BddHol` on the chart-image

For `V` open `⊆ (chartAt y).source` and a relatively-compact open `U' ⋐ (chartAt y) '' V`, the
analytic representative `holoFn` of an `OmegaDGerm 0 V` class gives a `BddHol U'` (value
`holoFn hg ∘ (chartAt y).symm`).  We bundle this per-overlap assignment as a `ℂ`-linear map. -/

section Atom

variable {y : X} {V : Opens X} (hV : (V : Set X) ⊆ (chartAt (H := ℂ) y).source)
    {U' : Set ℂ} (hsub : closure U' ⊆ (chartAt (H := ℂ) y) '' (V : Set X))
    (hcpt : IsCompact (closure U'))

/-- The analytic representative `holoFn hg` is analytic at every point of `V` in that point's OWN
chart — exactly the `holoSectionToBddHol` hypothesis. This is `gextLimRep_chart_analyticAt` applied to
the chosen holomorphic representative `holoRep hg`, since `holoFn hg = fun x => limUnder (𝓝[≠] x)
(Gext (holoRep hg))` definitionally. -/
theorem holoFn_analyticAt_ownChart {g : MGerm V} (hg : g ∈ OmegaDGerm (0 : Divisor X) V) :
    ∀ x ∈ (V : Set X),
      AnalyticAt ℂ (holoFn hg ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) :=
  fun x hx => gextLimRep_chart_analyticAt (holoRep_mem hg) hx

/-- **The per-overlap atom.** A germ-class holomorphic section `g ∈ OmegaDGerm 0 V`, read through the
cover-chart `y` and restricted to a relatively-compact open `U' ⋐ (chartAt y) '' V`, is a `BddHol U'`
element — the value of the forward cochain map at one overlap. The value is `holoFn hg ∘
(chartAt y).symm`. -/
noncomputable def germSectionToBddHol {g : MGerm V} (hg : g ∈ OmegaDGerm (0 : Divisor X) V) :
    BddHol U' :=
  holoSectionToBddHol hV (holoFn_analyticAt_ownChart (g := g) hg) hsub hcpt

@[simp] theorem germSectionToBddHol_toFun_of_mem {g : MGerm V}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) V) {z : ℂ} (hz : z ∈ U') :
    (germSectionToBddHol hV hsub hcpt hg).toFun z = holoFn hg ((chartAt (H := ℂ) y).symm z) :=
  holoSectionToBddHol_toFun_of_mem hV (holoFn_analyticAt_ownChart (g := g) hg) hsub hcpt hz

/-! #### Linearity of the atom

`germSectionToBddHol` factors through `holoFn`, which is additive/homogeneous and germ-invariant; so
on the section module `OmegaDGerm 0 V` the atom is `ℂ`-linear. We prove the value-level identities, then
package the map as a `ℂ`-linear map on the submodule. -/

theorem holoFn_add_at {W : Opens X} {g₁ g₂ : MGerm W}
    (hg₁ : g₁ ∈ OmegaDGerm (0 : Divisor X) W) (hg₂ : g₂ ∈ OmegaDGerm (0 : Divisor X) W)
    (hg : g₁ + g₂ ∈ OmegaDGerm (0 : Divisor X) W) {x : X} (hx : x ∈ W) :
    holoFn hg x = holoFn hg₁ x + holoFn hg₂ x := by
  have hsub := holoFn_sub (W := W) (g₁ := g₁ + g₂) (g₂ := g₂)
    (hg₁ := Submodule.add_mem _ hg₁ hg₂) (hg₂ := hg₂)
    (hg := by simpa using hg₁) (x := x) hx
  have h := congrArg (fun t => t + holoFn hg₂ x) hsub
  ring_nf at h ⊢
  exact h.symm

theorem holoFn_smul_at {W : Opens X} (c : ℂ) {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) (hcg : c • g ∈ OmegaDGerm (0 : Divisor X) W)
    {x : X} (hx : x ∈ W) : holoFn hcg x = c • holoFn hg x := by
  haveI := nhdsNE_neBot x
  obtain ⟨c₀, hc₀⟩ := holoFn_tendsto hg hx
  have hgerm : toGerm W (c • holoRep hg) = toGerm W (holoRep hcg) := by
    rw [map_smul, toGerm_holoRep hg, toGerm_holoRep hcg]
  have heq : Gext (holoRep hcg) =ᶠ[𝓝[≠] x] c • Gext (holoRep hg) := by
    have hmatch : rawRestrictG (inf_le_right : W ⊓ W ≤ W) (toGerm W (c • holoRep hg))
        = rawRestrictG (inf_le_left : W ⊓ W ≤ W) (toGerm W (holoRep hcg)) := by rw [hgerm]
    have h := Gext_overlap_eventuallyEq (holoRep hcg) (c • holoRep hg) hmatch hx hx
    rwa [Gext_smul] at h
  show limUnder (𝓝[≠] x) (Gext (holoRep hcg)) = c • holoFn hg x
  rw [show holoFn hg x = c₀ from hc₀.limUnder_eq]
  exact ((hc₀.const_smul c).congr' heq.symm).limUnder_eq

/-- The atom is additive (`holoFn` is additive on `U'`, where `(chartAt y).symm z ∈ V`). -/
theorem germSectionToBddHol_add {g₁ g₂ : MGerm V}
    (hg₁ : g₁ ∈ OmegaDGerm (0 : Divisor X) V) (hg₂ : g₂ ∈ OmegaDGerm (0 : Divisor X) V) :
    germSectionToBddHol hV hsub hcpt (Submodule.add_mem _ hg₁ hg₂)
      = germSectionToBddHol hV hsub hcpt hg₁ + germSectionToBddHol hV hsub hcpt hg₂ := by
  refine BddHol.toFun_injective (funext fun z => ?_)
  by_cases hz : z ∈ U'
  · have hzV : (chartAt (H := ℂ) y).symm z ∈ (V : Set X) := by
      have hmem : z ∈ (chartAt (H := ℂ) y) '' (V : Set X) := hsub (subset_closure hz)
      obtain ⟨w, hwV, hwz⟩ := hmem
      have hsrc : w ∈ (chartAt (H := ℂ) y).source := hV hwV
      rwa [← hwz, (chartAt (H := ℂ) y).left_inv hsrc]
    rw [BddHol.toFun_add, Pi.add_apply,
      germSectionToBddHol_toFun_of_mem hV hsub hcpt _ hz,
      germSectionToBddHol_toFun_of_mem hV hsub hcpt hg₁ hz,
      germSectionToBddHol_toFun_of_mem hV hsub hcpt hg₂ hz]
    exact holoFn_add_at hg₁ hg₂ (Submodule.add_mem _ hg₁ hg₂) hzV
  · rw [BddHol.toFun_add, Pi.add_apply,
      (germSectionToBddHol hV hsub hcpt (Submodule.add_mem _ hg₁ hg₂)).zero_off z hz,
      (germSectionToBddHol hV hsub hcpt hg₁).zero_off z hz,
      (germSectionToBddHol hV hsub hcpt hg₂).zero_off z hz, add_zero]

/-- The atom is homogeneous (`holoFn` is homogeneous on `U'`). -/
theorem germSectionToBddHol_smul (c : ℂ) {g : MGerm V}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) V) :
    germSectionToBddHol hV hsub hcpt (Submodule.smul_mem _ c hg)
      = c • germSectionToBddHol hV hsub hcpt hg := by
  refine BddHol.toFun_injective (funext fun z => ?_)
  by_cases hz : z ∈ U'
  · have hzV : (chartAt (H := ℂ) y).symm z ∈ (V : Set X) := by
      obtain ⟨w, hwV, hwz⟩ := hsub (subset_closure hz)
      have hsrc : w ∈ (chartAt (H := ℂ) y).source := hV hwV
      rwa [← hwz, (chartAt (H := ℂ) y).left_inv hsrc]
    rw [BddHol.toFun_smul, Pi.smul_apply,
      germSectionToBddHol_toFun_of_mem hV hsub hcpt _ hz,
      germSectionToBddHol_toFun_of_mem hV hsub hcpt hg hz]
    exact holoFn_smul_at c hg (Submodule.smul_mem _ c hg) hzV
  · rw [BddHol.toFun_smul, Pi.smul_apply,
      (germSectionToBddHol hV hsub hcpt (Submodule.smul_mem _ c hg)).zero_off z hz,
      (germSectionToBddHol hV hsub hcpt hg).zero_off z hz, smul_zero]

/-- **The per-overlap atom as a `ℂ`-linear map** `OmegaDGerm 0 V →ₗ[ℂ] BddHol U'`. Well-defined on
germ classes (`holoFn` is germ-invariant) and `ℂ`-linear (`germSectionToBddHol_add/smul`). This is the
forward cochain map restricted to a single overlap. -/
noncomputable def germSectionToBddHolCLM :
    (OmegaDGerm (0 : Divisor X) V) →ₗ[ℂ] BddHol U' where
  toFun g := germSectionToBddHol hV hsub hcpt g.2
  map_add' g₁ g₂ := germSectionToBddHol_add hV hsub hcpt g₁.2 g₂.2
  map_smul' c g := germSectionToBddHol_smul hV hsub hcpt c g.2

@[simp] theorem germSectionToBddHolCLM_apply {g : MGerm V}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) V) :
    germSectionToBddHolCLM hV hsub hcpt ⟨g, hg⟩ = germSectionToBddHol hV hsub hcpt hg :=
  rfl

/-- **The inverse exact-image atom as a `ℂ`-linear map.** On exact chart-image domains, `BddHol`
pulls back to an `OmegaDGerm 0` section. This is the local inverse bridge complementing the forward
overlap atom. -/
noncomputable def bddHolToOmegaDGermCLM_zero_image :
    BddHol ((chartAt (H := ℂ) y) '' (V : Set X)) →ₗ[ℂ] OmegaDGerm (0 : Divisor X) V :=
  bddHolToOmegaDGerm_zero_image (y := y) hV

end Atom

/-! ### Assembling the full cochain map into `DiskOverlapData.Ccov`

The forward cochain map sends a tuple of germ-class holomorphic sections — one per overlap `q : d.J`,
living on a holomorphy domain `V q` read through a cover-chart `chartCenter q`, with `d.Uov q` as the
relatively-compact piece — to the `BddHol`-cochain `d.Ccov = ∀ q, BddHol (d.Uov q)`. The per-overlap
data is packaged in `OverlapChartDatum`; the assembled map is the `Pi` of the per-overlap atoms.

This is the model-agnostic half of the comparison's forward direction: the geometric overlap model
(`chartCoverOverlapData` + the index identification `d.J ↔ 𝔘.ι × 𝔘.ι` + the nesting witnesses
`closure (Uov q) ⊆ chartCenter-image of V q`) is supplied separately (the manifold-geometry bridge);
once it produces an `OverlapChartDatum`, `cochainToCcov` is the `ℂ`-linear forward map. -/

/-- **Per-overlap chart data for a `DiskOverlapData`.** For each overlap `q : d.J`: a cover-chart
center `chartCenter q`, the holomorphy domain `V q` (an open `⊆ (chartAt (chartCenter q)).source`), and
the witness that `d.Uov q` is relatively compact inside the chart-image `(chartAt (chartCenter q)) ''
(V q)`. This is exactly the geometry `germSectionToBddHolCLM` consumes per overlap; supplying it for
the chart-disk model is the manifold-geometry bridge's job. -/
structure OverlapChartDatum (d : DiskOverlapData) where
  /-- The cover-chart center used to read overlap `q`. -/
  chartCenter : d.J → X
  /-- The holomorphy domain of the section over overlap `q`. -/
  V : d.J → Opens X
  /-- `V q` lies in the chart source of its center. -/
  hV : ∀ q, ((V q : Opens X) : Set X) ⊆ (chartAt (H := ℂ) (chartCenter q)).source
  /-- `d.Uov q` is relatively compact inside the chart-image of `V q`. -/
  hsub : ∀ q, closure (d.Uov q) ⊆ (chartAt (H := ℂ) (chartCenter q)) '' ((V q : Opens X) : Set X)
  /-- The relatively-compact closure is compact (automatic when `Uov q` is bounded; carried as data so
  the bridge can discharge it geometrically). -/
  hcpt : ∀ q, IsCompact (closure (d.Uov q))

namespace OverlapChartDatum

variable {d : DiskOverlapData} (𝒟 : OverlapChartDatum (X := X) d)

/-- The per-overlap section spaces tied to this datum: a germ-class holomorphic section on each
holomorphy domain `V q`. The forward cochain map's domain (the geometry bridge identifies this with
the germ-class cocycles `↥(𝔘.cocycles1 0)` via the index `d.J ↔ 𝔘.ι × 𝔘.ι`). -/
abbrev SectionTuple : Type _ := ∀ q : d.J, ↥(OmegaDGerm (X := X) (0 : Divisor X) (𝒟.V q))

/-- **The forward cochain map** `SectionTuple → Ccov`, `ℂ`-linear. Componentwise the per-overlap atom
`germSectionToBddHolCLM`: overlap `q`'s section becomes a `BddHol (d.Uov q)` via its analytic
representative restricted to the relatively-compact `d.Uov q`. Well-defined on germ classes and
`ℂ`-linear because each component is (`germSectionToBddHolCLM`). -/
noncomputable def cochainToCcov : 𝒟.SectionTuple →ₗ[ℂ] d.Ccov :=
  LinearMap.pi fun q =>
    (germSectionToBddHolCLM (𝒟.hV q) (𝒟.hsub q) (𝒟.hcpt q)).comp (LinearMap.proj q)

@[simp] theorem cochainToCcov_apply (s : 𝒟.SectionTuple) (q : d.J) :
    𝒟.cochainToCcov s q = germSectionToBddHolCLM (𝒟.hV q) (𝒟.hsub q) (𝒟.hcpt q) (s q) := by
  simp only [cochainToCcov, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- The value of the forward cochain map at overlap `q`, on `d.Uov q`, reads off the analytic
representative of the `q`-section pulled back through the cover-chart: `(cochainToCcov s q).toFun z =
holoFn (s q).2 ((chartAt (chartCenter q)).symm z)` for `z ∈ d.Uov q`. -/
theorem cochainToCcov_toFun_of_mem (s : 𝒟.SectionTuple) (q : d.J) {z : ℂ} (hz : z ∈ d.Uov q) :
    (𝒟.cochainToCcov s q).toFun z
      = holoFn (s q).2 ((chartAt (H := ℂ) (𝒟.chartCenter q)).symm z) := by
  rw [cochainToCcov_apply, germSectionToBddHolCLM_apply]
  exact germSectionToBddHol_toFun_of_mem (𝒟.hV q) (𝒟.hsub q) (𝒟.hcpt q) (s q).2 hz

end OverlapChartDatum

end Jacobians.Dolbeault
