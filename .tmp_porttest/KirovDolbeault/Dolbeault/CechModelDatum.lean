/-
  Čech finiteness — the `OverlapChartDatum` for the (4-level) nested chart-cover overlap model.

  Part of discharging `exists_cechModel` (Forster 14.9).
  `CechModelCochain.lean` builds the forward cochain map `OverlapChartDatum.cochainToCcov :
  SectionTuple →ₗ[ℂ] d.Ccov` (germ-class sections ↦ `BddHol` cochains) for ANY `DiskOverlapData d`
  equipped with an `OverlapChartDatum` (per-overlap cover-chart center `chartCenter q`, holomorphy
  domain `V q`, and the nesting witness `closure (d.Uov q) ⊆ chartAt (chartCenter q) '' (V q)`). This
  file supplies that `OverlapChartDatum` for the chart-cover geometry, finishing the forward
  `germ → BddHol` map of the comparison `cechH1 ≃ supH1`.

  THE NESTING PROBLEM (diagnosis).  In `chartCoverOverlapData`, `Uov (a,b) = chartAt y '' (chartOpen a
  ∩ chartOpen b)` is an OPEN set that equals its OWN holomorphy region.  An `OverlapChartDatum` for it
  would need `closure (Uov) ⊆ chartAt y '' V` for some open `V` — forcing `Uov` to be relatively
  compact inside a chart-image, i.e. forcing `closure (chartOpen-overlap) ⊆ V` with `V` open `⊆`
  source.  That cannot hold with `V` the *same* `chartOpen`-overlap.  The fix is a genuinely NESTED
  model: separate the open cover-domain `Uov` (where `BddHol` lives) from a strictly larger open
  holomorphy domain `V` (where the analytic representative is holomorphic), using a level of
  Montel's nested cover in between.

  THE 4-LEVEL MODEL (`nestedChartCoverOverlapData`).  Montel's cover gives, per cover-center `x`, the
  strictly nested chain `innerShrunkChart x ⊆ chartOpen x ⊆ shrunkChart x = closure (chartOpen x) ⊆
  (chartAt x).source` with `innerShrunkChart` (a COMPACT covering family) and `shrunkChart` closed.
  Reading every overlap `(a,b)` in chart `y = coverCenter a`, set:

  * `V (a,b)   = (chartAt y).source ∩ (chartAt (coverCenter b)).source` — the HOLOMORPHY domain (open,
    `⊆ source y`; the analytic representative of an overlap section is holomorphic across both charts'
    sources).
  * `Uov (a,b) = chartAt y '' (chartOpen a ∩ chartOpen b)` — the OPEN cover-domain.  Its closure lands
    inside `chartAt y '' V` because `closure (chartOpen a ∩ chartOpen b) ⊆ shrunkChart a ∩ shrunkChart
    b ⊆ source a ∩ source b = V` (`shrunkChart_subset_source`), so the chart-image of `Uov`'s closure
    is contained in the (compact, hence closed) chart-image of the `shrunkChart`-overlap.
  * `Kov (a,b) = chartAt y '' (innerShrunkChart a ∩ innerShrunkChart b)` — the COMPACT covering
    shrinking, `⊆ Uov` (`innerShrunkChart ⊆ chartOpen`); the `innerShrunkChart` family covers `X`
    (`iUnion_innerShrunkChart_coverCenter_eq`), so this is a genuine Leray-model shrinking, not a
    placeholder.

  The crux nesting witness is `hsub`: `closure (chartAt y '' (chartOpen-overlap)) ⊆ chartAt y ''
  (source-overlap)`, handled by the compact-image / closed-superset argument above
  (`closure_minimal` into the compact `chartAt y '' (shrunkChart-overlap)`).

  Sorry-free; reuses only the axiom-clean Montel nested-cover API (`Jacobians/Montel/Cover.lean`),
  the chart-image atoms (`isOpen/isCompact_chartImage_of_subset_source`, `CechModelGeometry`), and
  standard Mathlib topology (`closure_minimal`, `IsCompact.of_isClosed_subset`,
  `closure_inter_subset_inter_closure`).  Result: `(overlapChartDatum).cochainToCcov` is the finished
  forward `germ → BddHol` cochain map for the model.
-/
import KirovDolbeault.Dolbeault.CechModelCochain

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Jacobians.Montel

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The (4-level) nested chart-cover overlap data

`chartCoverOverlapData` reads overlaps in the FIRST chart of each ordered pair and takes `Uov` to be
the chart-image of the `chartOpen`-overlap, with `Kov` the chart-image of the (covering) compact
`innerShrunkChart`-overlap.  That model's `Uov` *equals* its own holomorphy region, so it admits no
`OverlapChartDatum`.  `nestedChartCoverOverlapData` keeps the SAME `Uov` and `Kov`, but its
`OverlapChartDatum` reads the holomorphy domain at the strictly larger `source a ∩ source b`, with
`closure (chartOpen-overlap) ⊆ shrunkChart-overlap ⊆ source-overlap` supplying the room. -/

/-- Per-overlap holomorphy domain for the nested model: the intersection of the two cover-charts'
sources, read as an `Opens X`.  Open (intersection of open chart sources), and `⊆ (chartAt
(coverCenter a)).source` so it is a valid `OverlapChartDatum.V`. The analytic representative of an
overlap section is holomorphic on this whole intersection. -/
noncomputable def overlapSourceInter
    (p : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) : Opens X :=
  ⟨(chartAt (H := ℂ) (coverCenter p.1)).source ∩ (chartAt (H := ℂ) (coverCenter p.2)).source,
    (chartAt (H := ℂ) (coverCenter p.1)).open_source.inter
      (chartAt (H := ℂ) (coverCenter p.2)).open_source⟩

@[simp] theorem overlapSourceInter_coe
    (p : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    ((overlapSourceInter (X := X) p : Opens X) : Set X)
      = (chartAt (H := ℂ) (coverCenter p.1)).source ∩ (chartAt (H := ℂ) (coverCenter p.2)).source :=
  rfl

/-- The `shrunkChart`-overlap (`closure (chartOpen a) ∩ closure (chartOpen b)` since `shrunkChart =
closure ∘ chartOpen`) lies in the source-overlap: each `shrunkChart` is `⊆` its own chart source
(`shrunkChart_subset_source`). The geometric inclusion behind the `hsub` nesting witness. -/
theorem shrunkChart_inter_subset_source_inter
    (p : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    shrunkChart (X := X) (coverCenter p.1) ∩ shrunkChart (X := X) (coverCenter p.2)
      ⊆ (chartAt (H := ℂ) (coverCenter p.1)).source ∩ (chartAt (H := ℂ) (coverCenter p.2)).source :=
  Set.inter_subset_inter
    (shrunkChart_subset_source (coverCenter p.1) (coverCenter_mem p.1))
    (shrunkChart_subset_source (coverCenter p.2) (coverCenter_mem p.2))

/-- The `shrunkChart`-overlap is compact (closed in compact `X`) and `⊆ source a`, so its chart-`a`
image is COMPACT in `ℂ` — the closed superset that pins down `closure (Uov)` in the `hsub`/`hcpt`
proofs. -/
theorem isCompact_chartImage_shrunkChart_inter
    (p : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    IsCompact ((chartAt (H := ℂ) (coverCenter p.1)) ''
      (shrunkChart (X := X) (coverCenter p.1) ∩ shrunkChart (X := X) (coverCenter p.2))) :=
  isCompact_chartImage_of_subset_source
    (((shrunkChart_isClosed (coverCenter p.1)).inter (shrunkChart_isClosed (coverCenter p.2))).isCompact)
    ((shrunkChart_inter_subset_source_inter p).trans Set.inter_subset_left)

/-- The chart-image of the `chartOpen`-overlap (`= Uov`) is contained in the chart-image of the
`shrunkChart`-overlap (`chartOpen ⊆ shrunkChart` and the chart is monotone). -/
theorem chartImage_chartOpen_subset_chartImage_shrunkChart
    (p : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    (chartAt (H := ℂ) (coverCenter p.1)) ''
        (chartOpen (X := X) (coverCenter p.1) ∩ chartOpen (X := X) (coverCenter p.2))
      ⊆ (chartAt (H := ℂ) (coverCenter p.1)) ''
        (shrunkChart (X := X) (coverCenter p.1) ∩ shrunkChart (X := X) (coverCenter p.2)) :=
  Set.image_mono
    (Set.inter_subset_inter (chartOpen_subset_shrunkChart (coverCenter p.1))
      (chartOpen_subset_shrunkChart (coverCenter p.2)))

/-- **The nested chart-cover overlap data.** Identical `J`/`Uov`/`Kov` to `chartCoverOverlapData`
(open chart-image cover-domain from the `chartOpen`-overlap; covering compact shrinking from the
`innerShrunkChart`-overlap), restated here so that it carries the `OverlapChartDatum` below.  The
defining property that distinguishes it is geometric, not structural: its overlaps are *nested* — the
closure of each `Uov` sits strictly inside the chart-image of a larger holomorphy domain (the
source-overlap), the room for which is `closure (chartOpen-overlap) ⊆ shrunkChart-overlap ⊆
source-overlap`. -/
noncomputable def nestedChartCoverOverlapData : DiskOverlapData where
  J := Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)
  Uov p :=
    (chartAt (H := ℂ) (coverCenter p.1)) ''
      (chartOpen (X := X) (coverCenter p.1) ∩ chartOpen (X := X) (coverCenter p.2))
  hUov p :=
    isOpen_chartImage_of_subset_source
      ((chartOpen_isOpen (coverCenter p.1)).inter (chartOpen_isOpen (coverCenter p.2)))
      (Set.inter_subset_left.trans
        (chartOpen_subset_chartAt_source (coverCenter p.1) (coverCenter_mem p.1)))
  Kov p :=
    (chartAt (H := ℂ) (coverCenter p.1)) ''
      (innerShrunkChart (X := X) (coverCenter p.1) ∩ innerShrunkChart (X := X) (coverCenter p.2))
  hKcpt p :=
    isCompact_chartImage_of_subset_source
      (((innerShrunkChart_isClosed (coverCenter p.1)).inter
        (innerShrunkChart_isClosed (coverCenter p.2))).isCompact)
      ((Set.inter_subset_left.trans (innerShrunkChart_subset_chartOpen (coverCenter p.1))).trans
        (chartOpen_subset_chartAt_source (coverCenter p.1) (coverCenter_mem p.1)))
  hKU p :=
    Set.image_mono
      (Set.inter_subset_inter (innerShrunkChart_subset_chartOpen (coverCenter p.1))
        (innerShrunkChart_subset_chartOpen (coverCenter p.2)))

@[simp] theorem nestedChartCoverOverlapData_Uov
    (p : (nestedChartCoverOverlapData (X := X)).J) :
    (nestedChartCoverOverlapData (X := X)).Uov p
      = (chartAt (H := ℂ) (coverCenter p.1)) ''
        (chartOpen (X := X) (coverCenter p.1) ∩ chartOpen (X := X) (coverCenter p.2)) :=
  rfl

/-! ### The `OverlapChartDatum` for the nested model -/

/-- **The crux nesting witness.** The closure of the cover-domain `Uov (a,b) = chartAt y ''
(chartOpen-overlap)` is contained in the chart-image of the holomorphy domain `V (a,b) =
source-overlap`.  Proof: the chart-image of the `shrunkChart`-overlap is COMPACT (hence closed in
`ℂ`) and contains `Uov` (since `chartOpen ⊆ shrunkChart`), so it contains `closure (Uov)`
(`closure_minimal`); and it is `⊆` the chart-image of the source-overlap by monotonicity of the
chart-image along `shrunkChart-overlap ⊆ source-overlap`. -/
theorem closure_nestedUov_subset_chartImage_source
    (p : (nestedChartCoverOverlapData (X := X)).J) :
    closure ((nestedChartCoverOverlapData (X := X)).Uov p)
      ⊆ (chartAt (H := ℂ) (coverCenter p.1)) ''
        ((overlapSourceInter (X := X) p : Opens X) : Set X) := by
  rw [nestedChartCoverOverlapData_Uov, overlapSourceInter_coe]
  refine (closure_minimal (chartImage_chartOpen_subset_chartImage_shrunkChart p)
    (isCompact_chartImage_shrunkChart_inter p).isClosed).trans ?_
  exact Set.image_mono (shrunkChart_inter_subset_source_inter p)

/-- **The nested model's relative compactness.** `closure (Uov (a,b))` is compact: it is closed
(`isClosed_closure`) and contained in the compact chart-image of the `shrunkChart`-overlap. -/
theorem isCompact_closure_nestedUov
    (p : (nestedChartCoverOverlapData (X := X)).J) :
    IsCompact (closure ((nestedChartCoverOverlapData (X := X)).Uov p)) := by
  refine (isCompact_chartImage_shrunkChart_inter p).of_isClosed_subset isClosed_closure ?_
  rw [nestedChartCoverOverlapData_Uov]
  exact closure_minimal (chartImage_chartOpen_subset_chartImage_shrunkChart p)
    (isCompact_chartImage_shrunkChart_inter p).isClosed

/-- **The `OverlapChartDatum` for the nested chart-cover model.** Per overlap `(a,b)`: the cover-chart
center is `coverCenter a`, the holomorphy domain `V` is the source-overlap (open, `⊆ source a`), and
the cover-domain `Uov` is relatively compact inside `chartAt a '' V` (the crux witness
`closure_nestedUov_subset_chartImage_source`).  Feeding this to `OverlapChartDatum.cochainToCcov`
yields the finished forward `germ → BddHol` cochain map for the model. -/
noncomputable def overlapChartDatum :
    OverlapChartDatum (X := X) (nestedChartCoverOverlapData (X := X)) where
  chartCenter p := coverCenter p.1
  V p := overlapSourceInter (X := X) p
  hV p := by
    rw [overlapSourceInter_coe]; exact Set.inter_subset_left
  hsub p := closure_nestedUov_subset_chartImage_source p
  hcpt p := isCompact_closure_nestedUov p

/-- **The finished forward cochain map** for the nested chart-cover model: `germ`-class section tuples
↦ `BddHol` cochains on the cover-domains, `ℂ`-linear.  This is `OverlapChartDatum.cochainToCcov`
specialised to `overlapChartDatum`; it is the forward half (`germ → BddHol`) of the comparison
`cechH1 𝔘 D ≃ supH1`, ready for the δ-square / Leray-refinement assembly in `exists_cechModel`. -/
noncomputable def nestedCochainToCcov :
    (overlapChartDatum (X := X)).SectionTuple →ₗ[ℂ] (nestedChartCoverOverlapData (X := X)).Ccov :=
  (overlapChartDatum (X := X)).cochainToCcov

end Jacobians.Dolbeault
