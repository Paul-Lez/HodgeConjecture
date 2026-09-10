/-
  Čech finiteness — the geometric `DiskOverlapData` from the chart-disk / chart cover.

  Part of discharging `exists_cechModel` (Forster 14.9).
  `DiskOverlapData` (in `CechFinitenessWiring.lean`) packages, for each overlap index `p`, an OPEN
  `Uov p ⊆ ℂ` (the chart-image of the overlap, where the cover 1-cochains `BddHol (Uov p)` live) and a
  COMPACT `Kov p ⊆ Uov p` (the relatively-compact shrinking, where the Montel restriction lands). After
  the convexity-field removal (`Kov` is any compact `⊆ Uov`, the Montel atom
  `BddHol.isCompactOperator_restrictCLM_of_compact` handles non-convex `K`), this geometry is buildable
  from a genuine cover.

  This file builds it from `Montel`'s canonical chart cover, whose nested shrinking
  (`coverOpen ⊇ chartOpen`, closures, and the inner `innerShrunkChart ⊆ chartOpen`, all covering `X`
  over `chartCover`) supplies BOTH a relatively-compact and a *covering* compact shrinking:

  * `Uov (i,j) = (chartAt ℂ i) '' (chartOpen i ∩ chartOpen j)` — OPEN
    (`OpenPartialHomeomorph.isOpen_image_of_subset_source`, since the overlap is open `⊆ source i`).
  * `Kov (i,j) = (chartAt ℂ i) '' (innerShrunkChart i ∩ innerShrunkChart j)` — COMPACT
    (closed-in-compact ⟹ compact; continuous image of compact), and `⊆ Uov (i,j)` by monotonicity of
    the image (`innerShrunkChart ⊆ chartOpen`).

  Sorry-free; reuses only the axiom-clean `Montel/Cover.lean` nested-cover API and two Mathlib atoms
  (`isOpen_image_of_subset_source`, `IsCompact.image_of_continuousOn`). The reusable analytic-geometry
  atoms (`isOpen_chartImage_of_subset_source`, `isCompact_chartImage_of_subset_source`) are stated
  standalone so the final `exists_cechModel` assembly (cochain map + δ-complex + `leray` + comparison)
  can consume them.
-/
-- Only the model TYPES (`DiskOverlapData`) are needed here, so we import `CechModelBase` (not
-- `CechFinitenessWiring`); this keeps the `CechFinitenessWiring → CechFinitenessDtwist → … →
-- CechModelGeometry` chain acyclic.
import KirovDolbeault.Dolbeault.CechModelBase
import KirovDolbeault.Montel.Cover

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Reusable analytic-geometry atoms (chart-image of an overlap). -/

/-- **Chart-image-open atom.** The image of an OPEN set `s ⊆ (chartAt ℂ y).source` under the chart
`chartAt ℂ y` is open in `ℂ`. (`chartAt ℂ y` is an `OpenPartialHomeomorph`, so this is
`OpenPartialHomeomorph.isOpen_image_of_subset_source`.) This is exactly how an overlap chart-image
`Uov` is shown open. -/
theorem isOpen_chartImage_of_subset_source {y : X} {s : Set X} (hs : IsOpen s)
    (hsub : s ⊆ (chartAt (H := ℂ) y).source) :
    IsOpen ((chartAt (H := ℂ) y) '' s) :=
  (chartAt (H := ℂ) y).isOpen_image_of_subset_source hs hsub

/-- **Compact-image atom.** The image of a COMPACT set `K ⊆ (chartAt ℂ y).source` under the chart
`chartAt ℂ y` is compact in `ℂ` (the chart is continuous on its source). This is how an overlap
chart-image shrinking `Kov` is shown compact. -/
theorem isCompact_chartImage_of_subset_source {y : X} {K : Set X} (hK : IsCompact K)
    (hsub : K ⊆ (chartAt (H := ℂ) y).source) :
    IsCompact ((chartAt (H := ℂ) y) '' K) :=
  hK.image_of_continuousOn ((chartAt (H := ℂ) y).continuousOn.mono hsub)

/-! ### The geometric `DiskOverlapData` from `Montel`'s canonical chart cover. -/

open Jacobians.Montel

/-- For `x ∈ chartCover`, the outer open shrinkage `chartOpen x` lies in the chart source
(`chartOpen x ⊆ shrunkChart x ⊆ (chartAt ℂ x).source`). The basic containment behind both the
`Uov`/`Kov` source-membership obligations. -/
theorem chartOpen_subset_chartAt_source (x : X) (hx : x ∈ (chartCover : Finset X)) :
    chartOpen (X := X) x ⊆ (chartAt (H := ℂ) x).source :=
  (chartOpen_subset_shrunkChart x).trans (shrunkChart_subset_source x hx)

/-- The `n`-th cover center, where `n = #chartCover`: enumerate `chartCover` by `Fin #chartCover`
(`Finset.equivFin`). Used to give the overlap index `J = Fin #chartCover ²` a `Type 0` carrier (the
`{x // x ∈ chartCover}` subtype lives in `X`'s universe, which `DiskOverlapData.J : Type` forbids). -/
noncomputable def coverCenter (a : Fin ((chartCover : Finset X).card)) : X :=
  ((chartCover : Finset X).equivFin.symm a : X)

theorem coverCenter_mem (a : Fin ((chartCover : Finset X).card)) :
    coverCenter a ∈ (chartCover : Finset X) :=
  ((chartCover : Finset X).equivFin.symm a).2

/-- **The chart-cover overlap geometry.** From `Montel`'s canonical chart cover of the compact
Riemann surface `X`, the `DiskOverlapData` whose overlaps are read in the FIRST chart of each ordered
pair (`coverCenter` enumerates the cover charts by `Fin #chartCover`, keeping the index in `Type 0`):
* index `J` = ordered pairs of cover charts `Fin #chartCover ²`;
* `Uov (a,b)` = chart-`a` image of the OPEN outer overlap `chartOpen a ∩ chartOpen b` (open in `ℂ`);
* `Kov (a,b)` = chart-`a` image of the COMPACT inner overlap `innerShrunkChart a ∩ innerShrunkChart b`
  (compact in `ℂ`, `⊆ Uov` by image-monotonicity).
The inner shrinkings cover `X` over `chartCover` (`Montel.iUnion_innerShrunkChart_chartCover_eq`,
transported through the `Fin`-enumeration), so this is a genuine *covering* relatively-compact
shrinking — the Leray-model geometry, not a placeholder. -/
noncomputable def chartCoverOverlapData : DiskOverlapData where
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

/-- **The inner shrinking covers `X`.** The `Kov`-overlaps come from `innerShrunkChart` pieces that
cover `X` over the cover indices: `⋃ a, innerShrunkChart (coverCenter a) = Set.univ`. This is the
covering property that promotes the geometry from "some compact `⊆` some open" to a genuine
*relatively-compact covering shrinking* (the Leray-model geometry). Transports
`Montel.iUnion_innerShrunkChart_chartCover_eq` through the `Fin`-enumeration `coverCenter`. -/
theorem iUnion_innerShrunkChart_coverCenter_eq :
    (⋃ a : Fin ((chartCover : Finset X).card), innerShrunkChart (X := X) (coverCenter a)) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerShrunkChart_chartCover_eq (X := X)]
  intro y hy
  simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  obtain ⟨x, hxmem, hxy⟩ := hy
  refine ⟨(chartCover : Finset X).equivFin ⟨x, hxmem⟩, ?_⟩
  rwa [coverCenter, Equiv.symm_apply_apply]

end Jacobians.Dolbeault
