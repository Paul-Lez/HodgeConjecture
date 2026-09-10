/-
  Čech finiteness — the sup-norm Čech δ-complex for the chart-cover Montel model (piece (a) of
  `exists_cechModel`).

  GOAL (`exists_cechModel`, Forster 14.9): for the chart-cover `DiskOverlapData`
  (`chartCoverOverlapData`), build a `Coboundaries` — the sup-norm Čech complex on bounded-holomorphic
  cochains — whose `supH1` is `ℂ`-linearly iso to the germ-class `cechH1`.  The `Coboundaries` fields
  split into three pieces:

    (a) **the δ-complex** (`δ0 : C0 →L Cshr`, `δ1 : Cshr →L C2`, `δ1cov : Ccov →L C2cov`, `hδδ`,
        `hcomm`) — THIS FILE.  The 1-cochain spaces `Ccov`/`Cshr` are already in `DiskOverlapData`; here
        we add the 0- and 2-cochain spaces and the Čech differentials.
    (b) the `leray` field — disk-acyclicity (`DbarDiskCohomology.dbar_solvable_ball`) assembled
        per-overlap + partition of unity (separate file).
    (c) the comparison `cechH1 ≃ₗ supH1` — the germ↔`BddHol` cochain iso (separate file).

  ⚠ THE CROSS-CHART SUBTLETY of (a).  A 0-cochain assigns each cover set `a` a bounded-holomorphic
  function on its OWN chart-image `(chartAt (coverCenter a)) '' (chartOpen a)` (chart-`a` coordinates).
  The Čech `δ⁰` on the overlap `(a,b)` is `(δ⁰f)_{ab} = f_b − f_a` read in a COMMON chart — here chart
  `a` (since `Uov (a,b)` is read in chart `a`).  So `f_a` restricts directly, but `f_b` must be
  transported from chart-`b` to chart-`a` coordinates through the holomorphic transition
  `φ_a ∘ φ_b⁻¹` (which is `AnalyticOn` on the overlap, the `ω`-manifold's chart change).  Building this
  transition transport on `BddHol`, with boundedness + continuity of the resulting `δ⁰`, is the genuine
  content of (a) and the next work.  The `CechH0`/`HoloRep` chart-change atoms
  (`analyticAt_chart_change`, `transition_analyticAt_of_mem`) are the inputs.

  This file is comparison-FREE (built on `CechModelGeometry` + `HoloRep`, NOT the ~900s
  Dolbeault-comparison chain), so it builds cheaply.  Sorry-free: the cochain SPACES + their Banach
  instances (below).  The cross-chart δ maps are stated as the next pieces (prose, not gap tactics).
-/
import KirovDolbeault.Dolbeault.CechModelGeometry

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Jacobians.Montel
open BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### 0-simplex and 2-simplex chart-image geometry (extending the pairwise `DiskOverlapData`) -/

/-- The chart-image of cover set `a` — the open set in `ℂ` (in chart-`a` coordinates) where the
0-cochain component over `a` is bounded-holomorphic. -/
noncomputable def coverSetImage (a : Fin ((chartCover : Finset X).card)) : Set ℂ :=
  (chartAt (H := ℂ) (coverCenter a)) '' (chartOpen (X := X) (coverCenter a))

theorem isOpen_coverSetImage (a : Fin ((chartCover : Finset X).card)) :
    IsOpen (coverSetImage (X := X) a) :=
  isOpen_chartImage_of_subset_source (chartOpen_isOpen (coverCenter a))
    (chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a))

/-! ### The sup-norm 0-cochains `C⁰` (the `Coboundaries.C0` for the chart cover)

A 0-cochain is a bounded-holomorphic function on each cover set's chart-image.  `δ⁰` (cross-chart,
next) maps it to the shrinking 1-cochains `Cshr`. -/

/-- **Sup-norm 0-cochains.** Bounded-holomorphic on each cover set's chart-image — the genuine Čech
`C⁰` for the chart cover, in the `BddHol` representation. -/
abbrev Cochain0Model : Type :=
  ∀ a : Fin ((chartCover : Finset X).card), BddHol (coverSetImage (X := X) a)

noncomputable instance : NormedAddCommGroup (Cochain0Model (X := X)) := inferInstance
noncomputable instance : NormedSpace ℂ (Cochain0Model (X := X)) := inferInstance

/-- `C⁰` is a Banach space (finite product of the Banach `BddHol`). -/
noncomputable instance : CompleteSpace (Cochain0Model (X := X)) := by
  haveI : ∀ a, CompleteSpace (BddHol (coverSetImage (X := X) a)) := fun a =>
    BddHol.completeSpace (isOpen_coverSetImage a)
  infer_instance

/-! ### 2-simplex chart-images and the sup-norm 2-cochains `C²`

The Čech `δ¹` lands in the 2-cochains over triple overlaps `(a,b,c)`, read (like the pairwise data) in
the FIRST chart `a`.  Cover side `C²cov` is bounded-holomorphic on the OPEN triple chart-image; the
shrinking side `C²` is bounded-continuous on the COMPACT inner triple chart-image (where the Montel
restriction lands), matching `DiskOverlapData.Cshr`'s `→ᵇ` style. -/

/-- Open chart-`a` image of the triple outer overlap `chartOpen a ∩ chartOpen b ∩ chartOpen c`. -/
noncomputable def coverTripleImage (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) : Set ℂ :=
  (chartAt (H := ℂ) (coverCenter t.1)) ''
    (chartOpen (X := X) (coverCenter t.1) ∩ chartOpen (X := X) (coverCenter t.2.1)
      ∩ chartOpen (X := X) (coverCenter t.2.2))

theorem isOpen_coverTripleImage (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    IsOpen (coverTripleImage (X := X) t) :=
  isOpen_chartImage_of_subset_source
    (((chartOpen_isOpen (coverCenter t.1)).inter (chartOpen_isOpen (coverCenter t.2.1))).inter
      (chartOpen_isOpen (coverCenter t.2.2)))
    ((Set.inter_subset_left.trans Set.inter_subset_left).trans
      (chartOpen_subset_chartAt_source (coverCenter t.1) (coverCenter_mem t.1)))

/-- Compact chart-`a` image of the triple inner overlap
`innerShrunkChart a ∩ innerShrunkChart b ∩ innerShrunkChart c` (the shrinking, `⊆ coverTripleImage`). -/
noncomputable def coverTripleShrink (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) : Set ℂ :=
  (chartAt (H := ℂ) (coverCenter t.1)) ''
    (innerShrunkChart (X := X) (coverCenter t.1) ∩ innerShrunkChart (X := X) (coverCenter t.2.1)
      ∩ innerShrunkChart (X := X) (coverCenter t.2.2))

theorem isCompact_coverTripleShrink (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    IsCompact (coverTripleShrink (X := X) t) :=
  isCompact_chartImage_of_subset_source
    ((((innerShrunkChart_isClosed (coverCenter t.1)).inter
      (innerShrunkChart_isClosed (coverCenter t.2.1))).inter
      (innerShrunkChart_isClosed (coverCenter t.2.2))).isCompact)
    (((Set.inter_subset_left.trans Set.inter_subset_left).trans
      (innerShrunkChart_subset_chartOpen (coverCenter t.1))).trans
      (chartOpen_subset_chartAt_source (coverCenter t.1) (coverCenter_mem t.1)))

noncomputable instance (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    CompactSpace (coverTripleShrink (X := X) t) :=
  isCompact_iff_compactSpace.mp (isCompact_coverTripleShrink t)

/-- **Sup-norm 2-cochains, cover side** `C²cov` — bounded-holomorphic on each open triple chart-image
(target of the cover-side `δ¹`). -/
abbrev Cochain2CovModel : Type :=
  ∀ t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card),
    BddHol (coverTripleImage (X := X) t)

/-- **Sup-norm 2-cochains, shrinking side** `C²` — bounded-continuous on each compact inner triple
chart-image (target of the shrinking-side `δ¹`). -/
abbrev Cochain2Model : Type :=
  ∀ t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card),
    (coverTripleShrink (X := X) t →ᵇ ℂ)

noncomputable instance : NormedAddCommGroup (Cochain2CovModel (X := X)) := inferInstance
noncomputable instance : NormedSpace ℂ (Cochain2CovModel (X := X)) := inferInstance
noncomputable instance : NormedAddCommGroup (Cochain2Model (X := X)) := inferInstance
noncomputable instance : NormedSpace ℂ (Cochain2Model (X := X)) := inferInstance

/-- `C²cov` is Banach (finite product of the Banach `BddHol`). -/
noncomputable instance : CompleteSpace (Cochain2CovModel (X := X)) := by
  haveI : ∀ t, CompleteSpace (BddHol (coverTripleImage (X := X) t)) := fun t =>
    BddHol.completeSpace (isOpen_coverTripleImage t)
  infer_instance

/-- `C²` is Banach (finite product of `→ᵇ`). -/
noncomputable instance : CompleteSpace (Cochain2Model (X := X)) := inferInstance

end Jacobians.Dolbeault
