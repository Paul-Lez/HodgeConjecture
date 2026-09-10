/-
  Čech finiteness — the CROSS-CHART Čech δ-complex for the HOLOMORPHIC-shrinking model.

  Companion to `CechModelDifferential.lean` (the CONTINUOUS-shrinking branch).  That file builds the
  Čech `δ⁰`/`δ¹`/`δ¹cov` and the `δ²=0`/`hcomm` algebra for `chartCoverOverlapData`, whose shrinking
  side is bounded-continuous on compact overlaps `Kov`.  This file builds the SAME differentials for the
  corrected holomorphic-shrinking model `chartCoverHolomorphicDiskOverlapData`
  (`CechModelHolomorphic.lean`), whose shrinking side is bounded-HOLOMORPHIC on the open
  relatively-compact shrinkings `Wov p` (`Wov p ⋐ Uov p`).

  The geometry is identical (same cover centres `montel_coverCenter = coverCenter`, same outer overlaps
  `Uov`), so the cover-side `δ¹cov` is REUSED verbatim from `CechModelDifferential.delta1CovModel`
  (the holomorphic `Ccov` is definitionally the continuous `Ccov`).  The shrinking side changes shape:
  the transport/restriction now stay in `BddHol` on the OPEN `Wov`/`WovTriple` sets (analytic
  `BddHol.precompHolCLM` / open `BddHol.restrictOpenCLM`), not `→ᵇ` on compacts.  The geometric
  witnesses (`τ_{ab}` analytic on `Wov`, mapping it into the `b`-side overlap) come from the same
  manifold chart-change atom `transition_analyticAt_of_mem`, now over the `innerChartOpen`-based `Wov`.

  All complete, axiom-clean `[propext, Classical.choice, Quot.sound]`.  The `leray` field is handled
  separately downstream (see `HolomorphicCoboundaries.leray`); this file delivers the structural
  δ-complex data `δ⁰`, `δ¹`, `δ¹cov`, `δ²=0`, and `hcomm`.
-/
import KirovDolbeault.Dolbeault.CechModelHolomorphic
import KirovDolbeault.Dolbeault.CechModelDifferential

open scoped Manifold ContDiff Topology
open Jacobians.Montel ContinuousLinearMap

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### A point of `innerChartOpen` lies in the chart source

The single geometric containment behind all the `Wov`-based witnesses: `innerChartOpen ⊆ chartOpen ⊆
(chartAt centre).source`. -/

/-- The cover centres of the holomorphic model and the continuous model coincide definitionally
(`montel_coverCenter = coverCenter`).  We expose this `rfl` as a simp lemma so the `coverTransition`
(defined via `coverCenter`) unfolds cleanly against the `Wov`/`Uov` sets (defined via
`montel_coverCenter`). -/
theorem montel_coverCenter_eq_coverCenter (a : Fin ((chartCover : Finset X).card)) :
    montel_coverCenter (X := X) a = coverCenter (X := X) a := rfl

/-- A point of `innerChartOpen (montel_coverCenter a)` lies in the chart source. -/
theorem innerChartOpen_subset_chartAt_source_aux (a : Fin ((chartCover : Finset X).card)) :
    innerChartOpen (X := X) (montel_coverCenter (X := X) a) ⊆
      (chartAt (H := ℂ) (montel_coverCenter (X := X) a)).source :=
  (montel_innerChartOpen_subset_chartOpen (X := X) (montel_coverCenter (X := X) a)).trans
    (montel_chartOpen_subset_chartAt_source (X := X) (montel_coverCenter (X := X) a)
      (montel_coverCenter_mem (X := X) a))

/-! ### The off-diagonal transport and the diagonal restriction on the OPEN shrinking `Wov`

The shrinking-side `δ⁰` reads the overlap `(a,b)` in chart `a`.  The `a`-component restricts directly
to the smaller open `Wov (a,b) ⊆ Uov (a,b)` (`BddHol.restrictOpenCLM`); the `b`-component (chart-`b`
coordinates) is transported to chart-`a` through the holomorphic transition `τ_{ab}` (analytic on the
OPEN `Wov (a,b)`, mapping it into the `b`-side cover open `Uov (b,b)` = `coverSetImage`-style image),
via `BddHol.precompHolCLM`.  Both stay `BddHol` on the open `Wov`. -/

/-- The cover transition `τ_{ab}` is analytic on the OPEN shrinking `Wov (a,b)` (chart-`a` image of
`innerChartOpen a ∩ innerChartOpen b`): at each point it is analytic by `transition_analyticAt_of_mem`,
both centres' sources containing the inner overlap point. -/
theorem analyticOn_coverTransition_Wov (a b : Fin ((chartCover : Finset X).card)) :
    AnalyticOn ℂ (coverTransition (X := X) a b) ((chartCoverHolomorphicDiskOverlapData (X := X)).Wov (a, b)) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  apply AnalyticAt.analyticWithinAt
  exact transition_analyticAt_of_mem
    (innerChartOpen_subset_chartAt_source_aux a hxa)
    (innerChartOpen_subset_chartAt_source_aux b hxb)

/-- The cover transition `τ_{ab}` maps the OPEN shrinking `Wov (a,b)` (chart-`a` coordinates) into
`coverSetImage b` (chart-`b` image of `chartOpen b`), where the `b`-component of a 0-cochain is
bounded-holomorphic.  A point `φ_a x` with `x ∈ innerChartOpen a ∩ innerChartOpen b` maps to `φ_b x`
with `x ∈ innerChartOpen b ⊆ chartOpen b`, so `φ_b x ∈ φ_b '' (chartOpen b) = coverSetImage b`. -/
theorem mapsTo_coverTransition_Wov (a b : Fin ((chartCover : Finset X).card)) :
    Set.MapsTo (coverTransition (X := X) a b) ((chartCoverHolomorphicDiskOverlapData (X := X)).Wov (a, b))
      (coverSetImage (X := X) b) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter (X := X) a)).source :=
    innerChartOpen_subset_chartAt_source_aux a hxa
  refine ⟨x, montel_innerChartOpen_subset_chartOpen (X := X) (montel_coverCenter (X := X) b) hxb, ?_⟩
  simp only [montel_coverCenter_eq_coverCenter, coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (coverCenter (X := X) a)).left_inv hxa_src]

/-- The shrinking `Wov (a,b)` lies in `coverSetImage a` (chart-`a` image of `innerChartOpen a ∩
innerChartOpen b ⊆ chartOpen a`), so the `a`-component restricts directly. -/
theorem Wov_subset_coverSetImage_fst (a b : Fin ((chartCover : Finset X).card)) :
    (chartCoverHolomorphicDiskOverlapData (X := X)).Wov (a, b) ⊆ coverSetImage (X := X) a := by
  show (chartAt (H := ℂ) (montel_coverCenter (X := X) a)) ''
      (innerChartOpen (X := X) (montel_coverCenter (X := X) a) ∩
        innerChartOpen (X := X) (montel_coverCenter (X := X) b)) ⊆ coverSetImage (X := X) a
  unfold coverSetImage
  exact Set.image_mono
    (Set.inter_subset_left.trans
      (montel_innerChartOpen_subset_chartOpen (X := X) (montel_coverCenter (X := X) a)))

/-- **The cross-chart Čech `δ⁰`** of the holomorphic-shrinking model: `Cochain0Model →L[ℂ] d.Cshr`.
Componentwise on overlap `(a,b)`,
    `(δ⁰f)_{ab} = (transport of f b to chart-a) − (restriction of f a)`   on the OPEN `Wov (a,b)`,
the genuine Čech coboundary with the `b`-side transported through the holomorphic transition `τ_{ab}`.
Both pieces stay `BddHol` on the open `Wov`: the off-diagonal via `BddHol.precompHolCLM`, the diagonal
via `BddHol.restrictOpenCLM`.

The 0-cochain spaces `Cochain0Model = ∀ a, BddHol (coverSetImage a)` are branch-independent
(`CechModelDelta`); `coverSetImage a = (chartAt (coverCenter a)) '' (chartOpen a)` is definitionally
`Uov (a,a)`, the diagonal cover open, so the diagonal restriction reads `f a : BddHol (coverSetImage a)
= BddHol (Uov (a,a))` and the transport lands `f b` in `Uov (b,b) = coverSetImage b`. -/
noncomputable def delta0ModelHolo :
    Cochain0Model (X := X) →L[ℂ] (chartCoverHolomorphicDiskOverlapData (X := X)).Cshr :=
  ContinuousLinearMap.pi fun p =>
    (BddHol.precompHolCLM (analyticOn_coverTransition_Wov p.1 p.2)
        (mapsTo_coverTransition_Wov p.1 p.2)).comp (proj p.2)
      - (BddHol.restrictOpenCLM (Wov_subset_coverSetImage_fst p.1 p.2)).comp (proj p.1)

/-- The component identity for `δ⁰` at overlap `p = (a,b)`. -/
theorem delta0ModelHolo_apply (f : Cochain0Model (X := X)) (p : (chartCoverHolomorphicDiskOverlapData (X := X)).J) :
    delta0ModelHolo f p
      = BddHol.precompHolCLM (analyticOn_coverTransition_Wov p.1 p.2)
          (mapsTo_coverTransition_Wov p.1 p.2) (f p.2)
        - BddHol.restrictOpenCLM (Wov_subset_coverSetImage_fst p.1 p.2) (f p.1) := rfl

/-- **The Čech coboundary pointwise formula.**  On the OPEN shrinking `Wov (a,b)`, the `δ⁰` value at a
point `z` is `f b` evaluated at the transported point `τ_{ab} z` minus `f a` at `z` — the explicit
cross-chart Čech `δ⁰` formula `(δ⁰f)_{ab}(z) = f_b(τ_{ab} z) − f_a(z)`. -/
theorem delta0ModelHolo_apply_apply (f : Cochain0Model (X := X)) (p : (chartCoverHolomorphicDiskOverlapData (X := X)).J)
    {z : ℂ} (hz : z ∈ (chartCoverHolomorphicDiskOverlapData (X := X)).Wov p) :
    (delta0ModelHolo f p).toFun z
      = (f p.2).toFun (coverTransition p.1 p.2 z) - (f p.1).toFun z := by
  obtain ⟨a, b⟩ := p
  rw [delta0ModelHolo_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### The shrinking-side 2-cochains on OPEN triples `WovTriple`, and the `δ¹` -/

/-- Open chart-`a` image of the triple inner overlap `innerChartOpen a ∩ innerChartOpen b ∩
innerChartOpen c` — the shrinking-side 2-cochain domain (relatively compact in `coverTripleImage`). -/
noncomputable def WovTriple (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) : Set ℂ :=
  (chartAt (H := ℂ) (montel_coverCenter (X := X) t.1)) ''
    (innerChartOpen (X := X) (montel_coverCenter (X := X) t.1)
      ∩ innerChartOpen (X := X) (montel_coverCenter (X := X) t.2.1)
      ∩ innerChartOpen (X := X) (montel_coverCenter (X := X) t.2.2))

theorem isOpen_WovTriple (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    IsOpen (WovTriple (X := X) t) :=
  (chartAt (H := ℂ) (montel_coverCenter (X := X) t.1)).isOpen_image_of_subset_source
    (((innerChartOpen_isOpen (montel_coverCenter (X := X) t.1)).inter
      (innerChartOpen_isOpen (montel_coverCenter (X := X) t.2.1))).inter
      (innerChartOpen_isOpen (montel_coverCenter (X := X) t.2.2)))
    ((Set.inter_subset_left.trans Set.inter_subset_left).trans
      (innerChartOpen_subset_chartAt_source_aux t.1))

/-- **Sup-norm 2-cochains, holomorphic shrinking side** `C2Holo` — bounded-holomorphic on each open
triple `WovTriple t` (target of the shrinking-side `δ¹`). -/
abbrev C2Holo : Type :=
  ∀ t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card),
    BddHol (WovTriple (X := X) t)

noncomputable instance : NormedAddCommGroup (C2Holo (X := X)) := inferInstance
noncomputable instance : NormedSpace ℂ (C2Holo (X := X)) := inferInstance

/-- `C2Holo` is Banach (finite product of the Banach `BddHol`). -/
noncomputable instance : CompleteSpace (C2Holo (X := X)) := by
  haveI : ∀ t, CompleteSpace (BddHol (WovTriple (X := X) t)) := fun t =>
    BddHol.completeSpace (isOpen_WovTriple t)
  infer_instance

/-- The cover transition `τ_{ab}` is analytic on the OPEN triple `WovTriple (a,b,c)`. -/
theorem analyticOn_coverTransition_WovTriple (a b c : Fin ((chartCover : Finset X).card)) :
    AnalyticOn ℂ (coverTransition (X := X) a b) (WovTriple (X := X) (a, b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩
  apply AnalyticAt.analyticWithinAt
  exact transition_analyticAt_of_mem
    (innerChartOpen_subset_chartAt_source_aux a hxa)
    (innerChartOpen_subset_chartAt_source_aux b hxb)

/-- The cover transition `τ_{ab}` maps the OPEN triple `WovTriple (a,b,c)` (chart-`a` coordinates) into
the shrinking `Wov (b,c)` (chart-`b` image of `innerChartOpen b ∩ innerChartOpen c`).  The `(b,c)`
transport is routed through `Wov (b,c)` — matching the `Cshr` shrinking-component domain `BddHol (Wov
(b,c))` — rather than the larger `Uov (b,c)`.  A point `φ_a x` with `x ∈ innerChartOpen a ∩
innerChartOpen b ∩ innerChartOpen c` maps to `φ_b x` with `x ∈ innerChartOpen b ∩ innerChartOpen c`. -/
theorem mapsTo_coverTransition_WovTriple_shrink (a b c : Fin ((chartCover : Finset X).card)) :
    Set.MapsTo (coverTransition (X := X) a b) (WovTriple (X := X) (a, b, c))
      ((chartCoverHolomorphicDiskOverlapData (X := X)).Wov (b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, hxc⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter (X := X) a)).source :=
    innerChartOpen_subset_chartAt_source_aux a hxa
  exact ⟨x, ⟨hxb, hxc⟩, by
    simp only [montel_coverCenter_eq_coverCenter, coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (coverCenter (X := X) a)).left_inv hxa_src]⟩

/-- The OPEN triple `WovTriple (a,b,c)` lies in `Wov (a,b)` (chart-`a` image of `innerChartOpen a ∩
innerChartOpen b ⊇ innerChartOpen a ∩ innerChartOpen b ∩ innerChartOpen c`). -/
theorem WovTriple_subset_Wov_fst_snd (a b c : Fin ((chartCover : Finset X).card)) :
    WovTriple (X := X) (a, b, c) ⊆ (chartCoverHolomorphicDiskOverlapData (X := X)).Wov (a, b) :=
  Set.image_mono (Set.inter_subset_left)

/-- The OPEN triple `WovTriple (a,b,c)` lies in `Wov (a,c)`. -/
theorem WovTriple_subset_Wov_fst_trd (a b c : Fin ((chartCover : Finset X).card)) :
    WovTriple (X := X) (a, b, c) ⊆ (chartCoverHolomorphicDiskOverlapData (X := X)).Wov (a, c) :=
  Set.image_mono (fun _ hx => ⟨hx.1.1, hx.2⟩)

/-- **The cross-chart Čech `δ¹` on the HOLOMORPHIC shrinking side** `d.Cshr →L[ℂ] C2Holo`.
Componentwise on the triple `(a,b,c)`,
    `(δ¹s)_{abc} = (s_{bc} ∘ τ_{ab}) − s_{ac} + s_{ab}`   on the OPEN `WovTriple (a,b,c)`,
the genuine Čech coboundary with the `(b,c)`-component transported chart-`b`→chart-`a` through the
holomorphic transition `τ_{ab}`.  All three pieces stay `BddHol` on the open triple: the off-diagonal
via `BddHol.precompHolCLM` (`Wov (b,c) → WovTriple`), the two diagonal restrictions via
`BddHol.restrictOpenCLM` (`Wov (a,c)`, `Wov (a,b) → WovTriple`). -/
noncomputable def delta1ModelHolo :
    (chartCoverHolomorphicDiskOverlapData (X := X)).Cshr →L[ℂ] C2Holo (X := X) :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.precompHolCLM (analyticOn_coverTransition_WovTriple t.1 t.2.1 t.2.2)
        (mapsTo_coverTransition_WovTriple_shrink t.1 t.2.1 t.2.2)).comp (proj (t.2.1, t.2.2))
      - (BddHol.restrictOpenCLM (WovTriple_subset_Wov_fst_trd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.2))
      + (BddHol.restrictOpenCLM (WovTriple_subset_Wov_fst_snd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.1))

/-- The component identity for the shrinking-side `δ¹` at the triple `t = (a,b,c)`. -/
theorem delta1ModelHolo_apply (s : (chartCoverHolomorphicDiskOverlapData (X := X)).Cshr)
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) :
    delta1ModelHolo s t
      = BddHol.precompHolCLM (analyticOn_coverTransition_WovTriple t.1 t.2.1 t.2.2)
          (mapsTo_coverTransition_WovTriple_shrink t.1 t.2.1 t.2.2) (s (t.2.1, t.2.2))
        - BddHol.restrictOpenCLM (WovTriple_subset_Wov_fst_trd t.1 t.2.1 t.2.2) (s (t.1, t.2.2))
        + BddHol.restrictOpenCLM (WovTriple_subset_Wov_fst_snd t.1 t.2.1 t.2.2)
            (s (t.1, t.2.1)) := rfl

/-- **The shrinking-side Čech coboundary pointwise formula.**  On the OPEN triple `WovTriple`, the `δ¹`
value at `z` is `s_{bc}` at the transported point `τ_{ab} z` minus `s_{ac}` at `z` plus `s_{ab}` at `z`
— the explicit cross-chart Čech `δ¹` formula `(δ¹s)_{abc}(z) = s_{bc}(τ_{ab} z) − s_{ac}(z) +
s_{ab}(z)`. -/
theorem delta1ModelHolo_apply_apply (s : (chartCoverHolomorphicDiskOverlapData (X := X)).Cshr)
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) {z : ℂ} (hz : z ∈ WovTriple (X := X) t) :
    (delta1ModelHolo s t).toFun z
      = (s (t.2.1, t.2.2)).toFun (coverTransition t.1 t.2.1 z)
        - (s (t.1, t.2.2)).toFun z + (s (t.1, t.2.1)).toFun z := by
  obtain ⟨a, b, c⟩ := t
  rw [delta1ModelHolo_apply, BddHol.toFun_add, Pi.add_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### The cover-side `δ¹` (REUSED from the continuous branch) -/

/-- **The cross-chart Čech `δ¹` on the COVER side** `d.Ccov →L[ℂ] Cochain2CovModel`.  REUSED verbatim
from `CechModelDifferential.delta1CovModel`: the holomorphic cover side `d.Ccov = ∀ p, BddHol (Uov p)`
is definitionally the continuous cover side (same cover centres `montel_coverCenter = coverCenter`, same
outer overlaps `Uov`), so the cover-side coboundary is identical. -/
noncomputable def delta1CovModelHolo :
    (chartCoverHolomorphicDiskOverlapData (X := X)).Ccov →L[ℂ] Cochain2CovModel (X := X) :=
  delta1CovModel

/-! ### The Čech cocycle identity `δ¹ ∘ δ⁰ = 0` (`hδδ`) -/

/-- **The chart-transition cocycle identity** on the OPEN triple `WovTriple`: `τ_{bc}(τ_{ab} z) = τ_{ac}
z` for `z ∈ WovTriple (a,b,c)`.  Geometrically `φ_c ∘ φ_b⁻¹ ∘ φ_b ∘ φ_a⁻¹ = φ_c ∘ φ_a⁻¹` where the inner
cancellations hold because the triple-overlap point `x` lies in all three chart sources.  The algebraic
heart of `δ¹∘δ⁰ = 0`. -/
theorem coverTransition_cocycle_Wov (a b c : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hz : z ∈ WovTriple (X := X) (a, b, c)) :
    coverTransition b c (coverTransition a b z) = coverTransition a c z := by
  obtain ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩ := hz
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter (X := X) a)).source :=
    innerChartOpen_subset_chartAt_source_aux a hxa
  have hxb_src : x ∈ (chartAt (H := ℂ) (coverCenter (X := X) b)).source :=
    innerChartOpen_subset_chartAt_source_aux b hxb
  simp only [montel_coverCenter_eq_coverCenter, coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (coverCenter (X := X) a)).left_inv hxa_src,
    (chartAt (H := ℂ) (coverCenter (X := X) b)).left_inv hxb_src]

/-- **`δ¹ ∘ δ⁰ = 0` (the Čech `hδδ`).**  The composite of the cross-chart `δ⁰` and the shrinking-side
`δ¹` vanishes — the defining Čech-complex identity `δ² = 0`.  Pointwise on the OPEN triple the six terms
of `(δ¹(δ⁰f))_{abc}(z)` collapse to `f_c(τ_{bc}(τ_{ab} z)) − f_c(τ_{ac} z)`, which is `0` by the cocycle
identity `coverTransition_cocycle_Wov` (the two `f_c`-arguments coincide). -/
theorem delta1_comp_delta0_holo :
    (delta1ModelHolo (X := X)).comp delta0ModelHolo = 0 := by
  ext f t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  -- reduce to a pointwise statement on `WovTriple t`
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ WovTriple (X := X) t
  · -- evaluate the six terms via the pointwise δ⁰/δ¹ formulas
    rw [show ((0 : C2Holo (X := X)) t).toFun z = 0 from rfl]
    rw [delta1ModelHolo_apply_apply _ _ hz]
    obtain ⟨a, b, c⟩ := t
    -- the three δ⁰ components, evaluated at the relevant transported points
    rw [delta0ModelHolo_apply_apply _ _ (mapsTo_coverTransition_WovTriple_shrink a b c hz),
      delta0ModelHolo_apply_apply _ _ (WovTriple_subset_Wov_fst_trd a b c hz),
      delta0ModelHolo_apply_apply _ _ (WovTriple_subset_Wov_fst_snd a b c hz)]
    -- identify the two `f_c` arguments `τ_{bc}(τ_{ab} z)` and `τ_{ac} z`
    rw [coverTransition_cocycle_Wov a b c hz]
    ring
  · -- off the triple both sides are the extend-by-zero value `0`
    rw [show ((0 : C2Holo (X := X)) t).toFun z = 0 from rfl,
      (delta1ModelHolo (delta0ModelHolo f) t).zero_off z hz]

/-! ### The 2-cochain restriction `ρ²` cover → holomorphic shrinking, and the `hcomm` square -/

/-- The OPEN triple `WovTriple (a,b,c)` lies in the cover triple-image `coverTripleImage (a,b,c)`
(chart-`a` image of `innerChartOpen a ∩ innerChartOpen b ∩ innerChartOpen c ⊆ chartOpen a ∩ chartOpen b
∩ chartOpen c`), so a cover 2-cochain restricts to a holomorphic shrinking 2-cochain. -/
theorem WovTriple_subset_coverTripleImage (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    WovTriple (X := X) t ⊆ coverTripleImage (X := X) t :=
  Set.image_mono (Set.inter_subset_inter
    (Set.inter_subset_inter
      (montel_innerChartOpen_subset_chartOpen (X := X) (montel_coverCenter (X := X) t.1))
      (montel_innerChartOpen_subset_chartOpen (X := X) (montel_coverCenter (X := X) t.2.1)))
    (montel_innerChartOpen_subset_chartOpen (X := X) (montel_coverCenter (X := X) t.2.2)))

/-- **The 2-cochain restriction `ρ² : Cochain2CovModel →L C2Holo`** (cover → holomorphic shrinking),
componentwise `BddHol.restrictOpenCLM` from the open cover triple-image to the open shrinking triple.
Carries the cover-side `δ¹` to the shrinking-side `δ¹` (the commuting square). -/
noncomputable def rho2ModelHolo : Cochain2CovModel (X := X) →L[ℂ] C2Holo (X := X) :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.restrictOpenCLM (WovTriple_subset_coverTripleImage t)).comp (proj t)

@[simp] theorem rho2ModelHolo_apply (g : Cochain2CovModel (X := X))
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) :
    rho2ModelHolo g t = BddHol.restrictOpenCLM (WovTriple_subset_coverTripleImage t) (g t) := by
  simp only [rho2ModelHolo, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **The commuting square** `δ¹_shr ∘ ρ = ρ² ∘ δ¹_cov`.  Restricting a cover 1-cochain to the
holomorphic shrinking and applying the shrinking `δ¹` is the same as applying the cover `δ¹` and
restricting the resulting 2-cochain — the Čech naturality of `δ¹` under cover-refinement.  Pointwise
both sides equal `x_{bc}(τ_{ab} z) − x_{ac}(z) + x_{ab}(z)` on the OPEN triple. -/
theorem delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov_holo :
    (delta1ModelHolo (X := X)).comp (chartCoverHolomorphicDiskOverlapData (X := X)).rhoRaw
      = rho2ModelHolo.comp delta1CovModelHolo := by
  ext x t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ WovTriple (X := X) t
  · -- LHS: shrinking δ¹ of the restricted cochain, at z
    rw [delta1ModelHolo_apply_apply _ _ hz]
    -- each `rhoRaw x` component is `x`-component restricted; evaluate on the smaller open
    obtain ⟨a, b, c⟩ := t
    rw [HolomorphicDiskOverlapData.rhoRaw_apply, HolomorphicDiskOverlapData.rhoRaw_apply,
      HolomorphicDiskOverlapData.rhoRaw_apply,
      BddHol.restrictOpenCLM_toFun_of_mem _ _ (mapsTo_coverTransition_WovTriple_shrink a b c hz),
      BddHol.restrictOpenCLM_toFun_of_mem _ _ (WovTriple_subset_Wov_fst_trd a b c hz),
      BddHol.restrictOpenCLM_toFun_of_mem _ _ (WovTriple_subset_Wov_fst_snd a b c hz)]
    -- RHS: restrict the cover δ¹ to the open triple, at z (`delta1CovModelHolo = delta1CovModel`)
    rw [rho2ModelHolo_apply, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]
    show _ = (delta1CovModel x (a, b, c)).toFun z
    rw [delta1CovModel_toFun_of_mem _ _ (WovTriple_subset_coverTripleImage (a, b, c) hz)]
    rfl
  · -- off the triple both sides are the extend-by-zero value `0`
    rw [(delta1ModelHolo ((chartCoverHolomorphicDiskOverlapData (X := X)).rhoRaw x) t).zero_off z hz,
      (rho2ModelHolo (delta1CovModelHolo x) t).zero_off z hz]

/-- **`hcomm` for the holomorphic-shrinking chart cover.**  If a cover 1-cochain `x` is a cocycle
(`δ¹_cov x = 0`), then its restriction `ρ x` (to the holomorphic shrinking) is a shrinking cocycle
(`δ¹_shr (ρ x) = 0`).  Immediate from the commuting square `δ¹_shr∘ρ = ρ²∘δ¹_cov`: `δ¹_shr(ρ x) =
ρ²(δ¹_cov x) = ρ²(0) = 0`.  This is the `HolomorphicCoboundaries.hcomm` field for the chart cover. -/
theorem hcomm_holo (x : (chartCoverHolomorphicDiskOverlapData (X := X)).Ccov) (hx : delta1CovModelHolo x = 0) :
    delta1ModelHolo ((chartCoverHolomorphicDiskOverlapData (X := X)).rhoRaw x) = 0 := by
  have h := congrArg (fun T => T x) delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov_holo
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h, hx, map_zero]

end Jacobians.Dolbeault
