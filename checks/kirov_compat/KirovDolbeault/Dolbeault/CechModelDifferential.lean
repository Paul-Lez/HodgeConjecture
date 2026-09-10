/-
  Čech finiteness — the CROSS-CHART Čech `δ⁰` on the sup-norm `BddHol` cochains (piece (a) of
  `exists_cechModel`, Forster 14.9).

  `CechModelDelta.lean` built the sup-norm cochain SPACES (`Cochain0Model`, `Cochain2*Model`) and their
  Banach structure, and flagged the next gap as the CROSS-CHART differentials — the off-diagonal
  components of the Čech coboundary, transported between neighbouring chart-images through the
  holomorphic chart transitions `φ_a ∘ φ_b⁻¹`. THIS FILE builds the Čech `δ⁰ : Cochain0Model →L Cshr`
  for the chart-cover model `chartCoverOverlapData`.

  THE CROSS-CHART SUBTLETY (recap).  A 0-cochain `f` assigns each cover chart `a` a bounded-holomorphic
  function `f a` on its OWN chart-image `coverSetImage a` (chart-`a` coordinates).  The Čech `δ⁰` on the
  overlap `(a,b)`, read in the FIRST chart `a` (matching `chartCoverOverlapData`'s `Uov`/`Kov`), is
      `(δ⁰f)_{ab} = (f b ∘ φ_b ∘ φ_a⁻¹) − (f a)`     on the shrinking `Kov (a,b)`,
  i.e. `f a` restricts directly, but `f b` (living in chart-`b` coordinates) must be TRANSPORTED to
  chart-`a` coordinates through the holomorphic transition `τ_{ab} = φ_b ∘ φ_a⁻¹`.  The two
  geometric witnesses the transport needs — `τ_{ab}` continuous on `Kov (a,b)` and mapping it into
  `coverSetImage b` — come from the `ω`-manifold's chart change (`transition_analyticAt_of_mem`,
  `CechModelManifold`), and the functional-analysis transport `g ↦ g ∘ τ` is `BddHol.precompCLM`
  (`BddHol`).  `δ⁰` is then the per-overlap difference (off-diagonal transport `−` diagonal
  restriction), assembled by `ContinuousLinearMap.pi`.

  This is the genuine content of part (a) of the `exists_cechModel` model.  Sorry-free, axiom-clean
  `[propext, Classical.choice, Quot.sound]`.  (The shrinking-side `δ¹`, the cover-side `δ¹cov`, the
  `hδδ`/`hcomm` algebra, the `leray` disk-acyclicity field, and the `cechH1 ≃ supH1` comparison remain
  — see `CechFinitenessWiring.exists_cechModel`.)
-/
import KirovDolbeault.Dolbeault.CechModelDelta
import KirovDolbeault.Dolbeault.CechModelManifold

open scoped Manifold ContDiff Topology
open Jacobians.Montel ContinuousLinearMap
open BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The chart transition `τ_{ab} = φ_b ∘ φ_a⁻¹` and its geometric witnesses on `Kov (a,b)` -/

/-- **The cover chart transition** `τ_{ab} = φ_b ∘ φ_a⁻¹` (chart-`a` coordinates → chart-`b`
coordinates), for the cover charts indexed `a, b : Fin #chartCover`.  Used to transport the `b`-side
0-cochain component into chart-`a` coordinates for the Čech `δ⁰`. -/
noncomputable def coverTransition (a b : Fin ((chartCover : Finset X).card)) : ℂ → ℂ :=
  (chartAt (H := ℂ) (coverCenter b)) ∘ (chartAt (H := ℂ) (coverCenter a)).symm

/-- The transition `τ_{ab}` is continuous on the compact overlap-shrinking `Kov (a,b)` (chart-`a`
image of `innerShrunk a ∩ innerShrunk b`): at each point it is analytic (`transition_analyticAt_of_mem`,
both centres' sources containing the inner-shrunk overlap point), hence continuous. -/
theorem continuousOn_coverTransition_Kov (a b : Fin ((chartCover : Finset X).card)) :
    ContinuousOn (coverTransition (X := X) a b) ((chartCoverOverlapData (X := X)).Kov (a, b)) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  apply ContinuousAt.continuousWithinAt
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
      (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
  have hxb_src : x ∈ (chartAt (H := ℂ) (coverCenter b)).source :=
    chartOpen_subset_chartAt_source (coverCenter b) (coverCenter_mem b)
      (innerShrunkChart_subset_chartOpen (coverCenter b) hxb)
  exact (transition_analyticAt_of_mem hxa_src hxb_src).continuousAt

/-- The transition `τ_{ab}` maps the shrinking `Kov (a,b)` (chart-`a` coordinates) into `coverSetImage
b` (chart-`b` image of `chartOpen b`), where the `b`-component of a 0-cochain is bounded-holomorphic.
A point `φ_a x` with `x ∈ innerShrunk a ∩ innerShrunk b` maps to `φ_b x ∈ φ_b '' (innerShrunk b) ⊆ φ_b
'' (chartOpen b) = coverSetImage b`. -/
theorem mapsTo_coverTransition_Kov (a b : Fin ((chartCover : Finset X).card)) :
    Set.MapsTo (coverTransition (X := X) a b) ((chartCoverOverlapData (X := X)).Kov (a, b))
      (coverSetImage (X := X) b) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
      (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
  exact ⟨x, innerShrunkChart_subset_chartOpen (coverCenter b) hxb, by
    simp only [coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (coverCenter a)).left_inv hxa_src]⟩

/-! ### The off-diagonal transport and the diagonal restriction (the two pieces of `δ⁰`) -/

/-- **The off-diagonal transport CLM.**  The `b`-component `f b : BddHol (coverSetImage b)`,
transported to chart-`a` coordinates through `τ_{ab}` and read on the compact shrinking `Kov (a,b)`, as
a bounded-continuous function there.  This is the `+` half of `(δ⁰f)_{ab}` (the cross-chart piece),
built from `BddHol.precompCLM` with the two transition witnesses. -/
noncomputable def transportComp (a b : Fin ((chartCover : Finset X).card)) :
    BddHol (coverSetImage (X := X) b) →L[ℂ] ((chartCoverOverlapData (X := X)).Kov (a, b) →ᵇ ℂ) :=
  BddHol.precompCLM (continuousOn_coverTransition_Kov a b) (mapsTo_coverTransition_Kov a b)

/-- The shrinking `Kov (a,b)` lies in `coverSetImage a` (chart-`a` image of `innerShrunk a ∩ innerShrunk
b ⊆ chartOpen a`), so the `a`-component restricts directly. -/
theorem Kov_subset_coverSetImage_fst (a b : Fin ((chartCover : Finset X).card)) :
    (chartCoverOverlapData (X := X)).Kov (a, b) ⊆ coverSetImage (X := X) a := by
  show (chartAt (H := ℂ) (coverCenter a)) ''
      (innerShrunkChart (X := X) (coverCenter a) ∩ innerShrunkChart (X := X) (coverCenter b))
    ⊆ coverSetImage (X := X) a
  unfold coverSetImage
  exact Set.image_mono
    (Set.inter_subset_left.trans (innerShrunkChart_subset_chartOpen (coverCenter a)))

/-- **The diagonal restriction CLM.**  The `a`-component `f a : BddHol (coverSetImage a)`, restricted to
the shrinking `Kov (a,b) ⊆ coverSetImage a`, as a bounded-continuous function there.  This is the `−`
half of `(δ⁰f)_{ab}` (the same-chart piece), built from `BddHol.restrictCLM`. -/
noncomputable def restrictComp (a b : Fin ((chartCover : Finset X).card)) :
    BddHol (coverSetImage (X := X) a) →L[ℂ] ((chartCoverOverlapData (X := X)).Kov (a, b) →ᵇ ℂ) :=
  BddHol.restrictCLM (Kov_subset_coverSetImage_fst a b)

/-! ### The cross-chart Čech `δ⁰ : Cochain0Model →L Cshr` -/

/-- **The cross-chart Čech `δ⁰`** of the chart-cover sup-norm model: `Cochain0Model →L[ℂ] Cshr`
(`chartCoverOverlapData`'s shrinking 1-cochains).  Componentwise on overlap `(a,b)`,
    `(δ⁰f)_{ab} = (transport of f b to chart-a) − (restriction of f a)`   on `Kov (a,b)`,
the genuine Čech coboundary with the `b`-side transported through the holomorphic transition `τ_{ab}`.
Assembled by `ContinuousLinearMap.pi` over the off-diagonal transport `transportComp` and diagonal
restriction `restrictComp`. -/
noncomputable def delta0Model : Cochain0Model (X := X) →L[ℂ] (chartCoverOverlapData (X := X)).Cshr :=
  ContinuousLinearMap.pi fun p =>
    (transportComp p.1 p.2).comp (proj p.2) - (restrictComp p.1 p.2).comp (proj p.1)

/-- The component identity for `δ⁰` at overlap `p = (a,b)`: the off-diagonal transport of `f b` minus
the diagonal restriction of `f a`. -/
theorem delta0Model_apply (f : Cochain0Model (X := X)) (p : (chartCoverOverlapData (X := X)).J) :
    delta0Model f p = transportComp p.1 p.2 (f p.2) - restrictComp p.1 p.2 (f p.1) := rfl

/-- **The Čech coboundary pointwise formula.**  On the shrinking `Kov (a,b)`, the `δ⁰` value at a point
`z` is `f b` evaluated at the transported point `τ_{ab} z` minus `f a` at `z` — the explicit
cross-chart Čech `δ⁰` formula `(δ⁰f)_{ab}(z) = f_b(τ_{ab} z) − f_a(z)`. -/
theorem delta0Model_apply_apply (f : Cochain0Model (X := X))
    (p : (chartCoverOverlapData (X := X)).J) (z : (chartCoverOverlapData (X := X)).Kov p) :
    delta0Model f p z = (f p.2).toFun (coverTransition p.1 p.2 z.1) - (f p.1).toFun z.1 := by
  have h : (delta0Model f p) z
      = (transportComp p.1 p.2 (f p.2)) z - (restrictComp p.1 p.2 (f p.1)) z := by
    rw [delta0Model_apply]; rfl
  rw [h, transportComp, restrictComp, BddHol.precompCLM_apply, BddHol.precompBcf_apply,
    BddHol.restrictCLM_apply, BddHol.restrict_apply]

/-! ### The cross-chart Čech `δ¹` on the COVER side `Ccov →L Cochain2CovModel`

The cover-side `δ¹` lands in the open-triple 2-cochains `Cochain2CovModel` (target of the cover-side
coboundary, whose kernel is `Z¹(cover)`).  On the triple `(a,b,c)`, read in the FIRST chart `a`
(matching `coverTripleImage`), the Čech `δ¹` is
    `(δ¹f)_{abc} = (f_{bc} ∘ τ_{ab}) − f_{ac} + f_{ab}`     on `coverTripleImage (a,b,c)`,
where `f_{ac}`, `f_{ab}` restrict directly to the smaller open triple-image (both `coverTripleImage
(a,b,c) ⊆ Uov (a,c)`, `⊆ Uov (a,b)`, same chart `a`), while `f_{bc}` (chart-`b` coordinates) is
transported to chart-`a` through the holomorphic transition `τ_{ab}` (analytic on the triple-image,
mapping it into `Uov (b,c)`).  All three components stay holomorphic on the OPEN triple-image, so the
result is `BddHol`; the transport is `BddHol.precompHolCLM` (analytic, open-set) and the diagonal
restrictions are `BddHol.restrictOpenCLM`. -/

/-- The cover transition `τ_{ab}` is analytic on the OPEN triple chart-image `coverTripleImage
(a,b,c)`: at each point it is analytic (`transition_analyticAt_of_mem`, both centres' sources containing
the triple outer-overlap point), hence analytic on the set. -/
theorem analyticOn_coverTransition_triple (a b c : Fin ((chartCover : Finset X).card)) :
    AnalyticOn ℂ (coverTransition (X := X) a b) (coverTripleImage (X := X) (a, b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩
  apply AnalyticAt.analyticWithinAt
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a) hxa
  have hxb_src : x ∈ (chartAt (H := ℂ) (coverCenter b)).source :=
    chartOpen_subset_chartAt_source (coverCenter b) (coverCenter_mem b) hxb
  exact transition_analyticAt_of_mem hxa_src hxb_src

/-- The cover transition `τ_{ab}` maps the OPEN triple chart-image `coverTripleImage (a,b,c)` (chart-`a`
coordinates) into `Uov (b,c)` (chart-`b` image of `chartOpen b ∩ chartOpen c`).  A point `φ_a x` with
`x ∈ chartOpen a ∩ chartOpen b ∩ chartOpen c` maps to `φ_b x` with `x ∈ chartOpen b ∩ chartOpen c`. -/
theorem mapsTo_coverTransition_triple (a b c : Fin ((chartCover : Finset X).card)) :
    Set.MapsTo (coverTransition (X := X) a b) (coverTripleImage (X := X) (a, b, c))
      ((chartCoverOverlapData (X := X)).Uov (b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, hxc⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a) hxa
  exact ⟨x, ⟨hxb, hxc⟩, by
    simp only [coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (coverCenter a)).left_inv hxa_src]⟩

/-- The open triple chart-image `coverTripleImage (a,b,c)` lies in `Uov (a,b)` (chart-`a` image of
`chartOpen a ∩ chartOpen b ⊇ chartOpen a ∩ chartOpen b ∩ chartOpen c`), so `f_{ab}` restricts. -/
theorem coverTripleImage_subset_Uov_fst_snd (a b c : Fin ((chartCover : Finset X).card)) :
    coverTripleImage (X := X) (a, b, c) ⊆ (chartCoverOverlapData (X := X)).Uov (a, b) :=
  Set.image_mono (Set.inter_subset_left)

/-- The open triple chart-image `coverTripleImage (a,b,c)` lies in `Uov (a,c)` (chart-`a` image of
`chartOpen a ∩ chartOpen c ⊇ chartOpen a ∩ chartOpen b ∩ chartOpen c`), so `f_{ac}` restricts. -/
theorem coverTripleImage_subset_Uov_fst_trd (a b c : Fin ((chartCover : Finset X).card)) :
    coverTripleImage (X := X) (a, b, c) ⊆ (chartCoverOverlapData (X := X)).Uov (a, c) :=
  Set.image_mono (fun _ hx => ⟨hx.1.1, hx.2⟩)

/-- **The cover-side transport CLM.**  The `(b,c)`-component `f_{bc} : BddHol (Uov (b,c))`, transported
to chart-`a` coordinates through the analytic transition `τ_{ab}` and landing on the open triple-image,
as a `BddHol (coverTripleImage (a,b,c))`.  The cross-chart `+` piece of `(δ¹f)_{abc}`, via
`BddHol.precompHolCLM`. -/
noncomputable def transportCovTriple (a b c : Fin ((chartCover : Finset X).card)) :
    BddHol ((chartCoverOverlapData (X := X)).Uov (b, c)) →L[ℂ]
      BddHol (coverTripleImage (X := X) (a, b, c)) :=
  BddHol.precompHolCLM (analyticOn_coverTransition_triple a b c) (mapsTo_coverTransition_triple a b c)

/-- **The cross-chart Čech `δ¹` on the COVER side** `Cochain2CovModel`.  Componentwise on the triple
`(a,b,c)`,
    `(δ¹f)_{abc} = (transport of f_{bc} to chart-a) − (restriction of f_{ac}) + (restriction of f_{ab})`
on the open triple-image `coverTripleImage (a,b,c)` — the genuine Čech coboundary with the cross-chart
`(b,c)`-component transported through the holomorphic transition `τ_{ab}`.  Assembled by
`ContinuousLinearMap.pi` over the cover-side transport `transportCovTriple` and the two diagonal
open-restrictions `BddHol.restrictOpenCLM`. -/
noncomputable def delta1CovModel :
    DiskOverlapData.Ccov (chartCoverOverlapData (X := X)) →L[ℂ] Cochain2CovModel (X := X) :=
  ContinuousLinearMap.pi fun t =>
    (transportCovTriple t.1 t.2.1 t.2.2).comp (proj (t.2.1, t.2.2))
      - (BddHol.restrictOpenCLM (coverTripleImage_subset_Uov_fst_trd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.2))
      + (BddHol.restrictOpenCLM (coverTripleImage_subset_Uov_fst_snd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.1))

/-- The component identity for the cover-side `δ¹` at the triple `t = (a,b,c)`. -/
theorem delta1CovModel_apply (f : DiskOverlapData.Ccov (chartCoverOverlapData (X := X)))
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) :
    delta1CovModel f t = transportCovTriple t.1 t.2.1 t.2.2 (f (t.2.1, t.2.2))
      - BddHol.restrictOpenCLM (coverTripleImage_subset_Uov_fst_trd t.1 t.2.1 t.2.2) (f (t.1, t.2.2))
      + BddHol.restrictOpenCLM (coverTripleImage_subset_Uov_fst_snd t.1 t.2.1 t.2.2)
          (f (t.1, t.2.1)) := rfl

/-- **The cover-side Čech coboundary pointwise formula.**  On the open triple-image, the `δ¹` value at
`z` is `f_{bc}` at the transported point `τ_{ab} z` minus `f_{ac}` at `z` plus `f_{ab}` at `z` — the
explicit cross-chart Čech `δ¹` formula `(δ¹f)_{abc}(z) = f_{bc}(τ_{ab} z) − f_{ac}(z) + f_{ab}(z)`. -/
theorem delta1CovModel_toFun_of_mem (f : DiskOverlapData.Ccov (chartCoverOverlapData (X := X)))
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) {z : ℂ} (hz : z ∈ coverTripleImage (X := X) t) :
    (delta1CovModel f t).toFun z
      = (f (t.2.1, t.2.2)).toFun (coverTransition t.1 t.2.1 z)
        - (f (t.1, t.2.2)).toFun z + (f (t.1, t.2.1)).toFun z := by
  obtain ⟨a, b, c⟩ := t
  rw [delta1CovModel_apply]
  rw [BddHol.toFun_add, Pi.add_apply, BddHol.toFun_sub, Pi.sub_apply]
  rw [transportCovTriple, BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### The cross-chart Čech `δ¹` on the SHRINKING side `Cshr →L Cochain2Model`

The shrinking-side `δ¹` lands in the compact-triple 2-cochains `Cochain2Model t = (coverTripleShrink t
→ᵇ ℂ)`.  On the triple `(a,b,c)`, read in the FIRST chart `a` (matching `coverTripleShrink`), the Čech
`δ¹` is
    `(δ¹s)_{abc} = (s_{bc} ∘ τ_{ab}) − s_{ac} + s_{ab}`     on `coverTripleShrink (a,b,c)`,
where `s_{ac}`, `s_{ab}` restrict directly (both `coverTripleShrink (a,b,c) ⊆ Kov (a,c)`, `⊆ Kov
(a,b)`, same chart `a`) and `s_{bc}` (chart-`b` coordinates) is transported through `τ_{ab}` (continuous
on the triple shrinking, mapping it into `Kov (b,c)`).  Everything lives in `→ᵇ` on compacts, so the
transport/restriction are bounded-continuous precompositions `bcfCompContinuousCLM` with the
appropriate `C(↥coverTripleShrink, ↥Kov ·)` reindexings. -/

/-- Build a `C(↥S, ↥T)` from a `ContinuousOn f S` mapping `S` into `T`. The continuous reindexing the
shrinking-side `δ¹` precomposes with. -/
noncomputable def subtypeCM {S T : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f S)
    (hmaps : Set.MapsTo f S T) : C(↥S, ↥T) :=
  ⟨fun z => ⟨f z.1, hmaps z.2⟩,
    continuous_induced_rng.mpr (hf.comp_continuous continuous_subtype_val Subtype.coe_prop)⟩

@[simp] theorem subtypeCM_apply {S T : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f S)
    (hmaps : Set.MapsTo f S T) (z : ↥S) : (subtypeCM hf hmaps z : ℂ) = f z.1 := rfl

/-- The transition `τ_{ab}` is continuous on the compact triple shrinking `coverTripleShrink (a,b,c)`
(at each point analytic, hence continuous). -/
theorem continuousOn_coverTransition_triple (a b c : Fin ((chartCover : Finset X).card)) :
    ContinuousOn (coverTransition (X := X) a b) (coverTripleShrink (X := X) (a, b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩
  apply ContinuousAt.continuousWithinAt
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
      (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
  have hxb_src : x ∈ (chartAt (H := ℂ) (coverCenter b)).source :=
    chartOpen_subset_chartAt_source (coverCenter b) (coverCenter_mem b)
      (innerShrunkChart_subset_chartOpen (coverCenter b) hxb)
  exact (transition_analyticAt_of_mem hxa_src hxb_src).continuousAt

/-- The transition `τ_{ab}` maps the compact triple shrinking `coverTripleShrink (a,b,c)` (chart-`a`
coordinates) into `Kov (b,c)` (chart-`b` image of `innerShrunk b ∩ innerShrunk c`). -/
theorem mapsTo_coverTransition_triple_shrink (a b c : Fin ((chartCover : Finset X).card)) :
    Set.MapsTo (coverTransition (X := X) a b) (coverTripleShrink (X := X) (a, b, c))
      ((chartCoverOverlapData (X := X)).Kov (b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, hxc⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
      (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
  exact ⟨x, ⟨hxb, hxc⟩, by
    simp only [coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (coverCenter a)).left_inv hxa_src]⟩

/-- The compact triple shrinking `coverTripleShrink (a,b,c)` lies in `Kov (a,b)` (chart-`a` image of
`innerShrunk a ∩ innerShrunk b ⊇ innerShrunk a ∩ innerShrunk b ∩ innerShrunk c`). -/
theorem coverTripleShrink_subset_Kov_fst_snd (a b c : Fin ((chartCover : Finset X).card)) :
    coverTripleShrink (X := X) (a, b, c) ⊆ (chartCoverOverlapData (X := X)).Kov (a, b) :=
  Set.image_mono (Set.inter_subset_left)

/-- The compact triple shrinking `coverTripleShrink (a,b,c)` lies in `Kov (a,c)`. -/
theorem coverTripleShrink_subset_Kov_fst_trd (a b c : Fin ((chartCover : Finset X).card)) :
    coverTripleShrink (X := X) (a, b, c) ⊆ (chartCoverOverlapData (X := X)).Kov (a, c) :=
  Set.image_mono (fun _ hx => ⟨hx.1.1, hx.2⟩)

/-- The transition reindexing `C(↥coverTripleShrink (a,b,c), ↥Kov (b,c))` for the cross-chart `s_{bc}`
transport. -/
noncomputable def coverTransitionTripleCM (a b c : Fin ((chartCover : Finset X).card)) :
    C(↥(coverTripleShrink (X := X) (a, b, c)), ↥((chartCoverOverlapData (X := X)).Kov (b, c))) :=
  subtypeCM (continuousOn_coverTransition_triple a b c) (mapsTo_coverTransition_triple_shrink a b c)

/-- The inclusion reindexing `C(↥coverTripleShrink (a,b,c), ↥Kov (a,b))` for the diagonal `s_{ab}`. -/
noncomputable def inclTripleFstSndCM (a b c : Fin ((chartCover : Finset X).card)) :
    C(↥(coverTripleShrink (X := X) (a, b, c)), ↥((chartCoverOverlapData (X := X)).Kov (a, b))) :=
  subtypeCM continuousOn_id (fun _ hz => coverTripleShrink_subset_Kov_fst_snd a b c hz)

/-- The inclusion reindexing `C(↥coverTripleShrink (a,b,c), ↥Kov (a,c))` for the diagonal `s_{ac}`. -/
noncomputable def inclTripleFstTrdCM (a b c : Fin ((chartCover : Finset X).card)) :
    C(↥(coverTripleShrink (X := X) (a, b, c)), ↥((chartCoverOverlapData (X := X)).Kov (a, c))) :=
  subtypeCM continuousOn_id (fun _ hz => coverTripleShrink_subset_Kov_fst_trd a b c hz)

/-- **The cross-chart Čech `δ¹` on the SHRINKING side** `Cshr →L[ℂ] Cochain2Model`.  Componentwise on
the triple `(a,b,c)`,
    `(δ¹s)_{abc} = (s_{bc} ∘ τ_{ab}) − (s_{ac}|·) + (s_{ab}|·)`   on `coverTripleShrink (a,b,c)`,
the genuine Čech coboundary with the `(b,c)`-component transported chart-`b`→chart-`a` through the
holomorphic transition `τ_{ab}`.  Assembled by `ContinuousLinearMap.pi` over the bounded-continuous
precompositions `bcfCompContinuousCLM` with the transition reindexing and the two inclusions. -/
noncomputable def delta1Model :
    (chartCoverOverlapData (X := X)).Cshr →L[ℂ] Cochain2Model (X := X) :=
  ContinuousLinearMap.pi fun t =>
    (bcfCompContinuousCLM (coverTransitionTripleCM t.1 t.2.1 t.2.2)).comp (proj (t.2.1, t.2.2))
      - (bcfCompContinuousCLM (inclTripleFstTrdCM t.1 t.2.1 t.2.2)).comp (proj (t.1, t.2.2))
      + (bcfCompContinuousCLM (inclTripleFstSndCM t.1 t.2.1 t.2.2)).comp (proj (t.1, t.2.1))

/-- The component identity for the shrinking-side `δ¹` at the triple `t = (a,b,c)`. -/
theorem delta1Model_apply (s : (chartCoverOverlapData (X := X)).Cshr)
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) :
    delta1Model s t = (s (t.2.1, t.2.2)).compContinuous (coverTransitionTripleCM t.1 t.2.1 t.2.2)
      - (s (t.1, t.2.2)).compContinuous (inclTripleFstTrdCM t.1 t.2.1 t.2.2)
      + (s (t.1, t.2.1)).compContinuous (inclTripleFstSndCM t.1 t.2.1 t.2.2) := rfl

/-- **The shrinking-side Čech coboundary pointwise formula.**  On the compact triple shrinking, the
`δ¹` value at `z` is `s_{bc}` at the transported point `τ_{ab} z` minus `s_{ac}` at `z` plus `s_{ab}` at
`z` — the explicit cross-chart Čech `δ¹` formula `(δ¹s)_{abc}(z) = s_{bc}(τ_{ab} z) − s_{ac}(z) +
s_{ab}(z)` (`s_{ac}`, `s_{ab}` at the *same point* `z`, via the inclusion of compacts). -/
theorem delta1Model_apply_apply (s : (chartCoverOverlapData (X := X)).Cshr)
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) (z : ↥(coverTripleShrink (X := X) t)) :
    delta1Model s t z
      = s (t.2.1, t.2.2) ⟨coverTransition t.1 t.2.1 z.1, mapsTo_coverTransition_triple_shrink _ _ _ z.2⟩
        - s (t.1, t.2.2) ⟨z.1, coverTripleShrink_subset_Kov_fst_trd _ _ _ z.2⟩
        + s (t.1, t.2.1) ⟨z.1, coverTripleShrink_subset_Kov_fst_snd _ _ _ z.2⟩ := by
  obtain ⟨a, b, c⟩ := t
  rw [delta1Model_apply]
  simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.compContinuous_apply, coverTransitionTripleCM, inclTripleFstTrdCM]
  rfl

/-! ### The Čech cocycle identity `δ¹ ∘ δ⁰ = 0` (`hδδ`) -/

/-- **The chart-transition cocycle identity** on the triple shrinking: `τ_{bc}(τ_{ab} z) = τ_{ac} z`
for `z ∈ coverTripleShrink (a,b,c)`.  Geometrically `φ_c ∘ φ_b⁻¹ ∘ φ_b ∘ φ_a⁻¹ = φ_c ∘ φ_a⁻¹` where the
inner cancellations `φ_b⁻¹∘φ_b`, `φ_a⁻¹∘φ_a` hold because the triple-overlap point `x` lies in all three
chart sources.  This is the algebraic heart of `δ¹∘δ⁰ = 0` (the `f_c`-terms land at the SAME point). -/
theorem coverTransition_cocycle (a b c : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hz : z ∈ coverTripleShrink (X := X) (a, b, c)) :
    coverTransition b c (coverTransition a b z) = coverTransition a c z := by
  obtain ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩ := hz
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
      (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
  have hxb_src : x ∈ (chartAt (H := ℂ) (coverCenter b)).source :=
    chartOpen_subset_chartAt_source (coverCenter b) (coverCenter_mem b)
      (innerShrunkChart_subset_chartOpen (coverCenter b) hxb)
  simp only [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (coverCenter a)).left_inv hxa_src,
    (chartAt (H := ℂ) (coverCenter b)).left_inv hxb_src]

/-- **`δ¹ ∘ δ⁰ = 0` (the Čech `hδδ`).**  The composite of the cross-chart `δ⁰` and the shrinking-side
`δ¹` vanishes — the defining Čech-complex identity `δ² = 0`.  Pointwise on the triple shrinking the
six terms of `(δ¹(δ⁰f))_{abc}(z)` collapse to `f_c(τ_{bc}(τ_{ab} z)) − f_c(τ_{ac} z)`, which is `0` by
the cocycle identity `coverTransition_cocycle` (the two `f_c`-arguments coincide).  This makes the
sup-norm cochains a genuine Čech `δ`-complex (`B¹ ⊆ Z¹`), the `Coboundaries.hδδ` field for the
chart-cover model. -/
theorem delta1_comp_delta0_eq_zero :
    (delta1Model (X := X)).comp delta0Model = 0 := by
  ext f t z
  -- reduce the LHS value to the explicit six-term form
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  show delta1Model (delta0Model f) t z = (0 : Cochain2Model (X := X)) t z
  rw [delta1Model_apply_apply]
  -- the three `δ⁰` components, evaluated at the relevant points
  rw [delta0Model_apply_apply, delta0Model_apply_apply, delta0Model_apply_apply]
  -- after the rewrites the `f_c` arguments are `τ_{bc}(τ_{ab} z)` and `τ_{ac} z`; identify them
  obtain ⟨a, b, c⟩ := t
  rw [coverTransition_cocycle a b c z.2]
  show _ = (0 : Cochain2Model (X := X)) (a, b, c) z
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  ring

/-! ### The 2-cochain restriction `ρ²` cover → shrinking, and the commuting square `hcomm` -/

/-- The compact triple shrinking lies in the open triple-image (chart-`a` image of `innerShrunk a ∩
innerShrunk b ∩ innerShrunk c ⊆ chartOpen a ∩ chartOpen b ∩ chartOpen c`).  So a 2-cochain holomorphic
on the open triple-image restricts to a bounded-continuous function on the compact triple shrinking. -/
theorem coverTripleShrink_subset_coverTripleImage (t : Fin ((chartCover : Finset X).card) ×
    Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)) :
    coverTripleShrink (X := X) t ⊆ coverTripleImage (X := X) t :=
  Set.image_mono (Set.inter_subset_inter
    (Set.inter_subset_inter (innerShrunkChart_subset_chartOpen (coverCenter t.1))
      (innerShrunkChart_subset_chartOpen (coverCenter t.2.1)))
    (innerShrunkChart_subset_chartOpen (coverCenter t.2.2)))

/-- **The 2-cochain restriction `ρ² : Cochain2CovModel →L Cochain2Model`** (cover → shrinking),
componentwise `BddHol.restrictCLM` from the open triple-image to the compact triple shrinking.  Carries
the cover-side `δ¹` to the shrinking-side `δ¹` (the commuting square `rho2_comp_delta1Cov`). -/
noncomputable def rho2Model : Cochain2CovModel (X := X) →L[ℂ] Cochain2Model (X := X) :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.restrictCLM (coverTripleShrink_subset_coverTripleImage t)).comp (proj t)

@[simp] theorem rho2Model_apply (g : Cochain2CovModel (X := X))
    (t : Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card) ×
      Fin ((chartCover : Finset X).card)) :
    rho2Model g t = BddHol.restrictCLM (coverTripleShrink_subset_coverTripleImage t) (g t) := by
  simp only [rho2Model, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **The commuting square** `δ¹_shr ∘ ρ = ρ² ∘ δ¹_cov`.  Restricting a cover 1-cochain to the shrinking
and applying the shrinking `δ¹` is the same as applying the cover `δ¹` and restricting the resulting
2-cochain — the Čech naturality of `δ¹` under cover-refinement.  Pointwise both sides equal
`x_{bc}(τ_{ab} z) − x_{ac}(z) + x_{ab}(z)` on the triple shrinking.  This is the bridge that gives the
`Coboundaries.hcomm` field (restriction carries cocycles to cocycles). -/
theorem delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov :
    (delta1Model (X := X)).comp (chartCoverOverlapData (X := X)).rhoRaw
      = rho2Model.comp delta1CovModel := by
  ext x t z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- LHS: shrinking δ¹ of the restricted cochain, at z
  rw [delta1Model_apply_apply]
  -- each `rhoRaw x` component is `x`-component restricted; evaluate
  simp only [DiskOverlapData.rhoRaw_apply, BddHol.restrictCLM_apply, BddHol.restrict_apply]
  -- RHS: restrict the cover δ¹ to the shrinking, at z
  rw [rho2Model_apply, BddHol.restrictCLM_apply, BddHol.restrict_apply,
    delta1CovModel_toFun_of_mem _ _ (coverTripleShrink_subset_coverTripleImage t z.2)]

/-- **`hcomm` for the chart cover (restriction carries cover-cocycles to shrinking-cocycles).**  If a
cover 1-cochain `x` is a cocycle (`δ¹_cov x = 0`), then its restriction `ρ x` is a shrinking cocycle
(`δ¹_shr (ρ x) = 0`).  Immediate from the commuting square `δ¹_shr∘ρ = ρ²∘δ¹_cov`: `δ¹_shr(ρ x) =
ρ²(δ¹_cov x) = ρ²(0) = 0`.  This is the `Coboundaries.hcomm` field for the chart-cover model. -/
theorem delta1_rhoRaw_eq_zero_of_delta1Cov_eq_zero
    (x : DiskOverlapData.Ccov (chartCoverOverlapData (X := X)))
    (hx : delta1CovModel x = 0) :
    delta1Model ((chartCoverOverlapData (X := X)).rhoRaw x) = 0 := by
  have h := congrArg (fun T => T x) delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h, hx, map_zero]

/-! ### Assembling the chart-cover `Coboundaries` (structural fields PROVEN; `leray` isolated)

All FOUR structural `Coboundaries` fields for the chart cover are now proven:
`δ⁰ = delta0Model`, `δ¹ = delta1Model`, `δ¹cov = delta1CovModel`, `hδδ = delta1_comp_delta0_eq_zero`,
`hcomm = delta1_rhoRaw_eq_zero_of_delta1Cov_eq_zero`.  The ONE remaining field is `leray` — the genuine
disk-acyclicity / Leray content (every shrinking 1-cocycle is, modulo a shrinking coboundary, the
restriction of a COVER 1-cocycle).  This is NOT a structural identity: it is the analytic theorem
`H¹(disk, 𝒪) = 0` (proven: `DbarDiskCohomology.dbar_solvable_ball`) globalised over the cover via a
partition of unity + Čech refinement.  The soundness note and the continuous-shrinking branch have now
been deleted; the corrected holomorphic-shrinking model lives in `CechModelHolomorphic.lean`. -/

/-- **The diagonal of a shrinking 1-cocycle vanishes** (a structural necessary condition for the
`ChartCoverContinuousLeray` hypothesis).  For any cocycle `s` (`delta1Model s = 0`) and any cover index `a`, the
diagonal component `s (a,a)` is `0` on `Kov (a,a)`: the triple `(a,a,a)` gives
`(δ¹s)_{aaa}(z) = s_{aa}(τ_{aa} z) − s_{aa}(z) + s_{aa}(z)`, and `τ_{aa} = id` on `Kov (a,a)`, so this
collapses to `s_{aa}(z) = 0`.  This pins the cocycle structure used by the (corrected) disk-acyclicity
splitting; it is the chart-cover analogue of the antisymmetry/diagonal Čech relations. -/
theorem delta1Model_diagonal_eq_zero (s : (chartCoverOverlapData (X := X)).Cshr)
    (hs : delta1Model (X := X) s = 0) (a : Fin ((chartCover : Finset X).card))
    (z : ↥(coverTripleShrink (X := X) (a, a, a))) :
    s (a, a) ⟨z.1, coverTripleShrink_subset_Kov_fst_snd a a a z.2⟩ = 0 := by
  have hz0 : delta1Model (X := X) s (a, a, a) z = 0 := by rw [hs]; rfl
  rw [delta1Model_apply_apply] at hz0
  -- `τ_{aa} z = z` on `Kov (a,a)`, so the first BCF argument matches the others.
  have htau : coverTransition (X := X) a a z.1 = z.1 := by
    obtain ⟨x, ⟨⟨hxa, _⟩, _⟩, hxz⟩ := z.2
    have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
      chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
        (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
    rw [← hxz]; simp only [coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (coverCenter a)).left_inv hxa_src]
  rw [show (⟨coverTransition (X := X) a a z.1, mapsTo_coverTransition_triple_shrink a a a z.2⟩
        : ↥((chartCoverOverlapData (X := X)).Kov (a, a)))
      = ⟨z.1, coverTripleShrink_subset_Kov_fst_trd a a a z.2⟩ from Subtype.ext htau] at hz0
  rw [show (⟨z.1, coverTripleShrink_subset_Kov_fst_trd a a a z.2⟩
        : ↥((chartCoverOverlapData (X := X)).Kov (a, a)))
      = ⟨z.1, coverTripleShrink_subset_Kov_fst_snd a a a z.2⟩ from Subtype.ext rfl] at hz0
  -- `s_{aa}(z) − s_{aa}(z) + s_{aa}(z) = 0`.
  linear_combination hz0

/-! ### Packaging the standard Čech differential construction

The pieces above already prove the standard cross-chart Čech differential construction for the
chart-cover model.  This bundle packages the proven `δ⁰/δ¹` data so downstream code can refer to the
construction as a single object; the genuine Leray/globalization theorem still lives in the finiteness
node. -/

/-- The standard chart-cover Čech differential bundle, packaging the proven `δ⁰`, `δ¹`, `δ¹cov`,
`δ¹∘δ⁰ = 0`, and commuting-square data.  This is the structural half of the model construction; the
`leray` field is handled separately downstream. -/
structure ChartCoverDifferentialData where
  /-- The 0-cochain space. -/
  C0 : Type
  [ng0 : NormedAddCommGroup C0]
  [ns0 : NormedSpace ℂ C0]
  [cs0 : CompleteSpace C0]
  /-- The 2-cochain space on the shrinking. -/
  C2 : Type
  [ng2 : NormedAddCommGroup C2]
  [ns2 : NormedSpace ℂ C2]
  /-- The 2-cochain space on the cover. -/
  C2cov : Type
  [ng2c : NormedAddCommGroup C2cov]
  [ns2c : NormedSpace ℂ C2cov]
  /-- The cross-chart `δ⁰`. -/
  δ0 : C0 →L[ℂ] (chartCoverOverlapData (X := X)).Cshr
  /-- The shrinking-side `δ¹`. -/
  δ1 : (chartCoverOverlapData (X := X)).Cshr →L[ℂ] C2
  /-- The cover-side `δ¹`. -/
  δ1cov : (chartCoverOverlapData (X := X)).Ccov →L[ℂ] C2cov
  /-- `δ¹ ∘ δ⁰ = 0`. -/
  hδδ : δ1.comp δ0 = 0
  /-- Restriction carries cover cocycles to shrinking cocycles. -/
  hcomm : ∀ x : (chartCoverOverlapData (X := X)).Ccov, δ1cov x = 0 →
    δ1 ((chartCoverOverlapData (X := X)).rhoRaw x) = 0

/-- The standard chart-cover Čech differential data, packaged as a single record. -/
noncomputable def chartCoverDifferentialData : ChartCoverDifferentialData (X := X) where
  C0 := Cochain0Model (X := X)
  C2 := Cochain2Model (X := X)
  C2cov := Cochain2CovModel (X := X)
  δ0 := delta0Model
  δ1 := delta1Model
  δ1cov := delta1CovModel
  hδδ := delta1_comp_delta0_eq_zero
  hcomm := delta1_rhoRaw_eq_zero_of_delta1Cov_eq_zero

end Jacobians.Dolbeault
