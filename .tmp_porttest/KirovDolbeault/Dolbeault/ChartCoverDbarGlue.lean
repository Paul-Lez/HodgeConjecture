/-
  Čech finiteness — the genuine-cover ∂̄-globalization FOUNDATION (Forster §13–§14, Dolbeault).

  This file banks the verified, axiom-clean foundation for discharging the (corrected) disk-acyclicity
  `leray` field of the chart-cover model — the cross-chart analogue of the single-chart prototype in
  `GluedDbarDatum.lean`.

  ## Why a fresh file (and why the SharedChartCover prototype does not directly apply)

  `GluedDbarDatum.lean` globalises a cocycle on a `SharedChartCover` — a finite family of opens living
  in ONE chart `φ = chartAt center`.  Its partition of unity sums to `1` only on a CLOSED CORE
  `C ⊊ ⋃ Uᵢ` (a subordinate PoU cannot sum to `1` on the open `⋃ Uᵢ` of a non-covering family on a
  connected `X`); that is precisely the obstruction `dbarDatum_agrees_on_interiorCore` documents — the
  glued datum agrees with `∂̄(chartPrim)` only on `interior C`, so it does NOT give a full
  `HasGluedDbarDatum`.  A single chart cannot cover a compact connected Riemann surface, so the
  `SharedChartCover` route is fundamentally partial.

  The GENUINE chart cover (`Montel`'s `chartCover`, the geometry of `CechModelGeometry.lean`) is a
  different beast: the OUTER opens `chartOpen a` (indexed by the cover charts `coverCenter a`) genuinely
  COVER `X` (`iUnion_chartOpen_eq`).  Therefore a smooth partition of unity subordinate to
  `(chartOpen a)` summing to `1` on ALL of `X` exists (`exists_genuineCoverPoU`, below) — exactly what
  `SharedChartCover` lacked.  This unblocks the PoU-globalization OVER THE COVERED REGION (here all of
  `X`), the right tool for the cross-chart Forster argument once the model's shrinking-side cochains are
  in the holomorphic (`BddHol`) representation (see the `⚠ SOUNDNESS NOTE` in `CechModelDifferential.lean`
  — the current continuous `Cshr` makes the literal `ChartCoverContinuousLeray` unprovable, so the telescoping is
  intentionally NOT plugged into that unsound field here).

  ## What is delivered (all complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

  * `exists_genuineCoverPoU` — a smooth PoU over `𝓘(ℝ,ℂ)`, subordinate to `(chartOpen (coverCenter a))`,
    summing to `1` on ALL of `X` (the genuine-cover globalization foundation).
  * `genuineCoverPoU` / `genuineCoverPoU_subordinate` / `sum_genuineCoverPoU_eq_one` — the chosen PoU and
    its sum-to-one-everywhere value form (no closed-core restriction needed — the cover covers).
  * `genuineCoverPoU_tsupport_subset` — the subordination `tsupport ρ_a ⊆ chartOpen (coverCenter a)`.

  ## What remains (the genuine analytic gap, documented — NOT a tactic gap here)

  The cross-chart telescoping of the Bott–Tu glued datum `ω̂ = ∑_{a,b}(ρ_b·h_{ab})·∂̄ρ_a` read across
  DIFFERENT charts (the `h_{ab}` live in chart-`a`, `chart-`b transitions enter), plus the holomorphic
  re-splitting `dbar_solvable_ball` per chart-disk, and the assembly into the holomorphic cover cocycle.
  This is Forster *Lectures on Riemann Surfaces* Thm 14.x / the Dolbeault lemma globalised by a PoU; it
  consumes `DbarDiskCohomology.dbar_solvable_ball` (proven) and the chart-transition Wirtinger chain rule
  (`dbarDisk_comp_holo`, proven in `CechDiskAcyclic`).  It is left for the corrected (holomorphic-`Cshr`)
  model; the single-chart telescoping in `GluedDbarDatum.dbarDatum_apply` is the prototype.
-/
import KirovDolbeault.Dolbeault.CechModelGeometry
import KirovDolbeault.Dolbeault.DiskAcyclicCore
import KirovDolbeault.Dolbeault.GluedDbarDatum

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Jacobians.Montel

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-! ## The genuine-cover partition of unity (sum-to-one on ALL of `X`)

The outer opens `chartOpen (coverCenter a)` of `Montel`'s chart cover genuinely cover `X`, so — unlike a
`SharedChartCover` family — a subordinate smooth PoU summing to `1` on all of `X` exists.  We take the
closed sum-to-one locus `C := univ` (compact `X` is closed), so the closed-core PoU
`exists_smoothPartitionOfUnity_core` yields a genuine partition of unity over the whole surface. -/

/-- **The genuine chart cover covers `X`.**  `⋃ a, chartOpen (coverCenter a) = univ` — the inner
shrinkings already cover (`iUnion_innerShrunkChart_coverCenter_eq`) and `innerShrunkChart ⊆ chartOpen`. -/
theorem iUnion_chartOpen_coverCenter_eq :
    (⋃ a : Fin ((chartCover : Finset X).card), chartOpen (X := X) (coverCenter a)) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerShrunkChart_coverCenter_eq (X := X)]
  exact Set.iUnion_mono (fun a => innerShrunkChart_subset_chartOpen (coverCenter a))

/-- **The genuine-cover smooth PoU exists (sum-to-one on all of `X`).**  A smooth partition of unity over
`𝓘(ℝ,ℂ)`, subordinate to the genuine cover `(chartOpen (coverCenter a))`, summing to `1` on ALL of `X`
(the closed sum-to-one locus is `univ`).  This is the genuine-cover globalization foundation the
single-chart `SharedChartCover` could not supply: there the family does not cover `X`, so a subordinate
PoU can only sum to `1` on a closed core `C ⊊ ⋃ Uᵢ`; here the cover covers, so `C = univ`. -/
theorem exists_genuineCoverPoU :
    ∃ ρ : SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun a => chartOpen (X := X) (coverCenter a)) := by
  apply exists_smoothPartitionOfUnity_core
    (fun a => ⟨chartOpen (X := X) (coverCenter a), chartOpen_isOpen (coverCenter a)⟩)
    isClosed_univ
  rw [Set.univ_subset_iff]
  exact iUnion_chartOpen_coverCenter_eq

/-- A fixed genuine-cover smooth PoU subordinate to `(chartOpen (coverCenter a))`, summing to `1` on all
of `X`. -/
noncomputable def genuineCoverPoU :
    SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ :=
  (exists_genuineCoverPoU (X := X)).choose

/-- The genuine-cover PoU is subordinate to the cover `(chartOpen (coverCenter a))`
(`tsupport ρ_a ⊆ chartOpen (coverCenter a)`). -/
theorem genuineCoverPoU_subordinate :
    (genuineCoverPoU (X := X)).IsSubordinate (fun a => chartOpen (X := X) (coverCenter a)) :=
  (exists_genuineCoverPoU (X := X)).choose_spec

/-- **Sum-to-one EVERYWHERE.**  `∑ a, ρ_a x = 1` for every `x : X` (the genuine cover covers `X`, so the
sum-to-one locus is all of `X` — no closed-core restriction, unlike `SharedChartCover`). -/
theorem sum_genuineCoverPoU_eq_one (x : X) :
    ∑ a, (genuineCoverPoU (X := X)) a x = 1 :=
  smoothPartitionOfUnity_sum_eq_one_of_mem (genuineCoverPoU (X := X)) (Set.mem_univ x)

/-- The subordination, as a `tsupport` containment: `tsupport (ρ_a) ⊆ chartOpen (coverCenter a)`. -/
theorem genuineCoverPoU_tsupport_subset (a : Fin ((chartCover : Finset X).card)) :
    tsupport (genuineCoverPoU (X := X) a) ⊆ chartOpen (X := X) (coverCenter a) :=
  genuineCoverPoU_subordinate a

/-- Each PoU function `ρ_a` (real-valued, `X → ℝ`) is globally `C^∞` on `X` over `𝓘(ℝ,ℂ) → 𝓘(ℝ,ℝ)` —
the regularity the chart-read ∂̄ telescoping needs (`ρ_a` read in any chart is `ContDiffAt`, hence so is
its planar `∂̄(ofReal ∘ ρ_a)`).  Composing with `Complex.ofReal` gives the chart-read complex factor. -/
theorem contMDiff_genuineCoverPoU (a : Fin ((chartCover : Finset X).card)) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (genuineCoverPoU (X := X) a) :=
  (genuineCoverPoU (X := X) a).contMDiff


/-! ## Chart-read genuine-cover PoU functions

These are the cross-chart analogues of `SharedChartCover.rhoHat` / `dRhoHat`, but for the genuine
Montel chart cover.  Unlike the single-chart closed-core prototype, the PoU sums to `1` on all of `X`,
so the chart-read identities have no core restriction. -/

/-- The complex-valued genuine-cover PoU function `ρ_a : X → ℂ`. -/
noncomputable def genuineRhoC (a : Fin ((chartCover : Finset X).card)) : X → ℂ :=
  fun x => ((genuineCoverPoU (X := X) a x : ℝ) : ℂ)

/-- The genuine-cover PoU functions sum to `1`, as complex-valued functions. -/
theorem sum_genuineRhoC_eq_one (x : X) :
    ∑ a, genuineRhoC (X := X) a x = 1 := by
  have h := sum_genuineCoverPoU_eq_one (X := X) x
  change (∑ a, ((genuineCoverPoU (X := X) a x : ℝ) : ℂ)) = 1
  rw [← Complex.ofReal_sum]
  exact_mod_cast h

/-- The chart-read PoU function in the chart indexed by `c`: `ρ̂_a = ρ_a ∘ φ_c.symm`. -/
noncomputable def genuineRhoHat (c a : Fin ((chartCover : Finset X).card)) : ℂ → ℂ :=
  genuineRhoC (X := X) a ∘ (chartAt (H := ℂ) (coverCenter c)).symm

/-- The planar `∂̄` of the chart-read genuine-cover PoU function. -/
noncomputable def genuineDRhoHat (c a : Fin ((chartCover : Finset X).card)) : ℂ → ℂ :=
  DbarDisk.dbar (genuineRhoHat (X := X) c a)

/-- `ρ̂_a` is real-smooth at every point of the chart target. -/
theorem contDiffAt_genuineRhoHat (c a : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (coverCenter c)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (genuineRhoHat (X := X) c a) z := by
  set φ := chartAt (H := ℂ) (coverCenter c) with hφ
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := coverCenter c) _ hz).contMDiffAt
      (φ.open_target.mem_nhds hz)
  have hρ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun w : ℂ => genuineCoverPoU (X := X) a (φ.symm w)) z :=
    (contMDiff_genuineCoverPoU (X := X) a).contMDiffAt.comp z hsymm
  have hcomplex : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun w : ℂ => ((genuineCoverPoU (X := X) a (φ.symm w) : ℝ) : ℂ)) z :=
    ofRealCM.contMDiff.contMDiffAt.comp z hρ
  exact contMDiffAt_iff_contDiffAt.1 (by
    simpa only [genuineRhoHat, genuineRhoC, Function.comp_apply, hφ] using hcomplex)

/-- In every chart, the chart-read genuine-cover PoU functions sum to `1`. -/
theorem sum_genuineRhoHat_eq_one (c : Fin ((chartCover : Finset X).card)) (z : ℂ) :
    ∑ a, genuineRhoHat (X := X) c a z = 1 := by
  simpa only [genuineRhoHat, Function.comp_apply] using
    sum_genuineRhoC_eq_one (X := X) ((chartAt (H := ℂ) (coverCenter c)).symm z)

/-- In every chart target, the chart-read planar `∂̄`s of the genuine-cover PoU functions sum to `0`. -/
theorem sum_genuineDRhoHat_eq_zero (c : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (coverCenter c)).target) :
    ∑ a, genuineDRhoHat (X := X) c a z = 0 := by
  have hdiff : ∀ a ∈ (Finset.univ : Finset (Fin ((chartCover : Finset X).card))),
      DifferentiableAt ℝ (genuineRhoHat (X := X) c a) z := fun a _ =>
    (contDiffAt_genuineRhoHat (X := X) c a hz).differentiableAt (by simp)
  have hsum : DbarDisk.dbar (fun w => ∑ a, genuineRhoHat (X := X) c a w) z =
      ∑ a, genuineDRhoHat (X := X) c a z := by
    rw [dbarFun_finset_sum Finset.univ (fun a => genuineRhoHat (X := X) c a) hdiff]
    rfl
  have hconst : DbarDisk.dbar (fun w => ∑ a, genuineRhoHat (X := X) c a w) z = 0 := by
    have heq : (fun w => ∑ a, genuineRhoHat (X := X) c a w) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) :=
      Filter.Eventually.of_forall (sum_genuineRhoHat_eq_one (X := X) c)
    rw [DbarDisk.dbar, heq.fderiv_eq]
    simp
  rw [← hsum, hconst]

/-- `ρ_a x = 0` for `x ∉ tsupport ρ_a` (the real PoU function vanishes there). -/
theorem genuineRhoC_eq_zero_of_notMem (a : Fin ((chartCover : Finset X).card)) {x : X}
    (hx : x ∉ tsupport (genuineCoverPoU (X := X) a)) : genuineRhoC (X := X) a x = 0 := by
  simp only [genuineRhoC, image_eq_zero_of_notMem_tsupport hx]
  rfl

/-- In chart `c`, `ρ̂_a z = 0` whenever the chart preimage is outside `tsupport ρ_a`. -/
theorem genuineRhoHat_eq_zero_of_notMem_tsupport
    (c a : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hzρ : (chartAt (H := ℂ) (coverCenter c)).symm z ∉ tsupport (genuineCoverPoU (X := X) a)) :
    genuineRhoHat (X := X) c a z = 0 := by
  simpa only [genuineRhoHat, Function.comp_apply] using
    genuineRhoC_eq_zero_of_notMem (X := X) a hzρ

/-- In chart `c`, `∂̄ρ̂_a z = 0` whenever `z` lies in the chart target and the chart preimage is outside
`tsupport ρ_a`. -/
theorem genuineDRhoHat_eq_zero_of_notMem_tsupport
    (c a : Fin ((chartCover : Finset X).card)) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (coverCenter c)).target)
    (hzρ : (chartAt (H := ℂ) (coverCenter c)).symm z ∉ tsupport (genuineCoverPoU (X := X) a)) :
    genuineDRhoHat (X := X) c a z = 0 := by
  set φ := chartAt (H := ℂ) (coverCenter c) with hφ
  show DbarDisk.dbar (genuineRhoHat (X := X) c a) z = 0
  have hcont : ContinuousAt φ.symm z := φ.continuousAt_symm hz
  have hzero : genuineRhoHat (X := X) c a =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hcont.preimage_mem_nhds
        ((isClosed_tsupport (genuineCoverPoU (X := X) a)).isOpen_compl.mem_nhds hzρ)] with w hw
    exact genuineRhoHat_eq_zero_of_notMem_tsupport (X := X) c a (by simpa only [hφ] using hw)
  rw [DbarDisk.dbar, hzero.fderiv_eq]
  simp

end Jacobians.Dolbeault
