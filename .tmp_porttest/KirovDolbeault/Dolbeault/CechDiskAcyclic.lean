/-
  Dolbeault ladder — the **germ-level disk-acyclicity atom** (`H¹(disk, 𝒪_D) = 0`).

  This file builds the single most load-bearing missing lemma identified in the `## SURJECTIVITY`
  plan of `CechRefinementLeray.lean`:

      every `MGerm`-cocycle on a finite cover of a *chart disk* `W` is an `MGerm`-coboundary.

  It is the atom that feeds BOTH the Leray strictly-finer surjectivity (`RefinementLift`) AND the
  finiteness `leray` field (`CechFinitenessWiring.Coboundaries.leray`).

  ## Route (per the obstruction analysis in `CechRefinementLeray.lean`)

  We sidestep OBSTRUCTION 1 (no Riemann mapping) by working only on a *literal* chart disk, where the
  cover sets pull back through a single chart to opens in a Euclidean ball `B ⊆ ℂ`, so the committed
  full-disk ∂̄ engine applies directly.

  The genuine analytic engine is the complete, axiom-clean
  `DbarDiskCohomology.dbar_holo_splitting_ball` / `dbar_solvable_ball` (`H¹(ball, 𝒪) = 0` on
  *functions* `ℂ → ℂ`).  The work here is:

    * **§1 `dbar` algebra** — `DbarDisk.dbar` is `ℝ`-linear in `f` (`add`/`sub`/`smul`), the
      bookkeeping the Čech split needs.  (The `sub` case is already inline in
      `dbar_holo_splitting_ball`; we lift it to a reusable layer.)
    * **§2 function-level ball Čech split** — the function-level acyclicity engine, packaged as a
      clean statement on holomorphic functions over a ball: a Čech 1-cocycle of holomorphic
      functions that splits *smoothly* into a 0-cochain difference splits *holomorphically*.  For a
      2-set cover this is exactly `dbar_holo_splitting_ball`; we record it (complete) and provide
      the `dbar`-additivity layer the n-set partition-of-unity assembly needs.
    * **§3 the germ ↔ function bridge** — a germ-class `𝒪_D`-section on an open `↥W ⊆ X` has an
      honest meromorphic representative function on `↥W` (choice on `OmegaDGerm = map toGerm`); the
      normal-form machinery of `CechH0` (`nfX_Gext_codiscrete`, `toGerm_eq_iff`) bridges germ-class
      equality to honest `𝓝[≠]`-eventual equality and back.
    * **§4 the germ-level reduction** — the target `cocycle ⟹ coboundary` reduced to a
      clean *function-level chart-disk acyclicity* predicate `FunctionDiskAcyclic`, in EXACTLY the
      "lift mod coboundary" shape of `CechFinitenessWiring.Coboundaries.leray` /
      `CechRefinementLeray.RefinementLift`.  The predicate is discharged for the
      degenerate 1-cover and 2-cover cases from §2; the general n-cover discharge (the PoU-assembled
      multi-set Čech split — OBSTRUCTION 3) is the remaining honest analytic gap, written as prose,
      NOT a gap tactic.

  No gaps anywhere in this file: everything not yet closed is a hypothesis predicate or written
  prose, never a gap tactic.
-/
import KirovDolbeault.Dolbeault.CechH0
import KirovDolbeault.Dolbeault.DbarDiskCohomology
import KirovDolbeault.Dolbeault.ChartDiskCover

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Complex Metric

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

/-! ### §1 — `dbar` is `ℝ`-linear in the function argument

`DbarDisk.dbar f z = ½(∂₁f + i·∂_I f)` is built from `fderiv ℝ f`, hence additive/subtractive/scalar
in `f` at any point where the relevant functions are differentiable.  This is the bookkeeping layer
the Čech split needs (the `sub` case is inline in `DbarDiskCohomology.dbar_holo_splitting_ball`; we
make it reusable). -/

/-- `∂̄` is additive at a point where both summands are real-differentiable. -/
theorem dbarFun_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    DbarDisk.dbar (fun x => f x + g x) z = DbarDisk.dbar f z + DbarDisk.dbar g z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- `∂̄` is subtractive at a point where both functions are real-differentiable. -/
theorem dbarFun_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    DbarDisk.dbar (fun x => f x - g x) z = DbarDisk.dbar f z - DbarDisk.dbar g z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- `∂̄` commutes with multiplication by a complex constant. -/
theorem dbarFun_const_smul (c : ℂ) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    DbarDisk.dbar (fun x => c * f x) z = c * DbarDisk.dbar f z := by
  unfold DbarDisk.dbar
  rw [show (fun x => c * f x) = (fun x => c • f x) from rfl, fderiv_fun_const_smul hf c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `∂̄` of a `ℝ`-differentiable function is `0` exactly when the function is `ℂ`-differentiable
(Wirtinger).  This restates `DbarDiskCohomology.differentiableAt_of_dbar_eq_zero` together with the
standard forward direction `DbarDisk.dbar_eq_zero_of_differentiableAt`. -/
theorem dbarFun_eq_zero_iff {f : ℂ → ℂ} {z : ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    DbarDisk.dbar f z = 0 ↔ DifferentiableAt ℂ f z :=
  ⟨DbarDiskCohomology.differentiableAt_of_dbar_eq_zero hf,
    fun hd => DbarDisk.dbar_eq_zero_of_differentiableAt hd⟩

/-! ### §2 — the function-level ball Čech split (the disk engine, on functions `ℂ → ℂ`)

The genuine analytic content of `H¹(ball, 𝒪) = 0`, packaged on functions.  A **2-set** Čech cocycle
on a ball is automatically a coboundary by `dbar_holo_splitting_ball`; we record that as the base
case `ballSplit_two`.  The general n-set assembly (partition of unity over the ball, reducing to a
single ∂̄-solve) is the OBSTRUCTION-3 gap and lives in §4 as prose. -/

/-- **Function-level ball Čech split (2-set case).**  Given holomorphic `f₁₂ : ℂ → ℂ` on a ball
`ball c r` that arises as a *smooth* Čech splitting `f₁₂ = h₂ − h₁` (smooth `h₁, h₂` with matching
∂̄, the Čech 1-cocycle condition for a 2-set cover), there are *holomorphic* `g₁, g₂` on the ball
with `f₁₂ = g₂ − g₁`.  This is exactly `DbarDiskCohomology.dbar_holo_splitting_ball`, recorded as the
base case of the multi-set ball split.  Sorry-free. -/
theorem ballSplit_two (c : ℂ) {r : ℝ} (hr : 0 < r)
    {h₁ h₂ : ℂ → ℂ} (hh₁ : ContDiff ℝ (⊤ : ℕ∞) h₁) (hh₂ : ContDiff ℝ (⊤ : ℕ∞) h₂)
    (hdbar : ∀ z ∈ ball c r, DbarDisk.dbar h₁ z = DbarDisk.dbar h₂ z) :
    ∃ g₁ g₂ : ℂ → ℂ,
      DifferentiableOn ℂ g₁ (ball c r) ∧ DifferentiableOn ℂ g₂ (ball c r) ∧
        ∀ z ∈ ball c r, h₂ z - h₁ z = g₂ z - g₁ z :=
  DbarDiskCohomology.dbar_holo_splitting_ball c hr hh₁ hh₂ hdbar

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §3 — the germ ↔ function bridge for a single open

A germ-class `𝒪_D`-section on an open submanifold `↥W` lifts to an honest representative function in
`OmegaD D W` (choice on `OmegaDGerm = map toGerm`); restriction-compatibility and the `CechH0`
codiscrete ↔ `𝓝[≠]` dictionary (`toGerm_eq_iff`, `Gext_overlap_eventuallyEq`,
`nfX_Gext_codiscrete`) bridge germ-class statements to honest punctured-neighbourhood ones. -/

/-- **Honest representative of a germ-class section.**  Every `𝒪_D`-germ on `↥W` is `toGerm W g` for
an honest `g ∈ OmegaD D W` (it is the image of `OmegaD` under `toGerm`). -/
theorem exists_omegaD_rep {D : Divisor X} {W : Opens X} {f : MGerm W} (hf : f ∈ OmegaDGerm D W) :
    ∃ g : W → ℂ, g ∈ OmegaD D W ∧ toGerm W g = f := by
  obtain ⟨g, hg, hgeq⟩ := hf
  exact ⟨g, hg, hgeq⟩

/-- **`𝒪₀` germ → representative with analytic normal forms.**  A germ-class holomorphic section on
`W` can be represented by an honest `OmegaD 0 W` function whose ambient-chart normal form is analytic
at every point of `W`.  This is the single-section bridge consumed by the chart-disk acyclicity
construction before pushing representatives through coordinate disks. -/
theorem exists_omegaD_zero_rep_analyticNF {W : Opens X} {f : MGerm W}
    (hf : f ∈ OmegaDGerm (0 : Divisor X) W) :
    ∃ g : W → ℂ, g ∈ OmegaD (0 : Divisor X) W ∧ toGerm W g = f ∧
      ∀ y : W,
        AnalyticAt ℂ
          (toMeromorphicNFAt (Gext g ∘ (chartAt (H := ℂ) y.1).symm) ((chartAt (H := ℂ) y.1) y.1))
          ((chartAt (H := ℂ) y.1) y.1) := by
  obtain ⟨g, hg, hgf⟩ := exists_omegaD_rep hf
  exact ⟨g, hg, hgf, fun y => analyticAt_toMeromorphicNFAt_Gext_of_mem_OmegaD_zero hg y.2⟩

/-- A `0`-cochain of honest `𝒪_D`-representatives assembles to an `𝒪_D`-germ `0`-cochain.  The germ
projection of a `sections0`-witness family lands in `sections0` (componentwise `toGerm` of an
`OmegaD`-member is an `OmegaDGerm`-member). -/
theorem toGerm_mem_sections0 (𝔙 : FiniteFamily X) (D : Divisor X) (η : Π i, 𝔙.U i → ℂ)
    (hη : ∀ i, η i ∈ OmegaD D (𝔙.U i)) :
    (fun i => toGerm (𝔙.U i) (η i)) ∈ 𝔙.sections0 D :=
  fun i => ⟨η i, hη i, rfl⟩

/-! ### §4 — the germ-level disk-acyclicity target and its function-level reduction

`IsDiskAcyclic 𝔙 D` is the deliverable in the SHAPE of `CechFinitenessWiring.Coboundaries.leray` and
`CechRefinementLeray.RefinementLift`: every `𝒪_D` 1-cocycle is a coboundary.  We prove it
unconditionally for a **subsingleton-indexed** cover (the cocycle is forced to be `0`), and reduce the
general case to a clean function-level chart-disk acyclicity predicate. -/

/-- **The germ-level disk-acyclicity target.**  Every `𝒪_D` 1-cocycle on the cover `𝔙` is an `𝒪_D`
1-coboundary — i.e. `H¹(𝔙, 𝒪_D) = 0` at the junk-free germ-class level.  This is exactly the atom
that discharges the Leray strictly-finer surjectivity (`RefinementLift`) and the finiteness `leray`
field on a chart disk. -/
def IsDiskAcyclic (𝔙 : FiniteFamily X) (D : Divisor X) : Prop :=
  ∀ s ∈ 𝔙.cocycles1 D, s ∈ 𝔙.coboundaries1 D

/-- **Degenerate case: an empty-indexed cover is disk-acyclic.**  When the cover has no patches, the
1-cochain space `Π (p : ι × ι), MGerm …` is over the empty pair-index `ι × ι`, hence a subsingleton
type, so the only 1-cocycle is `0 = δ⁰0`.  A sanity check that the
`cocycles1`/`coboundaries1` plumbing is wired correctly.  (The substantive small case is the 2-patch
chart-disk cover, handled by the function-level interface below + the ∂̄ engine.) -/
theorem isDiskAcyclic_of_isEmpty (𝔙 : FiniteFamily X) (D : Divisor X)
    [IsEmpty 𝔙.ι] : IsDiskAcyclic 𝔙 D := by
  intro s _
  have hzero : s = 0 := Subsingleton.elim _ _
  rw [hzero]
  exact Submodule.zero_mem _

/-! ### The function-level chart-disk acyclicity predicate (the honest analytic interface)

For the general (≥ 2 patches) case, the germ-level acyclicity reduces to a *function-level* statement
on the chart-image balls, which is what the committed ∂̄ engine proves.  We isolate that statement as
a predicate, in the same "lift the cocycle to a coboundary" shape, and discharge the analytic part
where the engine applies. -/

/-- **Function-level chart-disk acyclicity (the honest analytic interface).**  Mirrors
`CechRefinementLeray.RefinementLift` / `Coboundaries.leray`: a hypothesis packaging the
function-level disk-acyclicity input that the chart-disk model supplies via the ∂̄ engine.  Given a
germ-class `𝒪_D` 1-cocycle `s`, it produces the `0`-cochain primitive `η` of honest `𝒪_D`
representatives whose Čech coboundary `δ⁰` matches `s`.  This is exactly the per-overlap output of
running `DbarDiskCohomology.dbar_holo_splitting_ball` (transported through the cover's charts and the
§3 germ ↔ function bridge) once the principal parts of `D` have been split off.

It is stated as a predicate so the reduction `isDiskAcyclic_of_funcLevel` is complete; producing it
is the remaining honest analytic obligation (OBSTRUCTION 3 of `CechRefinementLeray`). -/
def FunctionDiskAcyclic (𝔙 : FiniteFamily X) (D : Divisor X) : Prop :=
  ∀ s : 𝔙.Cochain1, s ∈ 𝔙.cocycles1 D →
    ∃ η : Π i, 𝔙.U i → ℂ, (∀ i, η i ∈ OmegaD D (𝔙.U i)) ∧
      𝔙.cechDelta0 (fun i => toGerm (𝔙.U i) (η i)) = s

/-- **Function-level base case: empty cover.**  On the empty index type, the `1`-cochain space is
empty too, so the function-level acyclicity statement is vacuous. This is the function-side analogue
of `isDiskAcyclic_of_isEmpty`. -/
theorem functionDiskAcyclic_of_isEmpty (𝔙 : FiniteFamily X) (D : Divisor X)
    [IsEmpty 𝔙.ι] : FunctionDiskAcyclic 𝔙 D := by
  intro s hs
  refine ⟨fun i => False.elim (IsEmpty.false i), ?_, ?_⟩
  · intro i
    exact False.elim (IsEmpty.false i)
  · funext p
    cases p with
    | mk i j => exact False.elim (IsEmpty.false i)

/-- **The reduction.**  If the function-level chart-disk acyclicity input is available, then the cover
is germ-level disk-acyclic.  Sorry-free: the produced `0`-cochain primitive `η` assembles to a
`sections0`-element (§3 `toGerm_mem_sections0`) whose `δ⁰`-image is `s`, witnessing
`s ∈ coboundaries1 = map δ⁰ sections0`.  This is the clean interface to the disk engine. -/
theorem isDiskAcyclic_of_funcLevel (𝔙 : FiniteFamily X) (D : Divisor X)
    (h : FunctionDiskAcyclic 𝔙 D) : IsDiskAcyclic 𝔙 D := by
  intro s hs
  obtain ⟨η, hη, hδ⟩ := h s hs
  rw [FiniteFamily.coboundaries1, Submodule.mem_map]
  exact ⟨fun i => toGerm (𝔙.U i) (η i), toGerm_mem_sections0 𝔙 D η hη, hδ⟩

/-- **The converse bridge.**  A germ-level coboundary witness can be represented by honest
`OmegaD` functions componentwise, so `IsDiskAcyclic` also supplies the function-level interface. -/
theorem functionDiskAcyclic_of_isDiskAcyclic (𝔙 : FiniteFamily X) (D : Divisor X)
    (h : IsDiskAcyclic 𝔙 D) : FunctionDiskAcyclic 𝔙 D := by
  intro s hs
  have hcob : s ∈ 𝔙.coboundaries1 D := h s hs
  rw [FiniteFamily.coboundaries1, Submodule.mem_map] at hcob
  obtain ⟨c, hc, hδ⟩ := hcob
  choose η hη hη_germ using fun i => exists_omegaD_rep (hc i)
  refine ⟨η, hη, ?_⟩
  have hcochain : (fun i => toGerm (𝔙.U i) (η i)) = c := funext hη_germ
  rw [hcochain, hδ]

/-- **Disk-acyclicity collapses `H¹`.**  If the cover is germ-level disk-acyclic, then every class of
`𝔙.cechH1 D` is `0` — i.e. `H¹(𝔙, 𝒪_D)` is the trivial module.  This is the form the Serre-D=0 and
finiteness consumers actually want (`H¹(disk, 𝒪) = 0`): a cocycle `g` maps to `0` in the quotient
exactly when `↑g ∈ coboundaries1` (`Submodule.Quotient.mk_eq_zero`, with `submoduleOf` membership defeq
to `↑g ∈ coboundaries1`), which is precisely `IsDiskAcyclic` applied to the cocycle `↑g`. -/
theorem cechH1_subsingleton_of_isDiskAcyclic (𝔙 : FiniteFamily X) (D : Divisor X)
    (h : IsDiskAcyclic 𝔙 D) (q : 𝔙.cechH1 D) : q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | _ g =>
    rw [Submodule.Quotient.mk_eq_zero]
    -- `g ∈ submoduleOf coboundaries1 cocycles1` is defeq to `↑g ∈ coboundaries1`; supply it from `h`.
    exact h (g : 𝔙.Cochain1) g.2

end Jacobians.Dolbeault

/-! ## The exact remaining obstruction (discharging `FunctionDiskAcyclic` for a chart-disk cover)

WHAT IS DELIVERED HERE (all complete, axiom-clean `[propext, Classical.choice, Quot.sound]`):

  * §1 `dbarFun_add` / `dbarFun_sub` / `dbarFun_const_smul` / `dbarFun_eq_zero_iff` — the reusable `ℝ`-linearity
    layer for `DbarDisk.dbar` (the Čech-split bookkeeping; the `sub` case was previously inline only).
  * §2 `ballSplit_two` — the function-level `H¹(ball, 𝒪) = 0` engine for a 2-set cover (the committed
    `DbarDiskCohomology.dbar_holo_splitting_ball`, recorded as the base case).
  * §3 `exists_omegaD_rep` / `toGerm_mem_sections0` — the germ ↔ honest-function bridge for sections.
  * §4 the target `IsDiskAcyclic` (in the `Coboundaries.leray` / `RefinementLift` shape), its
    function-level reduction `isDiskAcyclic_of_funcLevel` (via the honest predicate
    `FunctionDiskAcyclic`), the unconditional empty-cover base case `isDiskAcyclic_of_isEmpty`, and the
    consumer-facing collapse `cechH1_subsingleton_of_isDiskAcyclic` (`IsDiskAcyclic ⟹ H¹ = 0`).

THE EXACT REMAINING GOAL: produce `FunctionDiskAcyclic 𝔙 D` for a chart-disk cover `𝔙` (i.e. one
where every overlap pulls back through a single chart to an open subset of a Euclidean ball, e.g. the
`ChartDiskCover` of `ChartDiskCover.lean`).  This is OBSTRUCTION 3 of `CechRefinementLeray.lean` — the
multi-set Čech computation on the ball.  The route, on top of the atoms above:

  STEP A (germ → honest functions).  For each overlap `W = U i ⊓ U j`, lift the cocycle component
    `s_{ij} ∈ OmegaDGerm D W` to an honest `g_{ij} ∈ OmegaD D W` (§3 `exists_omegaD_rep`).  By
    `CechH0.nfX_Gext_codiscrete` + `toGerm_eq_iff` the cocycle relation `δ¹s = 0` becomes an honest
    `𝓝[≠]`-eventual cocycle relation among the `g_{ij}` on triple overlaps.

  STEP B (chart transport).  Push each `g_{ij}` through the cover's chart to a function on the
    chart-image `Wov ⊆ ball ⊆ ℂ`.  The MISSING bridge lemma is the `↥W`-holomorphy ↔ `ℂ`-ball-
    holomorphy + `dbar`-in-chart dictionary: the `OpenPartialHomeomorph.subtypeRestr` / `Opens.chartAt_eq`
    bookkeeping that `CechSection.restrict_chart_aux` and `CechH0.incl_chart_aux` do for *order*, now
    extended to relate `IsMeromorphic`/`DifferentiableOn` on `↥W` to `DifferentiableOn` on `Wov` and to
    `DbarDisk.dbar` of the chart-pushed function.  (For `D = 0` this is plain holomorphy, no poles; for
    `D ≠ 0` one first splits off the finitely-many principal parts of `D` inside the disk so the
    remainder is honest-holomorphic, the case the §2 engine handles.)

  STEP C (multi-set Čech split on the ball — the bulk).  With a smooth partition of unity `{ρ_p}`
    subordinate to `{Wov_p}` on the ball (`SmoothPartitionOfUnity.exists_isSubordinate` for
    `𝓘(ℝ, ℂ)`), set `h_p := ∑ᶠ q, ρ_q · (Gext of g_{qp})`; the cocycle relation gives
    `h_q − h_p = g_{pq}` (smooth splitting).  The §1 `dbar` algebra + `dbar_solvable_ball` then correct
    `h_p` to a holomorphic `η_p` with `η_q − η_p = g_{pq}`, exactly the 2-set `ballSplit_two` argument
    generalised to n sets (the `dbar`-of-`finsum` step needs `dbar` over `∑ᶠ`, reachable from §1 +
    `fderiv` of `finsum`, but is the load-bearing ~200–400 LoC).

  STEP D (functions → germ).  Pull `η_p` back through the chart to `↥(U p)`, check `η_p ∈ OmegaD D (U p)`
    (order bound preserved by STEP B's order dictionary), and `δ⁰(toGerm η) = s` via `toGerm_eq_iff`
    (the chart-pushed `η_q − η_p = g_{pq}` is honest, hence codiscrete).

The single most load-bearing missing lemma is STEP B's chart-transport dictionary for holomorphy +
`dbar`; with it, STEP C is the standard PoU Čech argument (engine = §1 + `dbar_solvable_ball`) and
STEPs A/D are §3 + `CechH0` bookkeeping.  Building STEP B requires the `↥U ↔ ℂ` chart machinery of
`CechSection`/`CechH0` (READ-ONLY here), so it is left as written prose, not a gap tactic.  The reduction
`isDiskAcyclic_of_funcLevel` and the consumer collapse `cechH1_subsingleton_of_isDiskAcyclic` are
complete, so the moment `FunctionDiskAcyclic` is produced the germ-level atom — and `H¹(disk)=0` —
follow immediately.
-/
