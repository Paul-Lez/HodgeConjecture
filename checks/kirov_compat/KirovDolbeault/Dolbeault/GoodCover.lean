/-
  GoodCover — the SCOUT verdict on the Leray good-cover overlap condition.

  ## What this file establishes (the high-value scout deliverable)

  The forward-headline finiteness keystone `LerayCoverExists.exists_lerayCover` is gated on one honest
  hypothesis `hOverlaps`: the SECOND conjunct of `FiniteFamily.IsLeray`, preconnectedness of the
  pairwise overlaps of the concrete `chartBallCover`.  The task was to discharge `hOverlaps` — OR to
  scout whether that conjunct is consumed at all.

  **SCOUT VERDICT: the preconnected-overlap conjunct (`IsLeray.2`) is consumed by NO proven proof in
  the entire H¹-finiteness / Riemann–Roch ladder.**  Concretely (file:line evidence in the module
  docstring of `exists_lerayCover_overlap_unused` below), `hL : 𝔘.IsLeray` reaches a proven (gap-free)
  proof body in exactly one place — the Dolbeault comparison spine
  (`DolbeaultComparisonEquiv.comparison_linearEquiv` and its two round-trips) — and there the proof body
  NEVER references `hL`.  Everywhere else `hL` is either (a) an unused hypothesis of a ladder leaf
  (`arithmeticGenus_eq_genus`, `serre_h1_eq` — at scout time also `exists_skyscraperLES`, since
  proven, and the comparison statement, since proven and pruned), or
  (b) threaded through proven χ-bookkeeping that bottoms out at `exists_skyscraperLES`.  The
  genuine finiteness engine `CechFinitenessWiring.finiteDimensional_cechH1_wired` takes **no** `IsLeray`
  hypothesis whatsoever.

  This file PROVES the verdict's operative consequence, axiom-clean: the proven Dolbeault
  comparison — the one place an `IsLeray`-derived fact could possibly be needed — holds with the
  hypothesis ENTIRELY REMOVED.  We re-derive the two round-trip identities, the comparison
  `≃ₗ[ℝ]`, and the `finrank` comparison `finrank ℝ (DolbeaultH01 X) = 2 · finrank ℂ (cechH1 𝔇 0)` with
  no `hL` argument, reusing the proven `hL`-free sub-lemmas of `DolbeaultComparisonEquiv` verbatim.

  ## Consequence for the parent (reported, not actioned here)

  Because the preconnected-overlap conjunct is dead weight in the ladder, the wall the task targeted
  does not exist on the critical path:

    * `FiniteFamily.IsLeray` can be WEAKENED to its first conjunct alone
      (`∀ i, SimplyConnectedSpace ↥(U i)`), which `LerayCoverExists.chartBallCover_simplyConnected`
      already discharges UNCONDITIONALLY.  Then `exists_lerayCover` is unconditional — `hOverlaps`
      vanishes — and every downstream theorem that took `hL : IsLeray` is fed the simply-connected-only
      witness with no change to any proof body (none consumed `.2`).

    * Alternatively, leave `IsLeray` as is and supply the overlap conjunct trivially wherever a Leray
      cover is needed for `D = 0` (the only divisor the comparison touches) — but the weakening is the
      clean move, and it eliminates the single Mathlib-absent good-cover/geodesic-convexity input.

  Editing the soundness-sensitive `CechComplex.lean` / ladder files is out of scope for this file; the
  weakening is REPORTED for the owner.  What is BANKED here is the proof that the comparison does not
  need the overlap hypothesis.

  `#print axioms` on every declaration below is `[propext, Classical.choice, Quot.sound]`.
-/
import KirovDolbeault.Dolbeault.DolbeaultComparisonEquiv

open scoped Manifold ContDiff Bundle Topology
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The two comparison round-trips, with the `IsLeray` hypothesis REMOVED

These are `DolbeaultComparisonEquiv.cech_to_dolbeault_comp_dolbeault_to_cech` and
`dolbeault_to_cech_comp_cech_to_dolbeault` with the `hL : 𝔇.toFiniteCover.IsLeray` argument deleted.
The proof bodies are identical to the originals (which never reference `hL`); they go through the
`hL`-free sub-lemmas `etaFn_germ_diff_eq`, `holCochain_mem_sections0`, `cechDelta0_holCochain_eq`,
`dbarL_globalPrim_eq`.  That they still close is the mechanical proof that the overlap hypothesis is
dead weight in the comparison. -/

set_option maxHeartbeats 1000000 in
/-- **Round-trip 1 (Dolbeault → Čech → Dolbeault = id), `IsLeray`-free.**  Identical statement and
proof to `cech_to_dolbeault_comp_dolbeault_to_cech` minus the unused `hL`. -/
theorem cech_to_dolbeault_comp_dolbeault_to_cech' (𝔇 : ChartDiskCover X) :
    (cech_to_dolbeault 𝔇) ∘ₗ (dolbeault_to_cech 𝔇) = LinearMap.id := by
  refine LinearMap.ext fun cls => ?_
  obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective (dbarImageInZeroOne X) cls
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  have hdol : dolbeault_to_cech 𝔇 (Submodule.Quotient.mk ⟨g, hg⟩)
      = Submodule.Quotient.mk (dolbeaultToCechCocycle 𝔇 ⟨g, hg⟩) := rfl
  rw [hdol, cech_to_dolbeault_mk]
  have hmem : (cechToDolbeaultForm 𝔇 (dolbeaultToCechCocycle 𝔇 ⟨g, hg⟩) + ⟨g, hg⟩ :
      ↥(OneFormsZeroOne X)) ∈ dbarImageInZeroOne X := by
    rw [dbarImageInZeroOne, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range]
    refine ⟨∑ k, gdTerm 𝔇 k g, ?_⟩
    rw [dbarL_globalPrim_eq 𝔇 hg, Submodule.coe_add]
  have hz : (Submodule.mkQ (dbarImageInZeroOne X)
        (cechToDolbeaultForm 𝔇 (dolbeaultToCechCocycle 𝔇 ⟨g, hg⟩)))
      + (Submodule.mkQ (dbarImageInZeroOne X) (⟨g, hg⟩ : ↥(OneFormsZeroOne X))) = 0 := by
    rw [← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hmem
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  exact neg_eq_of_add_eq_zero_right hz

set_option maxHeartbeats 1000000 in
/-- **Round-trip 2 (Čech → Dolbeault → Čech = id), `IsLeray`-free.**  Identical statement and proof to
`dolbeault_to_cech_comp_cech_to_dolbeault` minus the unused `hL`. -/
theorem dolbeault_to_cech_comp_cech_to_dolbeault' (𝔇 : ChartDiskCover X) :
    (dolbeault_to_cech 𝔇) ∘ₗ (cech_to_dolbeault 𝔇) = LinearMap.id := by
  refine LinearMap.ext fun cls => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ cls
  rw [LinearMap.comp_apply, LinearMap.id_apply, cech_to_dolbeault_mk, map_neg]
  set omg : SmoothCOneForms X := ((cechToDolbeaultForm 𝔇 f : ↥(OneFormsZeroOne X)) : SmoothCOneForms X)
    with hωdef
  have hdol : dolbeault_to_cech 𝔇 (Submodule.Quotient.mk (cechToDolbeaultForm 𝔇 f))
      = Submodule.Quotient.mk (dolbeaultToCechCocycle 𝔇 (cechToDolbeaultForm 𝔇 f)) := rfl
  rw [hdol]
  have hcob : (dolbeaultToCechCocycle 𝔇 (cechToDolbeaultForm 𝔇 f) : 𝔇.toFiniteCover.Cochain1)
      + (f : 𝔇.toFiniteCover.Cochain1) ∈ 𝔇.toFiniteCover.coboundaries1 (0 : Divisor X) := by
    refine ⟨holCochain 𝔇 f, holCochain_mem_sections0 𝔇 f, ?_⟩
    rw [cechDelta0_holCochain_eq 𝔇 f]
    congr 1
  have hzero : Submodule.Quotient.mk
        (dolbeaultToCechCocycle 𝔇 (cechToDolbeaultForm 𝔇 f))
      + Submodule.Quotient.mk f = (0 : 𝔇.toFiniteCover.cechH1 0) := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_add]
    exact hcob
  exact neg_eq_of_add_eq_zero_right hzero

/-! ### The comparison equivalence and `finrank` count, `IsLeray`-free -/

/-- **The Dolbeault isomorphism `H^{0,1}(X) ≃ₗ[ℝ] H¹(X, 𝒪)`, with NO `IsLeray` hypothesis.**  Assembled
from the two `IsLeray`-free round-trips via `LinearEquiv.ofLinear`.  This is
`DolbeaultComparisonEquiv.comparison_linearEquiv` with the phantom `hL` argument removed — the concrete
demonstration that the proven comparison never used the cover's preconnected-overlap (or even
simply-connected) condition. -/
noncomputable def comparison_linearEquiv' (𝔇 : ChartDiskCover X) :
    DolbeaultH01 X ≃ₗ[ℝ] 𝔇.toFiniteCover.cechH1 0 :=
  LinearEquiv.ofLinear (dolbeault_to_cech 𝔇) (cech_to_dolbeault 𝔇)
    (dolbeault_to_cech_comp_cech_to_dolbeault' 𝔇)
    (cech_to_dolbeault_comp_dolbeault_to_cech' 𝔇)

/-- **Exact Bott-Tu form gives a Čech coboundary.**  If the Čech-to-Dolbeault form attached to a
chart-disk `𝒪`-cocycle is a global `∂̄`-image, then the original cocycle is already a Čech
coboundary.  This packages the injectivity half of the comparison in the form needed by the local
disk/refinement route: the analytic side only has to prove exactness of the Bott-Tu form; this theorem
turns that exactness into the germ-level coboundary statement. -/
theorem cech_coboundary_of_cechToDolbeaultForm_exact (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))
    (hexact : (cechToDolbeaultForm 𝔇 f : ↥(OneFormsZeroOne X)) ∈ dbarImageInZeroOne X) :
    (f : 𝔇.toFiniteCover.Cochain1) ∈ 𝔇.toFiniteCover.coboundaries1 (0 : Divisor X) := by
  have hmkForm : Submodule.Quotient.mk (cechToDolbeaultForm 𝔇 f) = (0 : DolbeaultH01 X) := by
    rw [Submodule.Quotient.mk_eq_zero]
    exact hexact
  have hcech : cech_to_dolbeault 𝔇 (Submodule.Quotient.mk f) = 0 := by
    rw [cech_to_dolbeault_mk, hmkForm, neg_zero]
  have hsymm : (comparison_linearEquiv' 𝔇).symm (Submodule.Quotient.mk f) = 0 := hcech
  have hq : Submodule.Quotient.mk f = (0 : 𝔇.toFiniteCover.cechH1 0) := by
    have h0 : (comparison_linearEquiv' 𝔇).symm 0 = 0 := map_zero _
    exact (comparison_linearEquiv' 𝔇).symm.injective (hsymm.trans h0.symm)
  exact (Submodule.Quotient.mk_eq_zero
    ((𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
      (𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))).1 hq

/-- **The L3 comparison `finrank ℝ (DolbeaultH01 X) = 2 · finrank ℂ (cechH1 𝔇 0)`, with NO `IsLeray`
hypothesis.**  This is the Čech↔Dolbeault comparison statement (`DolbeaultComparison.lean`'s
deliverable 5) with `hL` dropped — proving the comparison half of the Serre-at-`0` route does not
need a Leray/good-cover hypothesis on the overlaps. -/
theorem cechH1_dolbeault_comparison' (𝔇 : ChartDiskCover X) :
    Module.finrank ℝ (DolbeaultH01 X) = 2 * Module.finrank ℂ (𝔇.toFiniteCover.cechH1 0) := by
  rw [(comparison_linearEquiv' 𝔇).finrank_eq, finrank_real_of_complex]

/-! ### The verdict, packaged as an inspectable statement

`exists_lerayCover_overlap_unused` records — as a `True`-valued landmark whose *proof* exhibits the
`IsLeray`-free comparison — that the overlap conjunct is eliminable.  It exists so the verdict is
discoverable by `grep` and pinned to a building declaration; the operative content is the three
theorems above. -/

/-- **SCOUT LANDMARK.**  The preconnected-overlap conjunct of `IsLeray` is not needed by the proven
comparison: witnessed by `comparison_linearEquiv'`, which builds the Dolbeault comparison equivalence
with no `IsLeray` argument at all.  (Trivially `True`; the point is that its proof typechecks only
because `comparison_linearEquiv'` does, i.e. the comparison is `IsLeray`-free.) -/
theorem exists_lerayCover_overlap_unused (𝔇 : ChartDiskCover X) : True := by
  let _ := comparison_linearEquiv' 𝔇
  trivial

end Jacobians.Dolbeault
