import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.Separation.Regular
import Mathlib.Analysis.Complex.Basic

/-!
# Montel path — finite chart cover + compact shrinking

Foundational pieces for the Montel/Ahlfors-Sario construction:

- `exists_finite_chart_cover` — X compact + `ChartedSpace ℂ X` gives a
  finite subcover of the chart sources.
- `chartCover : Finset X` — a canonical choice, via `Classical.choose`.
- `shrunkChart : X → Set X` — a COMPACT refinement, each ⊆ the chart
  source, still covering X. Built via Mathlib's
  `exists_iUnion_eq_closed_subset` (shrinking lemma on normal spaces;
  NormalSpace is auto from compact T2).

This file is intentionally light on imports — no vector-bundle machinery
— so it compiles quickly and independently. -/

namespace Jacobians.Montel

open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Finite chart cover -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart source at x is open in X. -/
theorem isOpen_chartAt_source (x : X) : IsOpen (chartAt ℂ x).source :=
  (chartAt ℂ x).open_source

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Chart sources cover X. -/
theorem iUnion_chartAt_source_eq_univ : (⋃ x : X, (chartAt ℂ x).source) = Set.univ :=
  iUnion_source_chartAt ℂ X

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Compactness of X yields a FINITE set of points whose chart sources cover X. -/
theorem exists_finite_chart_cover :
    ∃ (s : Finset X), (⋃ x ∈ s, (chartAt ℂ x).source) = Set.univ := by
  have hcov : Set.univ ⊆ ⋃ x : X, (chartAt ℂ x).source :=
    (iUnion_chartAt_source_eq_univ (X := X)).symm.le
  have hopen : ∀ x : X, IsOpen (chartAt ℂ x).source := fun x => (chartAt ℂ x).open_source
  obtain ⟨s, hs⟩ :=
    IsCompact.elim_finite_subcover isCompact_univ (fun x : X => (chartAt ℂ x).source)
      hopen hcov
  exact ⟨s, Set.eq_univ_of_univ_subset hs⟩

/-! ### Canonical chart cover + shrinking -/

/-- The canonical finite chart cover of compact X. -/
noncomputable def chartCover : Finset X :=
  Classical.choose (exists_finite_chart_cover (X := X))

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem chartCover_cover :
    (⋃ x ∈ (chartCover : Finset X), (chartAt ℂ x).source) = Set.univ :=
  Classical.choose_spec (exists_finite_chart_cover (X := X))

omit [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
/-- The canonical finite chart cover is non-empty. -/
theorem chartCover_nonempty : ((chartCover : Finset X)).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hx : x₀ ∈ (⋃ x ∈ (chartCover : Finset X), (chartAt ℂ x).source) := by
    rw [chartCover_cover]; trivial
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, _⟩ := hx
  exact ⟨i, hi⟩

open Classical in
/-- Auxiliary open family for the shrinking lemma: chart source at x if
`x ∈ chartCover`, else `∅`. -/
private noncomputable def coverOpen (x : X) : Set X :=
  if x ∈ (chartCover : Finset X) then (chartAt ℂ x).source else ∅

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
private theorem coverOpen_isOpen (x : X) : IsOpen (coverOpen (X := X) x) := by
  unfold coverOpen
  by_cases hx : x ∈ (chartCover : Finset X)
  · rw [if_pos hx]; exact (chartAt ℂ x).open_source
  · rw [if_neg hx]; exact isOpen_empty

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
private theorem iUnion_coverOpen_eq :
    (⋃ x : X, coverOpen (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← chartCover_cover (X := X)]
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x₀, hx₀cover, hx₀src⟩ := hy
  refine Set.mem_iUnion.mpr ⟨x₀, ?_⟩
  unfold coverOpen
  rw [if_pos hx₀cover]
  exact hx₀src

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
private theorem coverOpen_locallyFinite (y : X) :
    {x | y ∈ coverOpen (X := X) x}.Finite := by
  apply Set.Finite.subset ((chartCover : Finset X)).finite_toSet
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  unfold coverOpen at hx
  by_contra hxmem
  rw [if_neg (by simpa [Finset.mem_coe] using hxmem)] at hx
  exact absurd hx (Set.notMem_empty y)

/-! ### Double open-shrinking for outer and inner nested closed covers

We use `exists_subset_iUnion_closure_subset` (normal-space open shrinking
lemma) twice to get a nested open/closed structure:

- `chartOpen x` — open, `closure (chartOpen x) ⊆ coverOpen x`,
  `⋃ chartOpen x = X`.
- `innerChartOpen x` — open, `closure (innerChartOpen x) ⊆ chartOpen x`,
  `⋃ innerChartOpen x = X`.
- `shrunkChart x := closure (chartOpen x)` — closed, `⊆ coverOpen x`,
  covers X.
- `innerShrunkChart x := closure (innerChartOpen x)` — closed,
  `⊆ chartOpen x` (open), covers X.

Key downstream property: `innerShrunkChart x ⊆ chartOpen x ⊆
interior (shrunkChart x)`, giving Arzelà–Ascoli the "wiggle room" it
needs — a uniform `localRep α x₀` bound on outer `shrunkChart x₀`
(from the Montel norm) automatically holds on an open neighborhood of
inner `innerShrunkChart x₀`. -/

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- First-pass open shrinking: for each x, an open set with closure inside
`coverOpen x`, still covering X. -/
private theorem exists_chartOpen :
    ∃ V : X → Set X,
      (Set.univ : Set X) ⊆ ⋃ x, V x ∧
      (∀ x, IsOpen (V x)) ∧
      (∀ x, closure (V x) ⊆ coverOpen (X := X) x) :=
  exists_subset_iUnion_closure_subset isClosed_univ coverOpen_isOpen
    (fun x _ => coverOpen_locallyFinite x)
    (by rw [iUnion_coverOpen_eq])

/-- The outer open family: each `chartOpen x` is open, closure contained in
`coverOpen x = (chartAt ℂ x).source` for `x ∈ chartCover`, and the family
covers X. -/
noncomputable def chartOpen (x : X) : Set X :=
  Classical.choose (exists_chartOpen (X := X)) x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem chartOpen_isOpen (x : X) : IsOpen (chartOpen (X := X) x) :=
  (Classical.choose_spec (exists_chartOpen (X := X))).2.1 x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem closure_chartOpen_subset_coverOpen (x : X) :
    closure (chartOpen (X := X) x) ⊆ coverOpen (X := X) x :=
  (Classical.choose_spec (exists_chartOpen (X := X))).2.2 x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem iUnion_chartOpen_eq : (⋃ x : X, chartOpen (X := X) x) = Set.univ :=
  Set.eq_univ_of_univ_subset (Classical.choose_spec (exists_chartOpen (X := X))).1

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
private theorem chartOpen_locallyFinite (y : X) :
    {x | y ∈ chartOpen (X := X) x}.Finite := by
  apply Set.Finite.subset (coverOpen_locallyFinite (X := X) y)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact closure_chartOpen_subset_coverOpen x (subset_closure hx)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Second-pass open shrinking: for each x, an open set with closure inside
`chartOpen x`, still covering X. -/
private theorem exists_innerChartOpen :
    ∃ W : X → Set X,
      (Set.univ : Set X) ⊆ ⋃ x, W x ∧
      (∀ x, IsOpen (W x)) ∧
      (∀ x, closure (W x) ⊆ chartOpen (X := X) x) :=
  exists_subset_iUnion_closure_subset isClosed_univ chartOpen_isOpen
    (fun x _ => chartOpen_locallyFinite x)
    (by rw [iUnion_chartOpen_eq])

/-- The inner open family: each `innerChartOpen x` is open, closure
contained in the outer `chartOpen x`, still covering X. -/
noncomputable def innerChartOpen (x : X) : Set X :=
  Classical.choose (exists_innerChartOpen (X := X)) x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem innerChartOpen_isOpen (x : X) : IsOpen (innerChartOpen (X := X) x) :=
  (Classical.choose_spec (exists_innerChartOpen (X := X))).2.1 x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem closure_innerChartOpen_subset_chartOpen (x : X) :
    closure (innerChartOpen (X := X) x) ⊆ chartOpen (X := X) x :=
  (Classical.choose_spec (exists_innerChartOpen (X := X))).2.2 x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem iUnion_innerChartOpen_eq : (⋃ x : X, innerChartOpen (X := X) x) = Set.univ :=
  Set.eq_univ_of_univ_subset (Classical.choose_spec (exists_innerChartOpen (X := X))).1

/-! ### Outer closed cover `shrunkChart` (public API — same as before) -/

/-- Outer closed shrinkage: `shrunkChart x := closure (chartOpen x)`. Has
the same API as the previous single-pass shrinkage (closed, ⊆ chart source,
covers X), plus the key extra structure `chartOpen x ⊆ shrunkChart x` with
`chartOpen x` open, which gives `innerShrunkChart x ⊆ chartOpen x ⊆
interior (shrunkChart x)`. -/
noncomputable def shrunkChart (x : X) : Set X :=
  closure (chartOpen (X := X) x)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem shrunkChart_isClosed (x : X) : IsClosed (shrunkChart (X := X) x) :=
  isClosed_closure

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem shrunkChart_isCompact (x : X) : IsCompact (shrunkChart (X := X) x) :=
  (shrunkChart_isClosed x).isCompact

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- `chartOpen x ⊆ shrunkChart x` — the open interior layer inside outer. -/
theorem chartOpen_subset_shrunkChart (x : X) :
    chartOpen (X := X) x ⊆ shrunkChart (X := X) x :=
  subset_closure

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem iUnion_shrunkChart_eq : (⋃ x : X, shrunkChart (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_chartOpen_eq (X := X)]
  exact Set.iUnion_mono (fun x => chartOpen_subset_shrunkChart x)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- `shrunkChart x ⊆ (chartAt ℂ x).source` when `x ∈ chartCover`. -/
theorem shrunkChart_subset_source (x : X) (hx : x ∈ (chartCover : Finset X)) :
    shrunkChart (X := X) x ⊆ (chartAt ℂ x).source := by
  intro y hy
  have h1 : y ∈ coverOpen (X := X) x := closure_chartOpen_subset_coverOpen x hy
  unfold coverOpen at h1
  rw [if_pos hx] at h1
  exact h1

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- For x ∉ chartCover, the shrunkChart is empty. -/
theorem shrunkChart_eq_empty (x : X) (hx : x ∉ (chartCover : Finset X)) :
    shrunkChart (X := X) x = ∅ := by
  have hcO : chartOpen (X := X) x = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have : y ∈ coverOpen (X := X) x :=
      closure_chartOpen_subset_coverOpen x (subset_closure hy)
    unfold coverOpen at this
    rw [if_neg hx] at this
    exact this
  unfold shrunkChart
  rw [hcO, closure_empty]

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Restricted cover: the shrunkCharts indexed by `chartCover` still cover X. -/
theorem iUnion_shrunkChart_chartCover_eq :
    (⋃ x ∈ (chartCover : Finset X), shrunkChart (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_shrunkChart_eq (X := X)]
  intro y hy
  simp only [Set.mem_iUnion] at hy ⊢
  obtain ⟨x, hxy⟩ := hy
  by_cases hxmem : x ∈ (chartCover : Finset X)
  · exact ⟨x, hxmem, hxy⟩
  · exfalso
    rw [shrunkChart_eq_empty x hxmem] at hxy
    exact hxy

/-! ### Inner closed cover `innerShrunkChart`

The inner closed family sits strictly inside `chartOpen x` (open), hence
strictly inside the interior of `shrunkChart x`. This gives Arzelà–Ascoli
the wiggle room it needs for Cauchy-estimate-based equicontinuity. -/

/-- Inner closed shrinkage: `innerShrunkChart x := closure (innerChartOpen x)`.
Strictly inside the outer's open interior layer `chartOpen x`, still
covering X. -/
noncomputable def innerShrunkChart (x : X) : Set X :=
  closure (innerChartOpen (X := X) x)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem innerShrunkChart_isClosed (x : X) : IsClosed (innerShrunkChart (X := X) x) :=
  isClosed_closure

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem innerShrunkChart_isCompact (x : X) : IsCompact (innerShrunkChart (X := X) x) :=
  (innerShrunkChart_isClosed x).isCompact

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The inner closed set sits inside the outer's open interior. -/
theorem innerShrunkChart_subset_chartOpen (x : X) :
    innerShrunkChart (X := X) x ⊆ chartOpen (X := X) x :=
  closure_innerChartOpen_subset_chartOpen x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Key wiggle-room property: inner `⊆` open `⊆` outer. -/
theorem innerShrunkChart_subset_shrunkChart (x : X) :
    innerShrunkChart (X := X) x ⊆ shrunkChart (X := X) x :=
  (innerShrunkChart_subset_chartOpen x).trans (chartOpen_subset_shrunkChart x)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem iUnion_innerShrunkChart_eq : (⋃ x : X, innerShrunkChart (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerChartOpen_eq (X := X)]
  exact Set.iUnion_mono (fun _ => subset_closure)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- For x ∉ chartCover, innerChartOpen is empty (via `chartOpen x = ∅`
and `innerChartOpen ⊆ closure (innerChartOpen) ⊆ chartOpen`). -/
theorem innerChartOpen_eq_empty (x : X) (hx : x ∉ (chartCover : Finset X)) :
    innerChartOpen (X := X) x = ∅ := by
  have h1 : chartOpen (X := X) x = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have : y ∈ coverOpen (X := X) x :=
      closure_chartOpen_subset_coverOpen x (subset_closure hy)
    unfold coverOpen at this
    rw [if_neg hx] at this
    exact this
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have : y ∈ chartOpen (X := X) x :=
    closure_innerChartOpen_subset_chartOpen x (subset_closure hy)
  rw [h1] at this
  exact this

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- For x ∉ chartCover, innerShrunkChart is empty (since innerChartOpen = ∅). -/
theorem innerShrunkChart_eq_empty (x : X) (hx : x ∉ (chartCover : Finset X)) :
    innerShrunkChart (X := X) x = ∅ := by
  unfold innerShrunkChart
  rw [innerChartOpen_eq_empty x hx, closure_empty]

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Restricted cover over chartCover: inner closed sets still cover X. -/
theorem iUnion_innerShrunkChart_chartCover_eq :
    (⋃ x ∈ (chartCover : Finset X), innerShrunkChart (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerShrunkChart_eq (X := X)]
  intro y hy
  simp only [Set.mem_iUnion] at hy ⊢
  obtain ⟨x, hxy⟩ := hy
  by_cases hxmem : x ∈ (chartCover : Finset X)
  · exact ⟨x, hxmem, hxy⟩
  · exfalso
    rw [innerShrunkChart_eq_empty x hxmem] at hxy
    exact hxy

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Restricted cover over chartCover: inner OPEN sets cover X. Useful
for chart-neighborhood arguments (e.g., Path 2 smoothness). -/
theorem iUnion_innerChartOpen_chartCover_eq :
    (⋃ x ∈ (chartCover : Finset X), innerChartOpen (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerChartOpen_eq (X := X)]
  intro y hy
  simp only [Set.mem_iUnion] at hy ⊢
  obtain ⟨x, hxy⟩ := hy
  by_cases hxmem : x ∈ (chartCover : Finset X)
  · exact ⟨x, hxmem, hxy⟩
  · exfalso
    rw [innerChartOpen_eq_empty x hxmem] at hxy
    exact hxy

end Jacobians.Montel
