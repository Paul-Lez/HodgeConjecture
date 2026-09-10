/-
  Dolbeault ladder — the **closed-core** partition-of-unity primitives for the disk-acyclicity.

  THE SOUNDNESS POINT.  A `SharedChartCover` is a finite *family* of opens living in one chart
  (NOT a cover of compact `X` — a single chart cannot cover a compact connected surface).  The
  disk-acyclicity globalizes a cocycle with a smooth partition of unity `ρ` SUBORDINATE to the family
  `(Uᵢ)`.  A subordinate PoU canNOT sum to `1` on the open `⋃ Uᵢ` (that forces `⋃ Uᵢ` clopen, hence
  `= X` on connected `X` — exactly the vacuity that made the old `extends FiniteCover` design empty).

  THE FIX (this file).  Sum to `1` only on a **closed core** `C ⊆ ⋃ Uᵢ`.  Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate` takes a *closed* `s ⊆ ⋃ Uᵢ`; with `s := C` it gives a
  subordinate PoU summing to `1` on `C` — sound, no clopen issue.  Since every pairwise overlap of a
  `SharedChartCover` lies in `interior C`, the cocycle germ-splitting (consumed only at overlap points)
  happens exactly where `∑ ρ = 1` on a neighbourhood.

  These are the genuinely-reusable NEW lemmas the re-proof extracts: the closed-core subordinate-PoU
  existence and its `∑ ρ = 1`-on-`C` value form, stated abstractly over a finite family `U : ι → Opens X`
  and a closed `C ⊆ ⋃ Uᵢ` (so they are independent of the `SharedChartCover` packaging and reusable for
  any closed-core globalization).  No gaps.
-/
import KirovDolbeault.Dolbeault.CechComplex
import KirovDolbeault.Dolbeault.RealManifold
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [LocallyCompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-! ## The closed-core subordinate partition of unity

A compact `T2` `ℂ`-manifold is a `σ`-compact finite-dimensional real manifold (over `𝓘(ℝ, ℂ)`), so
Mathlib's manifold PoU applies.  We expose the closed-core existence and the sum-on-`C` value form. -/

/-- **Closed-core subordinate PoU exists.**  For a finite family of opens `U : ι → Opens X` and a
CLOSED set `C ⊆ ⋃ i, Uᵢ`, there is a smooth partition of unity over `𝓘(ℝ, ℂ)`, subordinate to `(Uᵢ)`
(`tsupport ρᵢ ⊆ Uᵢ`), summing to `1` on `C`.  This is the sound replacement for the (vacuous on a
single-chart family) `univ`-subordinate PoU: the closed set `C` is the sum-to-one locus, avoiding the
clopen obstruction.  Direct application of `SmoothPartitionOfUnity.exists_isSubordinate` with `s := C`. -/
theorem exists_smoothPartitionOfUnity_core {ι : Type} [Fintype ι] (U : ι → Opens X)
    {C : Set X} (hCclosed : IsClosed C) (hCsub : C ⊆ ⋃ i, (U i : Set X)) :
    ∃ ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X C,
      ρ.IsSubordinate (fun i => (U i : Set X)) :=
  SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) hCclosed
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) hCsub

/-- **Open-union subordinate PoU exists.**  On the open submanifold given by the union of the family,
the closed set is `univ`, so the partition of unity sums to `1` everywhere there.  This is the sound
rebase for the globalization step the comments point at. -/
theorem exists_smoothPartitionOfUnity_openUnion {ι : Type} [Fintype ι] [SecondCountableTopology X]
    (U : ι → Opens X) :
    ∃ ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ)
      ↥(⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩ : Opens X)
      (Set.univ : Set ↥(⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩ : Opens X)),
      ρ.IsSubordinate (fun i => {x : ↥(⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩ : Opens X) | (x : X) ∈ U i}) := by
  classical
  let Y : Opens X := ⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩
  haveI : LocallyCompactSpace ↥Y := Y.2.locallyCompactSpace
  haveI : SecondCountableTopology ↥Y := inferInstance
  have hopen : ∀ i, IsOpen ({x : ↥Y | (x : X) ∈ U i} : Set ↥Y) := by
    intro i
    simpa [Set.preimage] using
      (isOpen_induced_iff.mpr ⟨(U i : Set X), (U i).isOpen, rfl⟩ :
        IsOpen ({x : ↥Y | (x : X) ∈ U i}))
  have hcov : (Set.univ : Set ↥Y) ⊆ ⋃ i, {x : ↥Y | (x : X) ∈ U i} := by
    intro x hx
    rcases Set.mem_iUnion.mp x.property with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hpoU :
      ∃ ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ↥Y (Set.univ : Set ↥Y),
        ρ.IsSubordinate (fun i => {x : ↥Y | (x : X) ∈ U i}) :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
      (s := (Set.univ : Set ↥Y)) isClosed_univ
      (fun i => {x : ↥Y | (x : X) ∈ U i}) hopen hcov
  simpa [Y] using hpoU

/-- The chosen smooth partition of unity on the open union of a finite family. -/
noncomputable def openUnionPoU {ι : Type} [Fintype ι] [SecondCountableTopology X] (U : ι → Opens X) :
    SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ)
      ↥(⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩ : Opens X)
      (Set.univ : Set ↥(⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩ : Opens X)) :=
  (exists_smoothPartitionOfUnity_openUnion U).choose

theorem openUnionPoU_subordinate {ι : Type} [Fintype ι] [SecondCountableTopology X] (U : ι → Opens X) :
    (openUnionPoU (X := X) U).IsSubordinate
      (fun i => {x : ↥(⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩ : Opens X) | (x : X) ∈ U i}) :=
  (exists_smoothPartitionOfUnity_openUnion U).choose_spec

/-- The open-union partition of unity sums to one at every point of the union. -/
theorem openUnionPoU_sum_eq_one {ι : Type} [Fintype ι] (U : ι → Opens X)
    [SecondCountableTopology X]
    {x : ↥(⟨⋃ i, (U i : Set X), isOpen_iUnion fun i => (U i).isOpen⟩ : Opens X)} :
    ∑ i, openUnionPoU (X := X) U i x = 1 := by
  rw [← finsum_eq_sum_of_fintype]
  exact (openUnionPoU (X := X) U).sum_eq_one (by simp)

/-- **Sum-to-one on the core**, value form: a PoU over the closed set `C` sums to `1` at every point of
`C`.  (Repackages Mathlib's `SmoothPartitionOfUnity.sum_eq_one` with the `finsum = Finset.sum` collapse
for the `Fintype` index.) -/
theorem smoothPartitionOfUnity_sum_eq_one_of_mem {ι : Type} [Fintype ι] {C : Set X}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X C) {x : X} (hx : x ∈ C) :
    ∑ i, ρ i x = 1 := by
  rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one hx

end Jacobians.Dolbeault
