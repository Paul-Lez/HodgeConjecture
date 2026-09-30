/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingNormalChartClass
public import Other.AlgebraicGeometry.ChernWindingNormalChartLog

/-!
# The normal coordinate only matters up to a unit

`ChernWinding.windingClass_eq_chartNormalProjectionCoclass` asks that the given function *be* the
normal coordinate of the flattening chart.  That is far more than necessary: since the flattened
support neighbourhood is simply connected, a nowhere vanishing continuous function on the whole
of it (i.e. one that does **not** vanish on the support) has a continuous logarithm there, hence
zero winding class.  So only the *ratio* matters:

`ChernWinding.windingClass_eq_chartNormalProjectionCoclass_of_unit` — if
`g = u · (normal coordinate)` with `u` nowhere vanishing on the whole chart neighbourhood, then
the winding class of `g` is still the normalised normal-chart coclass.

This is what removes the holomorphic implicit function theorem from the remaining obligations: one
does not have to build a chart whose normal coordinate *is* the analytified local equation, only
to know that the local equation generates the ideal of the component near the point, i.e. that it
differs from the normal coordinate of *any* flattening chart by a unit.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial TopologicalSpace AlgebraicTopology.Singular

namespace ChernWinding

variable {M : Type} [TopologicalSpace M] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ))) {S : Set M}
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
  (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

/-- The inclusion of the punctured chart neighbourhood into the chart neighbourhood. -/
def flattenedPuncturedInclusion :
    C(puncturedSpace ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S,
      ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The normal coordinate of the chart, as a nowhere vanishing function on the punctured chart
neighbourhood. -/
def flattenedNormalCoordinate :
    C(puncturedSpace ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S, ℂ) :=
  complexLineCoordinate.comp (topMap (flattenedNormalProjection E e S hS x hx).left)

theorem flattenedNormalCoordinate_apply (w) :
    flattenedNormalCoordinate E e hS x hx w =
      complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w) := rfl

theorem flattenedNormalCoordinate_ne_zero (w) :
    flattenedNormalCoordinate E e hS x hx w ≠ 0 := by
  show complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w) ≠ 0
  exact complexLineCoordinate_ne_zero _

/-- A nowhere vanishing continuous function on the whole chart neighbourhood restricts to one
with vanishing winding class: the neighbourhood is simply connected, so it has a continuous
logarithm. -/
theorem windingClass_comp_inclusion_eq_zero
    (u : C(((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M), ℂ))
    (hu : ∀ y, u y ≠ 0)
    (hu' : ∀ w, (u.comp (flattenedPuncturedInclusion (S := S) E e x hx)) w ≠ 0) :
    windingClass ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S
        (u.comp (flattenedPuncturedInclusion (S := S) E e x hx)) hu' = 0 := by
  obtain ⟨L, hL⟩ := exists_expLift u hu
    ⟨x, mem_flattenedSupportNeighborhood E 1 e x hx⟩
  exact windingRelativeClass_eq_zero_of_exp _ _ (L.comp (flattenedPuncturedInclusion (S := S) E e x hx))
    (fun w => hL _) _

set_option maxHeartbeats 1000000 in
include h0 in
/-- **The winding class only sees the normal coordinate up to a unit.** -/
theorem windingClass_eq_chartNormalProjectionCoclass_of_unit
    (g : C(puncturedSpace
      ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S, ℂ))
    (hg : ∀ y, g y ≠ 0)
    (u : C(((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M), ℂ))
    (hu : ∀ y, u y ≠ 0)
    (hmul : ∀ w, g w = u (flattenedPuncturedInclusion (S := S) E e x hx w) *
      complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w)) :
    windingClass ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S g hg =
      chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx)
        (flattenedSupportNeighborhood_subset_source E 1 e x hx) := by
  have hu' : ∀ w, (u.comp (flattenedPuncturedInclusion (S := S) E e x hx)) w ≠ 0 := fun w => hu _
  have hν := flattenedNormalCoordinate_ne_zero E e hS x hx
  rw [show windingClass ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S g hg =
      windingClass ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S
          (u.comp (flattenedPuncturedInclusion (S := S) E e x hx)) hu' +
        windingClass ((flattenedSupportNeighborhood E 1 e x hx : Opens M) : Set M) S
          (flattenedNormalCoordinate E e hS x hx) hν from
      windingRelativeClass_mul _ _ hmul _ _ _,
    windingClass_comp_inclusion_eq_zero E e x hx u hu hu', zero_add]
  exact windingClass_eq_chartNormalProjectionCoclass E e hS x hx h0 _ hν (fun w => rfl)

end ChernWinding
