import Other.AlgebraicGeometry.ExplicitEllipticSurfaceOneForms
import Other.AlgebraicGeometry.AnalyticNestedTransitionClass

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

noncomputable section

abbrev surfaceFstCechOpen (i : Fin 2) :
    Opens (TopCat.of (ComplexPoint (Over.mk surfaceToBase))) :=
  surfaceAnalyticOpen
    (pullback.fst curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex i))

abbrev surfaceSndCechOpen (i : Fin 2) :
    Opens (TopCat.of (ComplexPoint (Over.mk surfaceToBase))) :=
  surfaceAnalyticOpen
    (pullback.snd curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex i))

theorem surfaceFstCechOpen_cover :
    surfaceFstCechOpen 0 ⊔ surfaceFstCechOpen 1 = ⊤ := by
  apply top_unique
  intro z _
  have hc (x : curve) : x ∈ chart 2 ∨ x ∈ chart 1 := by
    have hx : x ∈ chart 1 ⊔ chart 2 := by
      rw [chart_one_sup_chart_two]
      trivial
    exact hx.elim Or.inr Or.inl
  rcases hc (pullback.fst curveToBase curveToBase z.underlying) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem surfaceSndCechOpen_cover :
    surfaceSndCechOpen 0 ⊔ surfaceSndCechOpen 1 = ⊤ := by
  apply top_unique
  intro z _
  have hc (x : curve) : x ∈ chart 2 ∨ x ∈ chart 1 := by
    have hx : x ∈ chart 1 ⊔ chart 2 := by
      rw [chart_one_sup_chart_two]
      trivial
    exact hx.elim Or.inr Or.inl
  rcases hc (pullback.snd curveToBase curveToBase z.underlying) with h | h
  · exact Or.inl h
  · exact Or.inr h

abbrev surfaceCechOuterOverlap := surfaceFstCechOpen 0 ⊓ surfaceFstCechOpen 1

abbrev surfaceCechInnerOpen (i : Fin 2) :=
  surfaceCechOuterOverlap ⊓ surfaceSndCechOpen i

theorem surfaceCechInnerOpen_cover :
    surfaceCechInnerOpen 0 ⊔ surfaceCechInnerOpen 1 =
      surfaceCechOuterOverlap := by
  change (surfaceCechOuterOverlap ⊓ surfaceSndCechOpen 0) ⊔
      (surfaceCechOuterOverlap ⊓ surfaceSndCechOpen 1) =
    surfaceCechOuterOverlap
  rw [← inf_sup_left, surfaceSndCechOpen_cover]
  simp

example : surfaceDifferentialOpen (0, 0) =
    (pullback.fst curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex 0)) ⊓
    (pullback.snd curveToBase curveToBase ⁻¹ᵁ chart (differentialChartIndex 0)) := rfl

end
end AlgebraicGeometry.ExplicitEllipticCandidate
