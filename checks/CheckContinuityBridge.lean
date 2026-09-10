import Other.AlgebraicGeometry.ExplicitEllipticCharts

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint ComplexProjectiveSpace

noncomputable section

set_option maxHeartbeats 600000

abbrev testCurveSpace2 : Over (Spec (CommRingCat.of ℂ)) := Over.mk curveToBase
abbrev testPlaneSpace2 : Over (Spec (CommRingCat.of ℂ)) :=
  Over.mk (ProjectiveSpace.toBase (Fin 3) base)

def testClosedMap : testCurveSpace2 ⟶ testPlaneSpace2 := Over.homMk curveToPlane rfl

instance : IsClosedImmersion testClosedMap.left :=
  inferInstanceAs (IsClosedImmersion curveToPlane)

lemma test_vectorToComplexPoint_proof_irrel {n : ℕ} (v : CoordinateSpace n)
    (h h' : v ≠ 0) : vectorToComplexPoint v h = vectorToComplexPoint v h' := by
  rw [Subsingleton.elim h h']

lemma continuous_of_testClosedMap_comp {T : Type*} [TopologicalSpace T]
    (f : T → ComplexPoint testCurveSpace2)
    (h : @Continuous T (ComplexPoint testPlaneSpace2) inferInstance Point.analyticTopology
      (Point.map testClosedMap ∘ f)) :
    @Continuous T (ComplexPoint testCurveSpace2) inferInstance Point.analyticTopology f := by
  exact (@IsInducing.continuous_iff T (ComplexPoint testCurveSpace2)
    (ComplexPoint testPlaneSpace2) f (Point.map testClosedMap) Point.analyticTopology
    inferInstance Point.analyticTopology (isInducing_map_of_closedImmersion testClosedMap)).mpr h

set_option backward.isDefEq.respectTransparency.types false in
lemma test_map_curvePoint (P : Fin 3 → ℂ) (hP : P ≠ 0)
    (heq : equation.toProjective.Equation P) :
    Point.map testClosedMap (curvePoint P hP heq) = vectorToComplexPoint P hP := by
  simpa only [testClosedMap] using curvePoint_map_vectorToComplexPoint P hP heq

lemma test_continuous_curvePoint_family {T : Type*} [TopologicalSpace T]
    (P : T → Fin 3 → ℂ) (hP : ∀ t, P t ≠ 0)
    (heq : ∀ t, equation.toProjective.Equation (P t))
    (hcontinuous : Continuous P) :
    @Continuous T (ComplexPoint testCurveSpace2) inferInstance Point.analyticTopology
      (fun t ↦ curvePoint (P t) (hP t) (heq t)) := by
  apply continuous_of_testClosedMap_comp
  rw [show (Point.map testClosedMap ∘ fun t ↦ curvePoint (P t) (hP t) (heq t)) =
      fun t ↦ vectorToComplexPoint (P t) (hP t) by
    funext t
    exact test_map_curvePoint _ _ _]
  change @Continuous T
    (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin 3) (Spec (CommRingCat.of ℂ)))))
    inferInstance Point.analyticTopology (fun t ↦ vectorToComplexPoint (P t) (hP t))
  have hv : Continuous (fun t ↦ (⟨P t, hP t⟩ : {v : Fin 3 → ℂ // v ≠ 0})) :=
    hcontinuous.subtype_mk hP
  have hc := continuous_vectorToComplexPoint.comp hv
  exact hc.congr fun t ↦ test_vectorToComplexPoint_proof_irrel _ _ _

end
end AlgebraicGeometry.ExplicitEllipticCandidate
