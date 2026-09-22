/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneTripleTransition
public import HodgeConjecture.Lemmas.AlgebraicTopology.LinearDualQuasiIso
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationParacompact
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationHausdorff

/-!
# The coordinate cocycle in the rational cover complex of `ℙ²`

The first part of this file identifies the named principal opens used in the coordinate
calculation with the literal intersections of the three-open analytic cover.  These are the
geometric identifications needed to insert the explicit winding cochains into the rational
Čech--singular total complex.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial AlgebraicGeometry AlgebraicTopology
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "analyticPlaneTop" => (TopCat.of (ComplexPoint analyticPlane))

lemma projectiveCover_pair01_intersection :
    AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1} : Finset (Fin 3)) = Point.overOpen (X := analyticPlane) pair01Open := by
  ext z
  change z ∈ (⋂ i ∈ ({0, 1} : Finset (Fin 3)), projectiveCover i) ↔ _
  simp only [Set.mem_iInter]
  change (∀ i ∈ ({0, 1} : Finset (Fin 3)),
      z.underlying ∈ chartOpen i) ↔ z.underlying ∈ pair01Open
  rw [show pair01Open = chartOpen 0 ⊓ chartOpen 1 by
    exact Proj.basicOpen_mul Grading (MvPolynomial.X 0) (MvPolynomial.X 1)]
  simp

lemma projectiveCover_pair02_intersection :
    AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 2} : Finset (Fin 3)) = Point.overOpen (X := analyticPlane) pair02Open := by
  ext z
  change z ∈ (⋂ i ∈ ({0, 2} : Finset (Fin 3)), projectiveCover i) ↔ _
  simp only [Set.mem_iInter]
  change (∀ i ∈ ({0, 2} : Finset (Fin 3)),
      z.underlying ∈ chartOpen i) ↔ z.underlying ∈ pair02Open
  rw [show pair02Open = chartOpen 0 ⊓ chartOpen 2 by
    exact Proj.basicOpen_mul Grading (MvPolynomial.X 0) (MvPolynomial.X 2)]
  simp

lemma projectiveCover_pair12_intersection :
    AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({1, 2} : Finset (Fin 3)) = Point.overOpen (X := analyticPlane) overlapOpen := by
  ext z
  change z ∈ (⋂ i ∈ ({1, 2} : Finset (Fin 3)), projectiveCover i) ↔ _
  simp only [Set.mem_iInter]
  change (∀ i ∈ ({1, 2} : Finset (Fin 3)),
      z.underlying ∈ chartOpen i) ↔ z.underlying ∈ overlapOpen
  rw [show overlapOpen = chartOpen 1 ⊓ chartOpen 2 by
    exact Proj.basicOpen_mul Grading (MvPolynomial.X 1) (MvPolynomial.X 2)]
  simp

lemma projectiveCover_triple_intersection :
    AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1, 2} : Finset (Fin 3)) = Point.overOpen (X := analyticPlane) tripleOpen := by
  ext z
  change z ∈ (⋂ i ∈ ({0, 1, 2} : Finset (Fin 3)), projectiveCover i) ↔ _
  simp only [Set.mem_iInter]
  change (∀ i ∈ ({0, 1, 2} : Finset (Fin 3)),
      z.underlying ∈ chartOpen i) ↔ z.underlying ∈ tripleOpen
  rw [show tripleOpen = chartOpen 0 ⊓ chartOpen 1 ⊓ chartOpen 2 by
    change Proj.basicOpen Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) =
      Proj.basicOpen Grading (MvPolynomial.X 0) ⊓
        Proj.basicOpen Grading (MvPolynomial.X 1) ⊓
          Proj.basicOpen Grading (MvPolynomial.X 2)
    rw [← Proj.basicOpen_mul, ← Proj.basicOpen_mul]]
  simp [and_assoc]

/-- The cover's `01` intersection, mapped to the named affine open used by the displayed
coordinate fraction. -/
noncomputable def projectiveCoverPair01ToAnalyticPair :
    TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1} : Finset (Fin 3))) ⟶ TopCat.of (ComplexPoint analyticPair01) :=
  TopCat.ofHom ⟨fun z ↦
    (ComplexPoint.openHomeomorph analyticPlane pair01Open).symm
      ⟨z.1, by
        rw [← projectiveCover_pair01_intersection]
        exact z.2⟩,
    (ComplexPoint.openHomeomorph analyticPlane pair01Open).symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun z ↦ by
        rw [← projectiveCover_pair01_intersection]
        exact z.2))⟩

/-- The cover's `02` intersection, mapped to its named affine open. -/
noncomputable def projectiveCoverPair02ToAnalyticPair :
    TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 2} : Finset (Fin 3))) ⟶ TopCat.of (ComplexPoint analyticPair02) :=
  TopCat.ofHom ⟨fun z ↦
    (ComplexPoint.openHomeomorph analyticPlane pair02Open).symm
      ⟨z.1, by
        rw [← projectiveCover_pair02_intersection]
        exact z.2⟩,
    (ComplexPoint.openHomeomorph analyticPlane pair02Open).symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun z ↦ by
        rw [← projectiveCover_pair02_intersection]
        exact z.2))⟩

/-- The cover's `12` intersection, mapped to its named affine open. -/
noncomputable def projectiveCoverPair12ToAnalyticPair :
    TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({1, 2} : Finset (Fin 3))) ⟶ TopCat.of (ComplexPoint analyticOverlap) :=
  TopCat.ofHom ⟨fun z ↦
    (ComplexPoint.openHomeomorph analyticPlane overlapOpen).symm
      ⟨z.1, by
        rw [← projectiveCover_pair12_intersection]
        exact z.2⟩,
    (ComplexPoint.openHomeomorph analyticPlane overlapOpen).symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun z ↦ by
        rw [← projectiveCover_pair12_intersection]
        exact z.2))⟩

/-- The cover's triple intersection, mapped to the named triple affine open. -/
noncomputable def projectiveCoverTripleToAnalyticTriple :
    TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1, 2} : Finset (Fin 3))) ⟶ TopCat.of (ComplexPoint analyticTriple) :=
  TopCat.ofHom ⟨fun z ↦
    (ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm
      ⟨z.1, by
        rw [← projectiveCover_triple_intersection]
        exact z.2⟩,
    (ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun z ↦ by
        rw [← projectiveCover_triple_intersection]
        exact z.2))⟩

/-- The three face inclusions from the literal triple intersection of the coordinate cover. -/
noncomputable def projectiveCoverTripleToPair01 :
    TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({0, 1} : Finset (Fin 3))) :=
  AlgebraicTopology.Singular.openCoverIntersectionInclusion analyticPlaneTop projectiveCover
    (by decide : ({0, 1} : Finset (Fin 3)) ⊆ {0, 1, 2})

noncomputable def projectiveCoverTripleToPair02 :
    TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({0, 2} : Finset (Fin 3))) :=
  AlgebraicTopology.Singular.openCoverIntersectionInclusion analyticPlaneTop projectiveCover
    (by decide : ({0, 2} : Finset (Fin 3)) ⊆ {0, 1, 2})

noncomputable def projectiveCoverTripleToPair12 :
    TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({1, 2} : Finset (Fin 3))) :=
  AlgebraicTopology.Singular.openCoverIntersectionInclusion analyticPlaneTop projectiveCover
    (by decide : ({1, 2} : Finset (Fin 3)) ⊆ {0, 1, 2})

lemma projectiveCoverTripleToPair01_comm :
    projectiveCoverTripleToPair01 ≫ projectiveCoverPair01ToAnalyticPair =
      projectiveCoverTripleToAnalyticTriple ≫ tripleToPair01Top := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply (ComplexPoint.openHomeomorph analyticPlane pair01Open).injective
  apply Subtype.ext
  dsimp [projectiveCoverTripleToPair01, projectiveCoverPair01ToAnalyticPair,
    projectiveCoverTripleToAnalyticTriple, tripleToPair01Top]
  rw [(ComplexPoint.openHomeomorph analyticPlane pair01Open).apply_symm_apply]
  change z.1 = Point.map (openInclusion analyticPlane pair01Open)
    (tripleToPair01 ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm _))
  change z.1 = Point.map (openInclusion analyticPlane pair01Open)
    (Point.map tripleToPair01Over ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm _))
  rw [← Point.map_comp_apply, tripleToPair01Over_comp_openInclusion]
  let zT : {z : ComplexPoint analyticPlane // z ∈ Point.overOpen tripleOpen} :=
    ⟨z.1, by
      rw [← projectiveCover_triple_intersection]
      exact z.2⟩
  change z.1 = Point.map (openInclusion analyticPlane tripleOpen)
    ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm zT)
  exact (congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).apply_symm_apply zT)).symm

lemma projectiveCoverTripleToPair02_comm :
    projectiveCoverTripleToPair02 ≫ projectiveCoverPair02ToAnalyticPair =
      projectiveCoverTripleToAnalyticTriple ≫ tripleToPair02Top := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply (ComplexPoint.openHomeomorph analyticPlane pair02Open).injective
  apply Subtype.ext
  dsimp [projectiveCoverTripleToPair02, projectiveCoverPair02ToAnalyticPair,
    projectiveCoverTripleToAnalyticTriple, tripleToPair02Top]
  rw [(ComplexPoint.openHomeomorph analyticPlane pair02Open).apply_symm_apply]
  change z.1 = Point.map (openInclusion analyticPlane pair02Open)
    (tripleToPair02 ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm _))
  change z.1 = Point.map (openInclusion analyticPlane pair02Open)
    (Point.map tripleToPair02Over ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm _))
  rw [← Point.map_comp_apply, tripleToPair02Over_comp_openInclusion]
  let zT : {z : ComplexPoint analyticPlane // z ∈ Point.overOpen tripleOpen} :=
    ⟨z.1, by
      rw [← projectiveCover_triple_intersection]
      exact z.2⟩
  change z.1 = Point.map (openInclusion analyticPlane tripleOpen)
    ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm zT)
  exact (congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).apply_symm_apply zT)).symm

lemma projectiveCoverTripleToPair12_comm :
    projectiveCoverTripleToPair12 ≫ projectiveCoverPair12ToAnalyticPair =
      projectiveCoverTripleToAnalyticTriple ≫ tripleToOverlapTop := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply (ComplexPoint.openHomeomorph analyticPlane overlapOpen).injective
  apply Subtype.ext
  dsimp [projectiveCoverTripleToPair12, projectiveCoverPair12ToAnalyticPair,
    projectiveCoverTripleToAnalyticTriple, tripleToOverlapTop]
  rw [(ComplexPoint.openHomeomorph analyticPlane overlapOpen).apply_symm_apply]
  change z.1 = Point.map (openInclusion analyticPlane overlapOpen)
    (tripleToOverlap ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm _))
  change z.1 = Point.map (openInclusion analyticPlane overlapOpen)
    (Point.map tripleToOverlapOver ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm _))
  rw [← Point.map_comp_apply, tripleToOverlapOver_comp_openInclusion]
  let zT : {z : ComplexPoint analyticPlane // z ∈ Point.overOpen tripleOpen} :=
    ⟨z.1, by
      rw [← projectiveCover_triple_intersection]
      exact z.2⟩
  change z.1 = Point.map (openInclusion analyticPlane tripleOpen)
    ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).symm zT)
  exact (congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane tripleOpen).apply_symm_apply zT)).symm

/-- The literal winding `1`-cochain on the `01` member of the projective cover. -/
noncomputable def projectiveCoverPair01Winding :
    ((TopCat.toSSet.obj (TopCat.of
      (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({0, 1} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 1 ⟶
      ModuleCat.of ℚ ℚ :=
  (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverPair01ToAnalyticPair)
      (ModuleCat.of ℚ ℚ)).f 1 ≫
    ChernWinding.windingIntegerCochain
      pair01Transition pair01Transition_ne_zero

/-- The literal winding `1`-cochain on the `02` member of the projective cover. -/
noncomputable def projectiveCoverPair02Winding :
    ((TopCat.toSSet.obj (TopCat.of
      (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({0, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 1 ⟶
      ModuleCat.of ℚ ℚ :=
  (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverPair02ToAnalyticPair)
      (ModuleCat.of ℚ ℚ)).f 1 ≫
    ChernWinding.windingIntegerCochain
      pair02Transition pair02Transition_ne_zero

/-- The literal winding `1`-cochain on the `12` member of the projective cover. -/
noncomputable def projectiveCoverPair12Winding :
    ((TopCat.toSSet.obj (TopCat.of
      (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 1 ⟶
      ModuleCat.of ℚ ℚ :=
  (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverPair12ToAnalyticPair)
      (ModuleCat.of ℚ ℚ)).f 1 ≫
    ChernWinding.windingIntegerCochain
      pair12Transition pair12Transition_ne_zero

/-- The literal principal-log branch-defect `0`-cochain on the triple cover intersection. -/
noncomputable def projectiveCoverTripleDefect :
    ((TopCat.toSSet.obj (TopCat.of
      (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({0, 1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 0 ⟶
      ModuleCat.of ℚ ℚ :=
  (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToAnalyticTriple)
      (ModuleCat.of ℚ ℚ)).f 0 ≫
    ChernWinding.pointLogProductDefectVertexCochain
      triple01Transition triple12Transition triple02Transition
      triple01Transition_ne_zero triple12Transition_ne_zero triple02Transition_ne_zero
      tripleTransition_product

lemma projectiveCoverPair01Winding_closed :
    ((TopCat.toSSet.obj (TopCat.of
      (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({0, 1} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).d 2 1 ≫
      projectiveCoverPair01Winding = 0 := by
  rw [projectiveCoverPair01Winding, ← Category.assoc,
    ← (SSet.chainComplexMap
      (TopCat.toSSet.map projectiveCoverPair01ToAnalyticPair)
      (ModuleCat.of ℚ ℚ)).comm 2 1, Category.assoc,
    ChernWinding.d_comp_windingIntegerCochain]
  simp

lemma projectiveCoverPair02Winding_closed :
    ((TopCat.toSSet.obj (TopCat.of
      (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({0, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).d 2 1 ≫
      projectiveCoverPair02Winding = 0 := by
  rw [projectiveCoverPair02Winding, ← Category.assoc,
    ← (SSet.chainComplexMap
      (TopCat.toSSet.map projectiveCoverPair02ToAnalyticPair)
      (ModuleCat.of ℚ ℚ)).comm 2 1, Category.assoc,
    ChernWinding.d_comp_windingIntegerCochain]
  simp

lemma projectiveCoverPair12Winding_closed :
    ((TopCat.toSSet.obj (TopCat.of
      (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
        ({1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).d 2 1 ≫
      projectiveCoverPair12Winding = 0 := by
  rw [projectiveCoverPair12Winding, ← Category.assoc,
    ← (SSet.chainComplexMap
      (TopCat.toSSet.map projectiveCoverPair12ToAnalyticPair)
      (ModuleCat.of ℚ ℚ)).comm 2 1, Category.assoc,
    ChernWinding.d_comp_windingIntegerCochain]
  simp

/-- Restricting the `01` cover cochain to the triple intersection gives the displayed
`X₁/X₀` winding cochain there. -/
lemma projectiveCoverPair01Winding_restricts :
    (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair01)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair01Winding =
      (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToAnalyticTriple)
        (ModuleCat.of ℚ ℚ)).f 1 ≫
        ChernWinding.windingIntegerCochain triple01Transition triple01Transition_ne_zero := by
  let h01 : ∀ y, (pair01Transition.comp (ChernWinding.topMap tripleToPair01Top)) y ≠ 0 :=
    fun y ↦ pair01Transition_ne_zero _
  rw [projectiveCoverPair01Winding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp, projectiveCoverTripleToPair01_comm, Functor.map_comp,
    Functor.map_comp, HomologicalComplex.comp_f, Category.assoc,
    ChernWinding.chainComplexMap_comp_windingIntegerCochain (hgf := h01)]
  have hwind : ChernWinding.windingIntegerCochain
      (pair01Transition.comp (ChernWinding.topMap tripleToPair01Top)) h01 =
      ChernWinding.windingIntegerCochain triple01Transition triple01Transition_ne_zero := by
    exact AlgebraicTopology.Singular.CechWinding.windingIntegerCochain_congr _ _ _ _
      pair01Transition_restricts
  rw [hwind]

lemma projectiveCoverPair02Winding_restricts :
    (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair02)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair02Winding =
      (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToAnalyticTriple)
        (ModuleCat.of ℚ ℚ)).f 1 ≫
        ChernWinding.windingIntegerCochain triple02Transition triple02Transition_ne_zero := by
  let h02 : ∀ y, (pair02Transition.comp (ChernWinding.topMap tripleToPair02Top)) y ≠ 0 :=
    fun y ↦ pair02Transition_ne_zero _
  rw [projectiveCoverPair02Winding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp, projectiveCoverTripleToPair02_comm, Functor.map_comp,
    Functor.map_comp, HomologicalComplex.comp_f, Category.assoc,
    ChernWinding.chainComplexMap_comp_windingIntegerCochain (hgf := h02)]
  have hwind : ChernWinding.windingIntegerCochain
      (pair02Transition.comp (ChernWinding.topMap tripleToPair02Top)) h02 =
      ChernWinding.windingIntegerCochain triple02Transition triple02Transition_ne_zero := by
    exact AlgebraicTopology.Singular.CechWinding.windingIntegerCochain_congr _ _ _ _
      pair02Transition_restricts
  rw [hwind]

lemma projectiveCoverPair12Winding_restricts :
    (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair12)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair12Winding =
      (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToAnalyticTriple)
        (ModuleCat.of ℚ ℚ)).f 1 ≫
        ChernWinding.windingIntegerCochain triple12Transition triple12Transition_ne_zero := by
  let h12 : ∀ y, (pair12Transition.comp (ChernWinding.topMap tripleToOverlapTop)) y ≠ 0 :=
    fun y ↦ pair12Transition_ne_zero _
  rw [projectiveCoverPair12Winding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp, projectiveCoverTripleToPair12_comm, Functor.map_comp,
    Functor.map_comp, HomologicalComplex.comp_f, Category.assoc,
    ChernWinding.chainComplexMap_comp_windingIntegerCochain (hgf := h12)]
  have hwind : ChernWinding.windingIntegerCochain
      (pair12Transition.comp (ChernWinding.topMap tripleToOverlapTop)) h12 =
      ChernWinding.windingIntegerCochain triple12Transition triple12Transition_ne_zero := by
    exact AlgebraicTopology.Singular.CechWinding.windingIntegerCochain_congr _ _ _ _
      pair12Transition_restricts
  rw [hwind]

/-- The literal Čech relation on the triple cover intersection.  This is the raw equality
`wind₀₁ - wind₀₂ + wind₁₂ = d(branchJump)`, before any cohomology is taken. -/
lemma projectiveCoverTriple_winding_relation :
    (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair01)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair01Winding -
      (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair02)
        (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair02Winding +
      (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair12)
        (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair12Winding =
      ((TopCat.toSSet.obj (TopCat.of
        (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
          ({0, 1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 ≫
        projectiveCoverTripleDefect := by
  rw [projectiveCoverPair01Winding_restricts, projectiveCoverPair02Winding_restricts,
    projectiveCoverPair12Winding_restricts, projectiveCoverTripleDefect, ← Category.assoc,
    ← (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToAnalyticTriple)
      (ModuleCat.of ℚ ℚ)).comm 1 0, Category.assoc]
  rw [← Preadditive.comp_sub, ← Preadditive.comp_add]
  have hwind := ChernWinding.windingIntegerCochain_mul_eq_add_sub_coboundary
    triple01Transition triple12Transition triple02Transition
    triple01Transition_ne_zero triple12Transition_ne_zero triple02Transition_ne_zero
    tripleTransition_product
  rw [hwind]
  abel

local notation "projectiveCoverChainModels" =>
  AlgebraicTopology.Singular.rationalOpenCoverIntersectionChainModels analyticPlaneTop projectiveCover

local notation "projectiveCechBicomplex" =>
  AlgebraicTopology.SupportChainModels.cechComplex projectiveCoverChainModels
    AlgebraicTopology.TupleClass.strictMono

noncomputable def projectiveCoverPair01WindingTuple :
    (((projectiveCoverChainModels).model
      (AlgebraicTopology.tupleSupport (![0, 1] : Fin 2 → Fin 3))).X 1) ⟶ ModuleCat.of ℚ ℚ := by
  change ((TopCat.toSSet.obj (TopCat.of
    (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 1 ⟶ ModuleCat.of ℚ ℚ
  exact projectiveCoverPair01Winding

noncomputable def projectiveCoverPair02WindingTuple :
    (((projectiveCoverChainModels).model
      (AlgebraicTopology.tupleSupport (![0, 2] : Fin 2 → Fin 3))).X 1) ⟶ ModuleCat.of ℚ ℚ := by
  change ((TopCat.toSSet.obj (TopCat.of
    (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 1 ⟶ ModuleCat.of ℚ ℚ
  exact projectiveCoverPair02Winding

noncomputable def projectiveCoverPair12WindingTuple :
    (((projectiveCoverChainModels).model
      (AlgebraicTopology.tupleSupport (![1, 2] : Fin 2 → Fin 3))).X 1) ⟶ ModuleCat.of ℚ ℚ := by
  change ((TopCat.toSSet.obj (TopCat.of
    (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 1 ⟶ ModuleCat.of ℚ ℚ
  exact projectiveCoverPair12Winding

noncomputable def projectiveCoverTripleDefectTuple :
    (((projectiveCoverChainModels).model
      (AlgebraicTopology.tupleSupport (![0, 1, 2] : Fin 3 → Fin 3))).X 0) ⟶ ModuleCat.of ℚ ℚ := by
  change ((TopCat.toSSet.obj (TopCat.of
    (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
      ({0, 1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).X 0 ⟶ ModuleCat.of ℚ ℚ
  exact projectiveCoverTripleDefect

lemma strictMono_finTwo_classify (a : Fin 2 → Fin 3) (ha : StrictMono a) :
    a = ![0, 1] ∨ a = ![0, 2] ∨ a = ![1, 2] := by
  have hlt : a 0 < a 1 := ha (by decide)
  generalize hx : a 0 = x
  generalize hy : a 1 = y
  fin_cases x <;> fin_cases y
  all_goals simp [hx, hy] at hlt
  · exact Or.inl (by
      funext i
      fin_cases i <;> simp [hx, hy])
  · exact Or.inr (Or.inl (by
      funext i
      fin_cases i <;> simp [hx, hy]))
  · exact Or.inr (Or.inr (by
      funext i
      fin_cases i <;> simp [hx, hy]))

lemma strictMono_finThree_eq_id (a : Fin 3 → Fin 3) (ha : StrictMono a) :
    a = ![0, 1, 2] := by
  have h01 : a 0 < a 1 := ha (by decide)
  have h12 : a 1 < a 2 := ha (by decide)
  generalize hx : a 0 = x
  generalize hy : a 1 = y
  generalize hz : a 2 = z
  fin_cases x <;> fin_cases y <;> fin_cases z
  all_goals simp [hx, hy, hz] at h01 h12
  funext i
  fin_cases i <;> simp [hx, hy, hz]

/-- The pair-overlap part of the displayed cochain, indexed by the actual strictly increasing
two-tuples of the coordinate cover. -/
noncomputable def projectiveCoverPairCochain
    (a : {a : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 a}) :
    (((projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport a.1)).X 1) ⟶
      ModuleCat.of ℚ ℚ := by
  rcases a with ⟨a, ha⟩
  classical
  by_cases h01 : a = ![0, 1]
  · subst a
    exact projectiveCoverPair01WindingTuple
  by_cases h02 : a = ![0, 2]
  · subst a
    exact projectiveCoverPair02WindingTuple
  by_cases h12 : a = ![1, 2]
  · subst a
    exact projectiveCoverPair12WindingTuple
  exact False.elim (h12 (((strictMono_finTwo_classify a ha).resolve_left h01).resolve_left h02))

/-- The triple-overlap component is the negative principal-log defect, matching the alternating
Čech sign convention. -/
noncomputable def projectiveCoverTripleCochain
    (a : {a : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 a}) :
    (((projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport a.1)).X 0) ⟶
      ModuleCat.of ℚ ℚ := by
  rcases a with ⟨a, ha⟩
  classical
  by_cases h : a = ![0, 1, 2]
  · subst a
    exact -projectiveCoverTripleDefectTuple
  exact False.elim (h (strictMono_finThree_eq_id a ha))

/-- Each pair-overlap component is vertically closed before it is inserted into the total
complex. -/
lemma projectiveCoverPairCochain_closed
    (a : {a : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 a}) :
    ((projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport a.1)).d 2 1 ≫
      projectiveCoverPairCochain a = 0 := by
  rcases a with ⟨a, ha⟩
  classical
  rcases strictMono_finTwo_classify a ha with h01 | h02 | h12
  · subst a
    exact projectiveCoverPair01Winding_closed
  · subst a
    exact projectiveCoverPair02Winding_closed
  · subst a
    exact projectiveCoverPair12Winding_closed

noncomputable def projectiveCoverPairDegreeDesc :
    ((projectiveCoverChainModels).cechObject AlgebraicTopology.TupleClass.strictMono 1).X 1 ⟶
      ModuleCat.of ℚ ℚ :=
  (CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)
    (fun a : {a : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 a} ↦
      (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport a.1))
    (fun a ↦ CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a)
    (CategoryTheory.Limits.coproductIsCoproduct _)).desc
      (CategoryTheory.Limits.Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun a ↦ projectiveCoverPairCochain a))

noncomputable def projectiveCoverTripleDegreeDesc :
    ((projectiveCoverChainModels).cechObject AlgebraicTopology.TupleClass.strictMono 2).X 0 ⟶
      ModuleCat.of ℚ ℚ :=
  (CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0)
    (fun a : {a : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 a} ↦
      (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport a.1))
    (fun a ↦ CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a)
    (CategoryTheory.Limits.coproductIsCoproduct _)).desc
      (CategoryTheory.Limits.Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun a ↦ projectiveCoverTripleCochain a))

/-- Evaluation of the pair-overlap functional on one normalized Čech summand. -/
lemma projectiveCoverPairDegreeDesc_ι
    (a : {a : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 a}) :
    (CategoryTheory.Limits.Sigma.ι
        (fun b : {b : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 b} ↦
          (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a).f 1 ≫
      projectiveCoverPairDegreeDesc = projectiveCoverPairCochain a := by
  change (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1).map
      (CategoryTheory.Limits.Sigma.ι
        (fun b : {b : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 b} ↦
          (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a) ≫
        projectiveCoverPairDegreeDesc = projectiveCoverPairCochain a
  exact (CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)
    (fun b : {b : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 b} ↦
      (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1))
    (fun b ↦ CategoryTheory.Limits.Sigma.ι
      (fun c : {c : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 c} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport c.1)) b)
    (CategoryTheory.Limits.coproductIsCoproduct _)).fac
      (CategoryTheory.Limits.Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun b ↦ projectiveCoverPairCochain b)) ⟨a⟩

/-- Evaluation of the triple-overlap functional on the unique normalized Čech summand. -/
lemma projectiveCoverTripleDegreeDesc_ι
    (a : {a : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 a}) :
    (CategoryTheory.Limits.Sigma.ι
        (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
          (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a).f 0 ≫
      projectiveCoverTripleDegreeDesc = projectiveCoverTripleCochain a := by
  change (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0).map
      (CategoryTheory.Limits.Sigma.ι
        (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
          (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a) ≫
        projectiveCoverTripleDegreeDesc = projectiveCoverTripleCochain a
  exact (CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0)
    (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
      (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1))
    (fun b ↦ CategoryTheory.Limits.Sigma.ι
      (fun c : {c : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 c} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport c.1)) b)
    (CategoryTheory.Limits.coproductIsCoproduct _)).fac
      (CategoryTheory.Limits.Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun b ↦ projectiveCoverTripleCochain b)) ⟨a⟩

set_option backward.isDefEq.respectTransparency false in
lemma projectiveCoverPairDegreeDesc_closed :
    (((projectiveCoverChainModels).cechComplex
      AlgebraicTopology.TupleClass.strictMono).X 1).d 2 1 ≫
      projectiveCoverPairDegreeDesc = 0 := by
  change ((projectiveCoverChainModels).cechObject
    AlgebraicTopology.TupleClass.strictMono 1).d 2 1 ≫
      projectiveCoverPairDegreeDesc = 0
  apply (CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 2)
    (fun b : {b : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 b} ↦
      (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1))
    (fun b ↦ CategoryTheory.Limits.Sigma.ι
      (fun c : {c : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 c} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport c.1)) b)
    (CategoryTheory.Limits.coproductIsCoproduct _)).hom_ext
  rintro ⟨a⟩
  change (CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a).f 2 ≫
      ((projectiveCoverChainModels).cechObject
        AlgebraicTopology.TupleClass.strictMono 1).d 2 1 ≫
      projectiveCoverPairDegreeDesc = 0
  rw [← Category.assoc,
    (CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a).comm 2 1,
    Category.assoc, projectiveCoverPairDegreeDesc_ι]
  exact projectiveCoverPairCochain_closed a

set_option backward.isDefEq.respectTransparency false in
lemma projectiveCoverChainModels_ι_comp_outer_d (p : ℕ)
    (a : {a : Fin (p + 2) → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem (p + 1) a}) :
    CategoryTheory.Limits.Sigma.ι
        (fun b : {b : Fin (p + 2) → Fin 3 //
          AlgebraicTopology.TupleClass.strictMono.mem (p + 1) b} ↦
          (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a ≫
        ((projectiveCoverChainModels).cechComplex
          AlgebraicTopology.TupleClass.strictMono).d (p + 1) p =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.val) •
        ((projectiveCoverChainModels).face (by
          rw [AlgebraicTopology.tupleSupport_subset_iff]
          exact Set.range_comp_subset_range i.succAbove a.1) ≫
          CategoryTheory.Limits.Sigma.ι
            (fun b : {b : Fin (p + 1) → Fin 3 //
              AlgebraicTopology.TupleClass.strictMono.mem p b} ↦
              (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1))
            ⟨Fin.removeNth i a.1,
              AlgebraicTopology.TupleClass.strictMono.removeNth_mem p a.1 i a.2⟩) := by
  rw [AlgebraicTopology.SupportChainModels.cechComplex_d,
    AlgebraicTopology.SupportChainModels.ι_realize,
    AlgebraicTopology.OrderedCechTuple.boundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Finsupp.single (Fin.removeNth i a.1) ((-1 : ℤ) ^ i.val * 1) =
      ((-1 : ℤ) ^ i.val) • Finsupp.single (Fin.removeNth i a.1) 1 by simp,
    map_zsmul]
  congr 1
  rw [AlgebraicTopology.SupportChainModels.realizeAux_single]
  unfold AlgebraicTopology.SupportChainModels.faceOrZero
  rw [dif_pos (by
    rw [AlgebraicTopology.tupleSupport_subset_iff]
    exact Set.range_comp_subset_range i.succAbove a.1),
    AlgebraicTopology.SupportChainModels.ιOrZero_of_mem]

lemma projectiveCoverTripleDegreeDesc_vertical
    (a : {a : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 a}) :
    (CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a).f 1 ≫
      (((projectiveCoverChainModels).cechComplex
        AlgebraicTopology.TupleClass.strictMono).X 2).d 1 0 ≫
      projectiveCoverTripleDegreeDesc =
        ((projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport a.1)).d 1 0 ≫
          projectiveCoverTripleCochain a := by
  change (CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a).f 1 ≫
      ((projectiveCoverChainModels).cechObject
        AlgebraicTopology.TupleClass.strictMono 2).d 1 0 ≫
      projectiveCoverTripleDegreeDesc = _
  rw [← Category.assoc,
    (CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1)) a).comm 1 0,
    Category.assoc, projectiveCoverTripleDegreeDesc_ι]

lemma projectiveCoverTripleDegreeDesc_vertical_explicit :
    ((projectiveCoverChainModels).model
      (AlgebraicTopology.tupleSupport (![0, 1, 2] : Fin 3 → Fin 3))).d 1 0 ≫
      projectiveCoverTripleCochain ⟨![0, 1, 2], by decide⟩ =
      -(((TopCat.toSSet.obj (TopCat.of
        (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
          ({0, 1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 ≫
    projectiveCoverTripleDefect) := by
  rfl

set_option maxHeartbeats 1000000 in
lemma projectiveCoverTriple_relation_transport
    (a12 a02 a01 : {a : Fin 2 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 1 a})
    (h12 : a12 = ⟨![1, 2], by decide⟩)
    (h02 : a02 = ⟨![0, 2], by decide⟩)
    (h01 : a01 = ⟨![0, 1], by decide⟩)
    (hs12 : (AlgebraicTopology.tupleSupport a12.1).1 ⊆
      (AlgebraicTopology.tupleSupport (![0, 1, 2] : Fin 3 → Fin 3)).1)
    (hs02 : (AlgebraicTopology.tupleSupport a02.1).1 ⊆
      (AlgebraicTopology.tupleSupport (![0, 1, 2] : Fin 3 → Fin 3)).1)
    (hs01 : (AlgebraicTopology.tupleSupport a01.1).1 ⊆
      (AlgebraicTopology.tupleSupport (![0, 1, 2] : Fin 3 → Fin 3)).1) :
    ((projectiveCoverChainModels).face hs12).f 1 ≫ projectiveCoverPairCochain a12 -
      ((projectiveCoverChainModels).face hs02).f 1 ≫ projectiveCoverPairCochain a02 +
      ((projectiveCoverChainModels).face hs01).f 1 ≫ projectiveCoverPairCochain a01 +
      ((projectiveCoverChainModels).model
        (AlgebraicTopology.tupleSupport (![0, 1, 2] : Fin 3 → Fin 3))).d 1 0 ≫
          projectiveCoverTripleCochain ⟨![0, 1, 2], by decide⟩ = 0 := by
  subst a12
  subst a02
  subst a01
  change
    (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair12)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair12Winding -
      (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair02)
        (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair02Winding +
      (SSet.chainComplexMap (TopCat.toSSet.map projectiveCoverTripleToPair01)
        (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair01Winding +
      -(((TopCat.toSSet.obj (TopCat.of
        (AlgebraicTopology.Singular.openCoverIntersection analyticPlaneTop projectiveCover
          ({0, 1, 2} : Finset (Fin 3))))).chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 ≫
        projectiveCoverTripleDefect) = 0
  rw [← projectiveCoverTriple_winding_relation]
  abel

set_option backward.isDefEq.respectTransparency false in
lemma projectiveCoverTriple_outer_vertical_relation :
    (((projectiveCoverChainModels).cechComplex
      AlgebraicTopology.TupleClass.strictMono).d 2 1).f 1 ≫
        projectiveCoverPairDegreeDesc +
      (((projectiveCoverChainModels).cechComplex
        AlgebraicTopology.TupleClass.strictMono).X 2).d 1 0 ≫
        projectiveCoverTripleDegreeDesc = 0 := by
  apply (CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)
    (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
      (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1))
    (fun b ↦ CategoryTheory.Limits.Sigma.ι
      (fun c : {c : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 c} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport c.1)) b)
    (CategoryTheory.Limits.coproductIsCoproduct _)).hom_ext
  rintro ⟨a⟩
  rcases a with ⟨a, ha⟩
  have htriple : a = ![0, 1, 2] := strictMono_finThree_eq_id a ha
  subst a
  change (CategoryTheory.Limits.Sigma.ι
      (fun b : {b : Fin 3 → Fin 3 // AlgebraicTopology.TupleClass.strictMono.mem 2 b} ↦
        (projectiveCoverChainModels).model (AlgebraicTopology.tupleSupport b.1))
      ⟨![0, 1, 2], by decide⟩).f 1 ≫ (_ + _) = 0
  rw [Preadditive.comp_add, ← Category.assoc, ← HomologicalComplex.comp_f,
    projectiveCoverChainModels_ι_comp_outer_d 1 ⟨![0, 1, 2], by decide⟩]
  rw [Fin.sum_univ_three, HomologicalComplex.add_f_apply,
    HomologicalComplex.add_f_apply, HomologicalComplex.zsmul_f_apply,
    HomologicalComplex.zsmul_f_apply, HomologicalComplex.zsmul_f_apply]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  norm_num
  rw [projectiveCoverPairDegreeDesc_ι, projectiveCoverPairDegreeDesc_ι,
    projectiveCoverPairDegreeDesc_ι, projectiveCoverTripleDegreeDesc_vertical]
  simpa [sub_eq_add_neg] using projectiveCoverTriple_relation_transport
    ⟨Fin.removeNth 0 (![0, 1, 2] : Fin 3 → Fin 3), by decide⟩
    ⟨Fin.removeNth 1 (![0, 1, 2] : Fin 3 → Fin 3), by decide⟩
    ⟨Fin.removeNth 2 (![0, 1, 2] : Fin 3 → Fin 3), by decide⟩
    (by apply Subtype.ext; decide) (by apply Subtype.ext; decide) (by apply Subtype.ext; decide)
    (by
      rw [AlgebraicTopology.tupleSupport_subset_iff]
      exact Set.range_comp_subset_range (0 : Fin 3).succAbove (![0, 1, 2] : Fin 3 → Fin 3))
    (by
      rw [AlgebraicTopology.tupleSupport_subset_iff]
      exact Set.range_comp_subset_range (1 : Fin 3).succAbove (![0, 1, 2] : Fin 3 → Fin 3))
    (by
      rw [AlgebraicTopology.tupleSupport_subset_iff]
      exact Set.range_comp_subset_range (2 : Fin 3).succAbove (![0, 1, 2] : Fin 3 → Fin 3))

/-- The degree-two functional on the literal normalized Čech--singular total chains.  Its
`(1,1)` summand is the three winding functionals and its `(2,0)` summand is the displayed
negative branch defect; all other summands are zero. -/
noncomputable def coordinateProjectiveCoverTotalFunctional :
    (((projectiveCoverChainModels).cechTotal AlgebraicTopology.TupleClass.strictMono).X 2) ⟶
      ModuleCat.of ℚ ℚ :=
  ((projectiveCoverChainModels).cechComplex AlgebraicTopology.TupleClass.strictMono).totalDesc
    (fun p q hpq ↦ by
    change p + q = 2 at hpq
    rcases p with _ | p
    · have hq : q = 2 := by omega
      subst q
      exact 0
    rcases p with _ | p
    · have hq : q = 1 := by omega
      subst q
      rw [AlgebraicTopology.SupportChainModels.cechComplex_X]
      exact projectiveCoverPairDegreeDesc
    rcases p with _ | p
    · have hq : q = 0 := by omega
      subst q
      rw [AlgebraicTopology.SupportChainModels.cechComplex_X]
      exact projectiveCoverTripleDegreeDesc
    omega)

lemma coordinateProjectiveCoverTotalFunctional_pair :
    ((projectiveCoverChainModels).cechComplex
      AlgebraicTopology.TupleClass.strictMono).ιTotal (ComplexShape.down ℕ) 1 1 2 (by norm_num) ≫
      coordinateProjectiveCoverTotalFunctional = projectiveCoverPairDegreeDesc := by
  rw [coordinateProjectiveCoverTotalFunctional, HomologicalComplex₂.ι_totalDesc]
  rfl

lemma coordinateProjectiveCoverTotalFunctional_triple :
    ((projectiveCoverChainModels).cechComplex
      AlgebraicTopology.TupleClass.strictMono).ιTotal (ComplexShape.down ℕ) 2 0 2 (by norm_num) ≫
      coordinateProjectiveCoverTotalFunctional = projectiveCoverTripleDegreeDesc := by
  rw [coordinateProjectiveCoverTotalFunctional, HomologicalComplex₂.ι_totalDesc]
  rfl

lemma coordinateProjectiveCoverTotalFunctional_zero :
    ((projectiveCoverChainModels).cechComplex
      AlgebraicTopology.TupleClass.strictMono).ιTotal (ComplexShape.down ℕ) 0 2 2 (by norm_num) ≫
      coordinateProjectiveCoverTotalFunctional = 0 := by
  rw [coordinateProjectiveCoverTotalFunctional, HomologicalComplex₂.ι_totalDesc]
  rfl

set_option maxHeartbeats 1000000 in
lemma coordinateProjectiveCoverTotalFunctional_closed :
    ((projectiveCoverChainModels).cechTotal AlgebraicTopology.TupleClass.strictMono).d 3 2 ≫
      coordinateProjectiveCoverTotalFunctional = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have hpq' : p + q = 3 := hpq
  simp only [CategoryTheory.Limits.comp_zero]
  rw [← Category.assoc, AlgebraicTopology.ιTotal_total_d, Preadditive.add_comp]
  rcases p with _ | p
  · have hq : q = 3 := by omega
    subst q
    rw [AlgebraicTopology.d₁_zero,
      AlgebraicTopology.d₂_succ, Linear.units_smul_comp, Category.assoc,
      (projectiveCechBicomplex).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 2 2 (by norm_num),
      coordinateProjectiveCoverTotalFunctional_zero]
    simp
  · rcases p with _ | p
    · have hq : q = 2 := by omega
      subst q
      have houter : (projectiveCechBicomplex).d₁ (ComplexShape.down ℕ) 1 2 2 ≫
          coordinateProjectiveCoverTotalFunctional = 0 := by
        rw [AlgebraicTopology.d₁_succ, Category.assoc,
          (projectiveCechBicomplex).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 2 2 (by norm_num),
          coordinateProjectiveCoverTotalFunctional_zero]
        simp
      have hvertical : (projectiveCechBicomplex).d₂ (ComplexShape.down ℕ) 1 2 2 ≫
          coordinateProjectiveCoverTotalFunctional = 0 := by
        rw [AlgebraicTopology.d₂_succ, Linear.units_smul_comp, Category.assoc,
          (projectiveCechBicomplex).ιTotalOrZero_eq (ComplexShape.down ℕ) 1 1 2 (by norm_num),
          coordinateProjectiveCoverTotalFunctional_pair,
          projectiveCoverPairDegreeDesc_closed]
        simp
      calc
        _ = 0 + 0 := congrArg₂ (· + ·) houter hvertical
        _ = 0 := by simp
    · rcases p with _ | p
      · have hq : q = 1 := by omega
        subst q
        have houter : (projectiveCechBicomplex).d₁ (ComplexShape.down ℕ) 2 1 2 ≫
            coordinateProjectiveCoverTotalFunctional =
          ((projectiveCechBicomplex).d 2 1).f 1 ≫ projectiveCoverPairDegreeDesc := by
          rw [AlgebraicTopology.d₁_succ, Category.assoc,
            (projectiveCechBicomplex).ιTotalOrZero_eq (ComplexShape.down ℕ) 1 1 2
              (by norm_num), coordinateProjectiveCoverTotalFunctional_pair]
        have hvertical : (projectiveCechBicomplex).d₂ (ComplexShape.down ℕ) 2 1 2 ≫
            coordinateProjectiveCoverTotalFunctional =
          ((projectiveCechBicomplex).X 2).d 1 0 ≫ projectiveCoverTripleDegreeDesc := by
          rw [AlgebraicTopology.d₂_succ, Linear.units_smul_comp, Category.assoc,
            (projectiveCechBicomplex).ιTotalOrZero_eq (ComplexShape.down ℕ) 2 0 2
              (by norm_num), coordinateProjectiveCoverTotalFunctional_triple]
          simpa
        rw [houter, hvertical, projectiveCoverTriple_outer_vertical_relation]
      · have hq : q = 0 := by omega
        subst q
        have hzcol : CategoryTheory.Limits.IsZero ((projectiveCoverChainModels).cechObject
            AlgebraicTopology.TupleClass.strictMono (p + 3)) :=
          (projectiveCoverChainModels).isZero_cechObject_strictMono (by
            simp only [Fintype.card_fin]
            omega)
        have hz : CategoryTheory.Limits.IsZero (((projectiveCoverChainModels).cechObject
            AlgebraicTopology.TupleClass.strictMono (p + 3)).X 0) :=
          (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0).map_isZero hzcol
        exact hz.eq_of_src _ _

/-- The explicit degree-two cochain as an element of the linear-dual cochain complex. -/
noncomputable def coordinateProjectiveCoverCochain :
    ((projectiveCoverChainModels).cechTotal
      AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex.X 2 :=
  coordinateProjectiveCoverTotalFunctional.hom

/-- The displayed cochain is closed in the dual total complex.  Unfolding the dual
differential says exactly that the total boundary annihilates the functional proved closed
above. -/
lemma coordinateProjectiveCoverCochain_closed :
    (((projectiveCoverChainModels).cechTotal
      AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex).d 2 3
      coordinateProjectiveCoverCochain = 0 := by
  change (((projectiveCoverChainModels).cechTotal
    AlgebraicTopology.TupleClass.strictMono).d 3 2 ≫
      coordinateProjectiveCoverTotalFunctional).hom = 0
  rw [coordinateProjectiveCoverTotalFunctional_closed]
  rfl

/-- The literal cochain factored through the cycle object. -/
noncomputable def coordinateProjectiveCoverCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (((projectiveCoverChainModels).cechTotal
        AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex).cycles 2 :=
  (((projectiveCoverChainModels).cechTotal
    AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex).liftCycles
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCoverCochain)) 3
      (by norm_num) (by
        ext
        change (((projectiveCoverChainModels).cechTotal
          AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex).d 2 3
            (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCoverCochain 1) = 0
        rw [LinearMap.toSpanSingleton_apply]
        simpa using coordinateProjectiveCoverCochain_closed)

/-- Forgetting the cycle factorization recovers the explicitly displayed total cochain. -/
lemma coordinateProjectiveCoverCocycle_iCycles :
    coordinateProjectiveCoverCocycle ≫
      (((projectiveCoverChainModels).cechTotal
        AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex).iCycles 2 =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCoverCochain) := by
  exact HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The cohomology class of the literal coordinate cocycle in the normalized
Čech--singular total complex. -/
noncomputable def coordinateProjectiveCoverCochainClass :
    (((projectiveCoverChainModels).cechTotal
      AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex).homology 2 :=
  (coordinateProjectiveCoverCocycle ≫
    (((projectiveCoverChainModels).cechTotal
      AlgebraicTopology.TupleClass.strictMono).linearDualCochainComplex).homologyπ 2).hom 1

/-- The rational chain comparison from the explicit cover total to all singular chains. -/
noncomputable def coordinateProjectiveCoverToSingular :
    (projectiveCoverChainModels).cechTotal AlgebraicTopology.TupleClass.strictMono ⟶
      (TopCat.toSSet.obj analyticPlaneTop).chainComplex (ModuleCat.of ℚ ℚ) :=
  AlgebraicTopology.Singular.rationalOpenCoverNormalizedCechTotalToSingular
    analyticPlaneTop projectiveCover

/-- The cochain-complex cohomology class transported from the explicit cover total to all
rational singular cochains. -/
noncomputable def coordinateProjectiveCoverSingularCochainClass :
    ((TopCat.toSSet.obj analyticPlaneTop).chainComplex
      (ModuleCat.of ℚ ℚ)).linearDualCochainComplex.homology 2 := by
  letI : QuasiIso coordinateProjectiveCoverToSingular :=
    projectiveCover_rationalNormalizedCechToSingular_quasiIso
  exact (HomologicalComplex.linearDualCohomologyEquivOfQuasiIso
    coordinateProjectiveCoverToSingular 2).symm coordinateProjectiveCoverCochainClass

/-- The ordinary rational singular cohomology class represented by the explicit
Čech--singular coordinate cocycle. -/
noncomputable def coordinateProjectiveCoverSingularClass :
    AlgebraicTopology.Singular.Cohomology ℚ analyticPlaneTop 2 :=
  HomologicalComplex.linearDualHomologyEquiv
    (AlgebraicTopology.Singular.SingularChainComplex ℚ analyticPlaneTop) 2
    coordinateProjectiveCoverSingularCochainClass

/-- The same explicitly constructed class in the constant-sheaf hypercohomology model, under
the explicitly displayed separation and hereditary-paracompactness hypotheses.

The only transport here is the proved Betti comparison for the smooth direct `Proj` model of
`ℙ²`; no cycle-class or Chern-class comparison is invoked. -/
noncomputable def coordinateProjectiveCoverHypercohomologyClass_of_topologicalHypotheses
    [T2Space (ComplexPoint analyticPlane)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U] :
    H2 := by
  letI : T2Space (ComplexPoint planeOver) := by
    change T2Space (ComplexPoint analyticPlane)
    infer_instance
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U := by
    change ∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U
    infer_instance
  exact (planeBettiComparison_of_smoothOfRelativeDimension).symm
    coordinateProjectiveCoverSingularClass

/-- The same hypercohomology class with the topological comparison hypotheses discharged from
projectivity and the already proved smooth relative dimension of the direct `Proj` plane.

The remaining explicit hypothesis is only projectivity of this particular direct `Proj`
structure morphism; it is not concealed in the construction. -/
noncomputable def coordinateProjectiveCoverHypercohomologyClass_of_isProjective
    [IsProjective planeOver.hom] : H2 := by
  letI : IsProjective analyticPlane.hom := by
    change IsProjective planeOver.hom
    infer_instance
  letI : SmoothOfRelativeDimension 2 analyticPlane.hom := by
    change SmoothOfRelativeDimension 2 planeOver.hom
    infer_instance
  letI : T2Space (ComplexPoint analyticPlane) :=
    @IsProjective.complexPoint_t2Space analyticPlane inferInstance
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U :=
    fun U ↦ ComplexPoint.openParacompactSpace_of_smoothOfRelativeDimension analyticPlane 2 U
  exact coordinateProjectiveCoverHypercohomologyClass_of_topologicalHypotheses

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
