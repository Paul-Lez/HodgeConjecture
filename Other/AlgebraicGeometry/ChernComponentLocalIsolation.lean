/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernLocalModelWinding
public import Other.AlgebraicGeometry.ChernRelativeCanonicalLift
public import Other.AlgebraicGeometry.CartierWindingChartCoefficient

/-!
# Local isolation of a component support
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernComponentLocalIsolationTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Support-enlargement is an isomorphism on sections over an open where the two supports have the
same trace. -/
theorem supportedInjectiveComplexMap_local_isIso
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hW : W ⊓ S.compl ≤ T.compl) :
    IsIso (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).map
      (supportedInjectiveComplexMap X hST)) := by
  let ψ := ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).map
    (supportedInjectiveComplexMap X hST)
  have hcomp : T.compl ≤ S.compl := by
    intro z hzS hzT
    exact hzS (hST hzT)
  have hψ : ∀ j : ℤ, IsIso (ψ.f j) := by
    intro j
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact TopCat.Sheaf.supportedOutsideMap_app_bijective hcomp hW
      ((ambientRationalInjectiveComplex X).X j)
  exact HomologicalComplex.Hom.isIso_of_components ψ

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The induced support-enlargement map on local supported cohomology is an isomorphism under the
same trace condition. -/
theorem supportedInjectiveHomology_local_map_isIso
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hW : W ⊓ S.compl ≤ T.compl) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).map
        (supportedInjectiveComplexMap X hST)) n) := by
  let ψ := ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).map
    (supportedInjectiveComplexMap X hST)
  let : IsIso ψ := supportedInjectiveComplexMap_local_isIso (X := X) hST W hW
  infer_instance

namespace ChernWindingChart

variable {c : Scheme.CartierData X.left} {x : X.left} {d : ℕ}
  [SmoothOfRelativeDimension d X.hom] {q : ComplexPoint X}

/-- The actual supported-injective complex map from this component to the bad-locus support is an
isomorphism after evaluating on the chart carrier. -/
theorem componentToBadLocusMap_local_isIso
    (ch : ChernWindingChart X c x d 1 q) (hx : c.divisor x ≠ 0) :
    IsIso (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ch.carrier).mapHomologicalComplex
      (.up ℤ)).map
      (supportedInjectiveComplexMap X
        (show cycleComponentAnalyticClosedSupport X x ≤ analyticClosedSupport X (badLocus c) from
          fun _ hy => closure_subset_badLocus c x hx hy))) := by
  apply supportedInjectiveComplexMap_local_isIso (X := X)
  simpa only [ChernWindingChart.punctured] using ch.punctured_le_goodComplement

/-- The corresponding map on local degree-two supported cohomology is an isomorphism. -/
theorem componentToBadLocusHomology_local_map_isIso
    (ch : ChernWindingChart X c x d 1 q) (hx : c.divisor x ≠ 0) :
    IsIso (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ch.carrier).mapHomologicalComplex
        (.up ℤ)).map
        (supportedInjectiveComplexMap X
          (show cycleComponentAnalyticClosedSupport X x ≤
              analyticClosedSupport X (badLocus c) from
            fun _ hy => closure_subset_badLocus c x hx hy))) (2 : ℤ)) := by
  apply supportedInjectiveHomology_local_map_isIso (X := X)
  simpa only [ChernWindingChart.punctured] using ch.punctured_le_goodComplement

end ChernWindingChart

end AlgebraicGeometry.ComplexPoint
