/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingChartCoclassRestrict
public import Other.AlgebraicGeometry.ChernWindingGenericChartData
public import Other.AlgebraicGeometry.ChernWindingNormalChartExistence

/-!
# Assembly of generic winding chart data
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingGenericChartAssemblyTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

variable (c : Scheme.CartierData X.left) (x : X.left) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

namespace FlatteningChartWithCoclass

variable {x d} {q : ComplexPoint X}

abbrev restrictedFlattened
    (F : FlatteningChartWithCoclass X x d q)
    (V : Opens (ComplexPoint X)) (hqV : q ∈ V) : Opens (ComplexPoint X) :=
  (F.restrict V hqV).flattened

/-- Assemble generic chart data from a full-neighbourhood unit factorisation.

The hypothesis `hfactor` is deliberately stated for the winding function.  It is the exact
interface needed by the winding normalization theorem and avoids discarding the holomorphic
provenance of the canonical flattening chart before the algebraic factorisation is supplied.
-/
def toGenericWindingChartData
    (F : FlatteningChartWithCoclass X x d q)
    (V : Opens (ComplexPoint X)) (hqV : q ∈ V)
    (i : c.ι) (localForm : c.LocalForm i x)
    (hV : V ≤ analyticOpen X localForm.opens)
    (coord : (holomorphicUnitSheaf X d).obj.obj
      (op (restrictedFlattened F V hqV ⊓
        (cycleComponentAnalyticClosedSupport X x).compl)))
    (hcoord : ((Additive.toMul coord).val :
        (holomorphicRingSheaf X d).obj.obj
          (op (restrictedFlattened F V hqV ⊓
            (cycleComponentAnalyticClosedSupport X x).compl))) =
      (holomorphicRingSheaf X d).obj.map
        (homOfLE ((inf_le_left : restrictedFlattened F V hqV ⊓
          (cycleComponentAnalyticClosedSupport X x).compl ≤
            restrictedFlattened F V hqV).trans
        (F.restrict_flattened_le V hqV |>.trans hV))).op
        (analyticFunction X d localForm.opens localForm.equation))
    (normalUnit : C((restrictedFlattened F V hqV : Set (ComplexPoint X)), ℂ))
    (normalUnit_ne_zero : ∀ y, normalUnit y ≠ 0)
    (hfactor : ∀ w : ChernWinding.puncturedSpace
        ((restrictedFlattened F V hqV : Set (ComplexPoint X)))
        (cycleComponentSupport X x),
      windingUnitFunction X d (restrictedFlattened F V hqV)
          (cycleComponentAnalyticClosedSupport X x)
          coord w =
        normalUnit (ChernWinding.flattenedPuncturedInclusion
            (S := cycleComponentSupport X x) (Fin (d - 1) → ℂ)
            (F.restrict V hqV).chart q (F.restrict V hqV).mem_source w) *
          ChernWinding.complexLineCoordinate
            ((ChernWinding.flattenedNormalProjection (Fin (d - 1) → ℂ)
              (F.restrict V hqV).chart (cycleComponentSupport X x)
              (F.restrict V hqV).flattens q (F.restrict V hqV).mem_source).left w)) :
    GenericWindingChartData X c x d q := by
  let F' := F.restrict V hqV
  let W := F'.flattened
  let hW : W ≤ analyticOpen X localForm.opens := F.restrict_flattened_le V hqV |>.trans hV
  refine {
    index := i
    localForm := localForm
    chart := F'.chart
    mem_source := F'.mem_source
    flattens := F'.flattens
    center := F'.center
    le := F'.le
    le_analytic := F.restrict_flattened_le V hqV |>.trans hV
    coord := coord
    coord_eq := hcoord
    exists_log := exists_log_of_flattening F'.chart F'.mem_source
    normalUnit := normalUnit
    normalUnit_ne_zero := normalUnit_ne_zero
    normal_coordinate := ?_
    coclass_restrict := fun hx => F'.coclass_restrict hx }
  intro w
  exact hfactor w

end FlatteningChartWithCoclass

end AlgebraicGeometry.ComplexPoint
