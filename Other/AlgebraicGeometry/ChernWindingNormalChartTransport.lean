/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingGenericChartData

/-!
# Reducing `coclass_restrict` to germs on the support

The field `coclass_restrict` of `GenericWindingChartData` is an equality of *sections* of the
sheafified local relative-cohomology sheaf.  Off the support that sheaf has subsingleton stalks
(`AlgebraicTopology.Singular.supportRelativeCohomologySheaf_subsingleton_stalk`), so such an
equality only has to be checked at points **of the support**:

```lean
theorem AlgebraicTopology.Singular.supportRelativeCohomologySheaf_eq_toSheaf_of_germ …
```

`AlgebraicGeometry.ComplexPoint.coclass_restrict_of_germ` is the specialisation to the
component-coclass situation: `coclass_restrict` holds as soon as, at every point of the chart
lying on the component, the germ of the glued coclass section is the germ of the chart's
normal-projection coclass — which is exactly what the repository's
`smoothClosedSupportCoclassSection_germ_eq_normalCoclass` and
`smoothClosedSupportNormalCoclass_restrict_eq_chart` compute, upstairs along the open embedding
`cycleComponentSmoothClosedLiftAmbientMap`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order

namespace AlgebraicTopology.Singular

/-- A section of the local relative-cohomology sheaf is the sheafification of a relative class as
soon as their germs agree at the points of the support. -/
theorem supportRelativeCohomologySheaf_eq_toSheaf_of_germ
    (M : TopCat.{0}) (S : Set M) (hS : IsClosed S) (n : ℕ) (W : Opens M)
    (s : (supportRelativeCohomologySheaf M S n).obj.obj (op W))
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (W : Set M) S) n)
    (h : ∀ y, ∀ hy : y ∈ W, y ∈ S →
      (supportRelativeCohomologySheaf M S n).presheaf.germ W y hy s =
        supportRelativeCohomologyGerm M S n W y hy a) :
    s = (supportRelativeCohomologyToSheaf M S n).app (op W) a := by
  refine TopCat.Presheaf.section_ext _ W s _ fun y hy => ?_
  by_cases hyS : y ∈ S
  · exact h y hy hyS
  · have := supportRelativeCohomologySheaf_subsingleton_stalk M S n hS y hyS
    exact Subsingleton.elim _ _

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingNormalChartTransportTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X} (x : X.left) {d : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- **`coclass_restrict` reduces to germs on the component.**  The section equality required by
`GenericWindingChartData.coclass_restrict` follows from the corresponding germ equality at the
points of the chart that lie on the component. -/
theorem coclass_restrict_of_germ (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (W : Opens (ComplexPoint X)) (hW : W ≤ cycleComponentSmoothSupportAmbientOpen X x)
    (a : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair ((W : Set (ComplexPoint X)))
        (cycleComponentSupport X x)) (2 * 1))
    (h : ∀ y, ∀ hy : y ∈ W, y ∈ cycleComponentSupport X x →
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
          (cycleComponentSupport X x) (2 * 1)).presheaf.germ W y hy
          ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
            (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE hW).op
            (cycleComponentSmoothSupportCoclassSection X x (d := d) hx)) =
        supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
          (cycleComponentSupport X x) (2 * 1) W y hy a) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE hW).op
        (cycleComponentSmoothSupportCoclassSection X x (d := d) hx) =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).app (op W) a :=
  supportRelativeCohomologySheaf_eq_toSheaf_of_germ (TopCat.of (ComplexPoint X))
    (cycleComponentSupport X x) (cycleComponentAnalyticClosedSupport X x).isClosed (2 * 1) W _ a h

end AlgebraicGeometry.ComplexPoint
