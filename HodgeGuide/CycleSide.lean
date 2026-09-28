/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import Other.AlgebraicGeometry.Cycle.SheafClass

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Cycles and cohomology with support" =>
%%%
tag := "cycles"
%%%

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
noncomputable section
universe u
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
  {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X) [IsIntegral Y.left] [IsClosedImmersion i.left]
  (hi : dim Y.left + p = dim X.left)

local instance analyticSupportHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)
```

# From cycle points to closed subvarieties

A codimension-$`p` cycle is a locally finite integer combination of scheme points of coheight
$`p`. The subgroup {name}`AlgebraicCycle.codimSubgroup` retains this indexing.

```lean
#check AlgebraicCycle.codimSubgroup
#check Function.locallyFinsupp.supported.single
```

The geometric construction accepts an integral scheme {lean}`Y` and a closed immersion
{lean}`i`. Its codimension is specified by {lean}`hi`: the source dimension plus {lean}`p`
is the ambient dimension. Only the ambient variety is assumed smooth.

# The support of a subvariety

The support is the image on complex points, bundled with its analytic closedness proof.

```lean -show
namespace Guide.Cycles.Support
```
```lean
def closedEmbeddingSupport {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
    [IsClosedImmersion i.left] : Closeds (ComplexPoint X) :=
  ⟨Set.range (Point.map i), ComplexPoint.isClosed_range_map_of_closedImmersion i⟩
```
```lean -show
end Guide.Cycles.Support
example : @Guide.Cycles.Support.closedEmbeddingSupport =
    @AlgebraicGeometry.closedEmbeddingSupport := rfl
```

The theorem below tests membership through underlying scheme points. Its two sides are sets
of complex points.

```lean
#check closedEmbeddingSupport_eq_preimage
#check closedEmbedding_coheight_eq_iff
```

To evaluate a point-indexed cycle, {name}`CycleComponent.ι` supplies the closed immersion of
{name}`Scheme.pointClosure`. The fundamental-class construction itself takes the immersion.

```lean
#check Scheme.reducedClosedSubscheme
#check Scheme.pointClosure
#check CycleComponent.ι
#check CycleComponent.dim_add_codimension
```

# Cohomology with support

Let $`Z\subseteq X(\mathbb C)` be closed, with open complement $`j:U\hookrightarrow X(\mathbb C)`.
Cohomology with support in $`Z` sits in the distinguished triangle

$$`R\Gamma_Z(X,\mathbb Q_X)\longrightarrow R\Gamma(X,\mathbb Q_X)
  \longrightarrow R\Gamma(U,\mathbb Q_U)\xrightarrow{+1}.`

The formalization builds the first term as a homotopy fibre. It resolves the constant sheaf
$`\underline{\mathbb Q}_U` injectively, pushes the resolution forward along $`j`, maps
$`\underline{\mathbb Q}_X` into the result, and takes the mapping cone of that map. The fibre is
the cone shifted by $`-1`, but the complex itself is left unshifted and the shift is carried in
the degree instead: $`H^n_Z(X;\mathbb Q)` is the hypercohomology of the cone in degree $`n-1`,
which is the `n - 1` in the second definition below. The group has its own notation,
`H_[Z]^n(X; ℚ)`.

Forgetting support is the first map of the displayed triangle. In the mapping-cone picture it is
the cone's connecting morphism to $`\underline{\mathbb Q}_X[1]`, and composing a class of degree
$`n-1` in the cone with that morphism gives a class in degree $`n` of the ambient complex. The
composite is {name}`forgetSupport`, the map $`H^n_Z(X;\mathbb Q)\to H^n(X;\mathbb Q)`.

```lean -show
namespace Guide.Cycles.D8
```
```lean
abbrev rationalCohomologyWithSupportComplex (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.mappingCone (rationalRestrictionComplexInt X Z)
```
```lean -show
end Guide.Cycles.D8
example : @Guide.Cycles.D8.rationalCohomologyWithSupportComplex = @AlgebraicGeometry.ComplexPoint.rationalCohomologyWithSupportComplex := rfl
```
```lean -show
namespace Guide.Cycles.D9
```
```lean
abbrev RationalCohomologyWithSupport (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (n : ℤ) :
    Type 1 :=
  Hypercohomology X (rationalCohomologyWithSupportComplex X Z) (n - 1)
```
```lean -show
end Guide.Cycles.D9
example : @Guide.Cycles.D9.RationalCohomologyWithSupport = @AlgebraicGeometry.ComplexPoint.RationalCohomologyWithSupport := rfl
```
```lean -show
namespace Guide.Cycles.D10
```
```lean
def forgetSupport (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (n : ℤ) :
    RationalCohomologyWithSupport X Z n →+ H^n(X; ℚ) where
  toFun α := α.comp (forgetSupportShiftedHom X Z) (by lia)
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.zero_comp]
  map_add' α β := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add, ShiftedHom.add_comp]
```
```lean -show
end Guide.Cycles.D10
example : @Guide.Cycles.D10.forgetSupport = @AlgebraicGeometry.ComplexPoint.forgetSupport := rfl
```

For the triangle and the exact sequence of a pair see Goresky,
[§§7.14–7.15](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=31); for the derived-functor
description see the Stacks Project,
[§20.21](https://stacks.math.columbia.edu/tag/0A39).
