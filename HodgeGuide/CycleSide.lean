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

local instance analyticSupportHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)
```

# Cycles are indexed by generic points

The *coheight* of a point $`x` of a scheme is the codimension of its closure $`\overline{\{x\}}`,
an irreducible closed subset with generic point $`x`. An algebraic cycle is a locally finite
combination of points. The cycles whose points with a nonzero coefficient all lie in a given set
form a subgroup, and a codimension-$`p` cycle is a cycle whose points with a nonzero coefficient
have coheight $`p`. The formalization uses this description throughout, in place of a separate
type of subvarieties.

```lean -show
namespace Guide.Cycles.D1
```
```lean
def supported (X : Type*) [TopologicalSpace X] (Y : Type*) [AddGroup Y] (s : Set X) :
    AddSubgroup (Function.locallyFinsupp X Y) where
  carrier D := D.support ⊆ s
  zero_mem' _ h := (h rfl).elim
  add_mem' {a b} ha hb := (Function.support_add a b).trans (Set.union_subset ha hb)
  neg_mem' {a} ha := (Function.locallyFinsuppWithin.support_neg a).trans_subset ha
```
```lean -show
end Guide.Cycles.D1
example : @Guide.Cycles.D1.supported = @Function.locallyFinsupp.supported := rfl
```
```lean -show
namespace Guide.Cycles.D2
```
```lean
noncomputable abbrev codimSubgroup (X : Scheme.{u}) (R : Type*) [AddGroup R] (p : ℕ∞) :
    AddSubgroup (AlgebraicCycle X R) :=
  Function.locallyFinsupp.supported X R (coheight ⁻¹' {p})
```
```lean -show
end Guide.Cycles.D2
example : @Guide.Cycles.D2.codimSubgroup.{u} = @AlgebraicGeometry.AlgebraicCycle.codimSubgroup.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D3
```
```lean
open scoped Classical in
noncomputable def supported.single {X : Type*} [TopologicalSpace X] {Y : Type*} [AddGroup Y]
    {s : Set X} (x : X) (hx : x ∈ s) (y : Y) : Function.locallyFinsupp.supported X Y s :=
  ⟨Function.locallyFinsuppWithin.single x y,
    Function.locallyFinsupp.single_mem_supported.2 (Or.inr hx)⟩
```
```lean -show
end Guide.Cycles.D3
example : @Guide.Cycles.D3.supported.single = @Function.locallyFinsupp.supported.single := rfl
```
# The support of a subvariety

For a closed subset `S` of a scheme `X`, `X.reducedClosedSubscheme S` is the reduced closed
subscheme with underlying space `S`. For a point {lean}`x` of {lean}`X.left`,
{lean}`X.left.pointClosure x` is the case $`S = \overline{\{x\}}`: the integral closed subscheme
with generic point $`x`, and {name}`Scheme.pointClosureι` is its closed immersion into
{lean}`X.left`. The support of the subvariety in $`X(\mathbb C)` is the closed set of complex
points whose underlying scheme point lies in $`\overline{\{x\}}`.

```lean -show
namespace Guide.Cycles.D5
```
```lean
def reducedClosedSubscheme (X : Scheme) (S : Closeds X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal S).subscheme
```
```lean -show
end Guide.Cycles.D5
example : @Guide.Cycles.D5.reducedClosedSubscheme.{u} = @AlgebraicGeometry.Scheme.reducedClosedSubscheme.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D6
```
```lean
abbrev pointClosure (X : Scheme) (x : X) : Scheme :=
  X.reducedClosedSubscheme (Closeds.closure {x})
```
```lean -show
end Guide.Cycles.D6
example : @Guide.Cycles.D6.pointClosure.{u} = @AlgebraicGeometry.Scheme.pointClosure.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D7
```
```lean
def cycleComponentSupport (X : Over (Spec ↧ℂ)) (x : X.left) : Closeds (ComplexPoint X) :=
  (Closeds.closure {x}).preimage Point.continuous_underlying
```
```lean -show
end Guide.Cycles.D7
example : @Guide.Cycles.D7.cycleComponentSupport = @AlgebraicGeometry.ComplexPoint.cycleComponentSupport := rfl
```

```lean
#check AlgebraicGeometry.ComplexPoint.mem_cycleComponentSupport
```

Only the ambient variety is assumed smooth. A subvariety may be singular, and the construction of
its class in the next section handles that case from the start.

# Cohomology with support

Let $`Z\subseteq X(\mathbb C)` be closed, with open complement $`j:U\hookrightarrow X(\mathbb C)`.
Cohomology with support in $`Z` sits in the distinguished triangle

$$`R\Gamma_Z(X,\mathbb Q_X)\longrightarrow R\Gamma(X,\mathbb Q_X)
  \longrightarrow R\Gamma(U,\mathbb Q_U)\xrightarrow{+1}.`

The formalization builds the first term as a homotopy fibre. It resolves the constant sheaf
$`\underline{\mathbb Q}_U` injectively, pushes the resolution forward along $`j`, maps
$`\underline{\mathbb Q}_X` to the result, and takes the mapping cone shifted by $`-1`.
Hypercohomology of this complex is $`H^n_Z(X;\mathbb Q)`, and the connecting map of the triangle
is {name}`forgetSupport`, the map $`H^n_Z(X;\mathbb Q)\to H^n(X;\mathbb Q)`.

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
