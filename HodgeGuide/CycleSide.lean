/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import Other.AlgebraicGeometry.SheafCycleClass

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
an irreducible closed subset with generic point $`x`. A codimension-$`p` cycle is a locally finite
integer combination of points of coheight $`p`. The formalization uses this description
throughout, in place of a separate type of subvarieties.

```lean -show
namespace Guide.Cycles.D1
```
```lean
abbrev CodimensionCycle (X : Scheme.{u}) (p : ℕ) := codimensionCycleSubgroup X p
```
```lean -show
end Guide.Cycles.D1
example : @Guide.Cycles.D1.CodimensionCycle.{u} = @AlgebraicGeometry.CodimensionCycle.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D2
```
```lean
noncomputable def CodimensionCycle.single {X : Scheme.{u}} {p : ℕ} (x : X) (hx : coheight x = p)
    (n : ℤ) : CodimensionCycle X p := by
  classical
  exact ⟨Function.locallyFinsuppWithin.single x n, by
    intro y hy
    by_cases h : y = x
    · simpa [h] using hx
    · simp [Function.locallyFinsuppWithin.single_apply, h] at hy⟩
```
```lean -show
end Guide.Cycles.D2
example : @Guide.Cycles.D2.CodimensionCycle.single.{u} = @AlgebraicGeometry.CodimensionCycle.single.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D3
```
```lean
abbrev ChowGroup (X : Scheme.{u}) (p : ℕ) :=
  CodimensionCycle X p ⧸ rationalEquivalenceSubgroup X p
```
```lean -show
end Guide.Cycles.D3
example : @Guide.Cycles.D3.ChowGroup.{u} = @AlgebraicGeometry.ChowGroup.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D4
```
```lean
noncomputable abbrev RationalChowGroup (X : Scheme.{u}) (p : ℕ) :=
  TensorProduct ℤ ℚ (ChowGroup X p)
```
```lean -show
end Guide.Cycles.D4
example : @Guide.Cycles.D4.RationalChowGroup.{u} = @AlgebraicGeometry.RationalChowGroup.{u} := rfl
```

Rational equivalence is defined in the usual way. For an integral Noetherian closed subscheme
$`W\subseteq X` of codimension $`p-1` and a nonzero rational function on $`W`, push the divisor of
the function forward to $`X`. The Chow group $`\mathrm{CH}^p(X)` is the quotient of the cycle
group by the subgroup these relations generate, and
$`\mathrm{CH}^p(X)_{\mathbb Q}=\mathbb Q\otimes_{\mathbb Z}\mathrm{CH}^p(X)`. Compare the Stacks
Project on [cycles of given codimension](https://stacks.math.columbia.edu/tag/0FE2) and on
[rational equivalence](https://stacks.math.columbia.edu/tag/02RW).

# The support of a subvariety

For a point {lean}`x` of {lean}`X.left`, {lean}`cycleComponent X.left x` is the reduced closed
subscheme with underlying space $`\overline{\{x\}}`, and {name}`cycleComponentι` is its closed
immersion into {lean}`X.left`. The
support of the subvariety in $`X(\mathbb C)` is the preimage of $`\overline{\{x\}}` under the map
from complex points to scheme points, and it is closed in the analytic topology.

```lean -show
namespace Guide.Cycles.D5
```
```lean
def cycleComponent (X : Scheme) (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subscheme
```
```lean -show
end Guide.Cycles.D5
example : @Guide.Cycles.D5.cycleComponent.{u} = @AlgebraicGeometry.cycleComponent.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D6
```
```lean
def cycleComponentι (X : Scheme) (x : X) : cycleComponent X x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι
```
```lean -show
end Guide.Cycles.D6
example : @Guide.Cycles.D6.cycleComponentι.{u} = @AlgebraicGeometry.cycleComponentι.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D7
```
```lean
def cycleComponentSupport (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) : Set (ComplexPoint X) :=
  Point.underlying ⁻¹' closure {x}
```
```lean -show
end Guide.Cycles.D7
example : @Guide.Cycles.D7.cycleComponentSupport = @AlgebraicGeometry.cycleComponentSupport := rfl
```

```lean
#check AlgebraicGeometry.isClosed_cycleComponentSupport
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
    RationalCohomologyWithSupport X Z n →+ FieldCohomology ℚ X n where
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
