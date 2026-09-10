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

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
```

# Cycles are indexed by generic points

The *coheight* of a point $`x` of a scheme is the codimension of its closure $`\overline{\{x\}}`,
an irreducible closed subset with generic point $`x`. A codimension-$`p` cycle is a locally finite
integer combination of points of coheight $`p`. The formalization uses this description
throughout, in place of a separate type of subvarieties.

```lean
#check AlgebraicGeometry.CodimensionCycle
#check AlgebraicGeometry.CodimensionCycle.single
#check AlgebraicGeometry.ChowGroup
#check AlgebraicGeometry.RationalChowGroup
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

```lean
#check AlgebraicGeometry.cycleComponent
#check AlgebraicGeometry.cycleComponentι
#check AlgebraicGeometry.cycleComponentSupport
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

```lean
#check AlgebraicGeometry.ComplexPoint.rationalCohomologyWithSupportComplex
#check AlgebraicGeometry.ComplexPoint.RationalCohomologyWithSupport
#check AlgebraicGeometry.ComplexPoint.forgetSupport
```

For the triangle and the exact sequence of a pair see Goresky,
[§§7.14–7.15](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=31); for the derived-functor
description see the Stacks Project,
[§20.21](https://stacks.math.columbia.edu/tag/0A39).

# From subvarieties to cycles

Once every subvariety has a class, which is the subject of the next section, summing over the
components of a cycle with their multiplicities gives an additive map on integral cycles, and
extension of scalars gives a $`\mathbb Q`-linear map on rational cycles. The evaluation formulas
below hold for all integer and rational coefficients.

```lean
#check AlgebraicGeometry.ComplexPoint.sheafCycleClassOnCycles
#check AlgebraicGeometry.ComplexPoint.sheafCycleClassOnCycles_single
#check AlgebraicGeometry.ComplexPoint.rationalSheafCycleClassOnCycles
#check AlgebraicGeometry.ComplexPoint.rationalSheafCycleClassOnCycles_tmul_single
```

These maps take a {name}`DimensionedSmoothProjectiveComplexVariety`, a smooth projective variety
bundled with its dimension, which the construction of the class of a subvariety needs. The
constructor {name DimensionedSmoothProjectiveComplexVariety.ofOver}`ofOver` packages {lean}`X` with
{lean}`dim X.left` and the proof, from smoothness and integrality, that this is the relative
dimension of {lean}`X` over $`\mathbb C`. The statement does not use the bundle:
{name}`algebraicCycleClassSpan` evaluates each class at {lean}`dim X.left` directly.

```lean
#check AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety.ofOver
#check AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan
```

Whether these maps factor through rational equivalence is a separate question, taken up with the
statement.
