/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeConjecture.Statement
import Other.AlgebraicGeometry.ChowCycleClassDescent

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Assembling the statement" =>

# The algebraic subspace

For every point `x : X` of coheight $`p`, the preceding construction gives an ordinary class

$$`\operatorname{cl}_X(\overline{\{x\}})\in H^{2p}(X;\mathbb Q).`

The algebraic subspace is their rational span:

$$`A^p(X)=\sum_{\operatorname{coht}(x)=p}
  \mathbb Q\,\operatorname{cl}_X(\overline{\{x\}}).`

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass
#check AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_mem_algebraicCycleClassSpan
```

This is exactly the span of the values of the constructed map on individual components. It does
not use the older fallback of quantifying over elements that might generate the image of supported
cohomology.

# The proposition

Here is the complete Lean statement, elaborated while this page is built:

```lean
#print HodgeConjecture
```

It quantifies over an integral scheme `X`, a morphism to `Spec ℂ`, smoothness and projectivity of
that morphism, and `p : ℕ`. The conclusion is the submodule inclusion

$$`\operatorname{Hdg}^p(X;\mathbb Q)\le A^p(X).`

This is the difficult direction of the classical formulation: every rational Hodge class is a
rational combination of classes of algebraic subvarieties. Deligne develops the Hodge filtration,
the cycle-class construction, and this formulation in
[§1, especially pp. 45--46](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56).

# Why the statement uses a span rather than a Chow map

The repository already has the algebraic definitions of `ChowGroup` and `RationalChowGroup`, and
the component construction gives an additive map on cycles. To descend this map to the quotient,
one must prove that every principal-divisor relation maps to zero. The general descent interface is
present, but that geometric vanishing theorem is not yet proved for the new sheaf class.

```lean
#check AlgebraicGeometry.ChowGroup.cycleClassOfComponents
#check AlgebraicGeometry.ChowGroup.rationalCycleClassOfComponents
#check AlgebraicGeometry.ChowGroup.cycleClassOfComponents_mk
```

Using the span is therefore logically exact: it expresses “rational linear combinations of the
constructed component classes” without claiming a factorization through rational equivalence.

# Status ledger

The following is the shortest accurate summary of the development.

* *Constructed:* analytic complex points; the holomorphic de Rham complex and its constant-sheaf
  quasi-isomorphism; rational and de Rham hypercohomology; the truncation definition of $`F^p`;
  mapping-cone cohomology with support; scheme-theoretic component supports; normalized
  smooth-locus coclasses; purity and unique extension across arbitrary component singularities;
  actual ambient chain-sheaf Borel--Moore duality; component classes in every codimension; and
  additive/rational-linear maps on cycles.
* *Proved as a consistency theorem:* for a pure Hodge structure of weight $`2p`, a rational vector
  belongs to $`F^p` exactly when it has Hodge type `(p,p)`.
* *Not yet proved:* principal-divisor vanishing for the constructed map; the theorem that its
  values have Hodge type `(p,p)`; intrinsic compactification independence of the ambient-supported
  Borel--Moore group; and, of course, the conjectural inclusion itself.

# A productive source order

For the shortest route through the implementation, read:

1. `HodgeConjecture/Statement.lean`;
2. `Definitions/AlgebraicGeometry/HodgeFiltration.lean`;
3. `Definitions/AlgebraicGeometry/CohomologyWithSupport.lean`;
4. `Other/AlgebraicGeometry/CycleComponentSmoothSupportCoclassSection.lean`;
5. `Other/AlgebraicGeometry/CycleComponentSupportExtension.lean`;
6. `Other/AlgebraicGeometry/CycleComponentSheafClass.lean`;
7. `Other/AlgebraicGeometry/ComplexSheafBorelMoore.lean` and
   `ComplexSheafBorelMooreRationalComparison.lean`;
8. `Other/AlgebraicGeometry/SheafCycleClass.lean`;
9. `Other/AlgebraicGeometry/ChowCycleClassDescent.lean`.

The invariants to track are the integer shifts, real versus complex dimensions, exact local
normalization, whether support has been forgotten, and whether a map is on cycles or on their
rational-equivalence quotient.
