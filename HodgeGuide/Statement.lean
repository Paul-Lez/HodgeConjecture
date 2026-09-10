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

#doc (Manual) "The statement" =>

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint
```

# The algebraic subspace

For every point `x : X.left` of coheight $`p`, the previous section gives a class

$$`\operatorname{cl}_X(\overline{\{x\}})\in H^{2p}(X;\mathbb Q).`

The algebraic subspace is the rational span of these classes:

$$`A^p(X)=\sum_{\operatorname{coht}(x)=p}
  \mathbb Q\,\operatorname{cl}_X(\overline{\{x\}}).`

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass
#check AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_mem_algebraicCycleClassSpan
```

In Lean the span is the supremum, over all points `x` and all proofs `hx : coheight x = p`, of the
line spanned by `cycleComponentSheafClass X x hx`, with the dimension argument set to
`dim X.left`.

# The proposition

Here is the full statement, elaborated when this page is built:

```lean
#print HodgeConjecture
```

It quantifies over a scheme `X` over $`\mathbb C` that is integral with smooth and projective
structure morphism, and over a natural number `p`. The conclusion is the inclusion of subspaces

$$`\operatorname{Hdg}^p(X;\mathbb Q)\le A^p(X):`

every rational Hodge class of degree $`2p` is a rational linear combination of classes of
algebraic subvarieties of codimension $`p`. This is the conjecture as Deligne states it,
[pp. 45–46](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56). The reverse
inclusion, that every algebraic class is a Hodge class, is a theorem that has not yet been
formalized, so the formulation as an equality $`\operatorname{Hdg}^p(X;\mathbb Q)=A^p(X)` is not
yet available.

# Why a span rather than a map on Chow groups

The repository defines `ChowGroup` and `RationalChowGroup`, and the classes of subvarieties give an
additive map on cycles. To descend this map to the Chow group, one must show that it vanishes on
every principal-divisor relation. The descent itself is formalized as a construction that takes
this vanishing as a hypothesis, but the vanishing has not been proved for the classes constructed
here.

```lean
#check AlgebraicGeometry.ChowGroup.cycleClassOfComponents
#check AlgebraicGeometry.ChowGroup.rationalCycleClassOfComponents
#check AlgebraicGeometry.ChowGroup.cycleClassOfComponents_mk
```

The span of the classes of subvarieties is exactly the image that the descended map would have,
so nothing is lost by using it. The statement says "rational linear combinations of classes of
subvarieties" without claiming a factorization through rational equivalence.

# Reading the source

The shortest route through the implementation is:

1. `HodgeConjecture/Statement.lean`, the statement;
2. `HodgeConjecture/Definitions/AlgebraicGeometry/HodgeFiltration.lean`, cohomology and the Hodge
   filtration;
3. `HodgeConjecture/Definitions/AlgebraicGeometry/CohomologyWithSupport.lean`, the mapping-cone
   model of cohomology with support;
4. `Other/AlgebraicGeometry/CycleComponentSmoothSupportCoclassSection.lean`, the class on the
   smooth locus;
5. `Other/AlgebraicGeometry/CycleComponentSupportExtension.lean`, its extension across the
   singular locus;
6. `Other/AlgebraicGeometry/CycleComponentSheafClass.lean`, the class of a subvariety;
7. `Other/AlgebraicGeometry/ComplexSheafBorelMoore.lean` and
   `ComplexSheafBorelMooreRationalComparison.lean`, Borel–Moore homology and duality;
8. `Other/AlgebraicGeometry/SheafCycleClass.lean`, the maps on cycles;
9. `Other/AlgebraicGeometry/ChowCycleClassDescent.lean`, descent to Chow groups.

Things to keep track of while reading: integer versus natural-number degrees, real versus complex
dimension, whether a class has been normalized, whether its support has been forgotten, and
whether a map is defined on cycles or on their quotient by rational equivalence.
