/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeConjecture.Statement

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Overview" =>

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint
```

The conjecture concerns a smooth projective variety over $`\mathbb C`. In Lean such a variety is an
object `X : Over (Spec ℂ)` of the over category: a scheme `X.left` together with its structure
morphism `X.hom : X.left ⟶ Spec ℂ`. The hypotheses are the instance arguments `IsIntegral X.left`,
`Smooth X.hom` and `IsProjective X.hom`. A codimension is a natural number `p`, while cohomological
degrees are integers, so the class of a codimension-$`p` cycle lives in degree `2 * (p : ℤ)`; the
coercion is visible in the types below.

The statement is a single proposition, comparing two subspaces of rational cohomology.

```lean
#check HodgeConjecture
#check AlgebraicGeometry.ComplexPoint.hodgeClasses
#check AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan
```

Mathematically it is the inclusion

$$`\operatorname{Hdg}^p(X;\mathbb Q)
  \subseteq
  \langle \operatorname{cl}_X(Z)\mid Z\subseteq X\text{ irreducible},
  \operatorname{codim}_X Z=p\rangle_{\mathbb Q}`

of the rational Hodge classes of degree $`2p` in the rational span of the classes of the
irreducible subvarieties of codimension $`p`.

# The construction in outline

1. Form the space $`X(\mathbb C)` of complex points with its analytic topology, and the holomorphic
   de Rham complex $`\Omega_X^\bullet` on it. Rational cohomology $`H^n(X;\mathbb Q)` and de Rham
   cohomology $`H^n_{\mathrm{dR}}(X)` are hypercohomology groups of sheaf complexes on
   $`X(\mathbb C)`, and the maps of complexes
   $`\underline{\mathbb Q}_X\to\underline{\mathbb C}_X\to\Omega_X^\bullet` induce a comparison map
   from the first to the second.
2. Define $`F^pH^n_{\mathrm{dR}}(X)` as the image of the hypercohomology of the truncated complex
   $`\Omega_X^{\ge p}`. The Hodge classes $`\operatorname{Hdg}^p(X;\mathbb Q)` are the rational
   classes of degree $`2p` whose image under the comparison map lies in $`F^p`.
3. Represent an irreducible subvariety $`Z\subseteq X` of codimension $`p` by its generic point, a
   point of the scheme `X.left` of coheight $`p`.
4. On the smooth locus of $`Z`, the complex orientation of the normal directions singles out a
   generator of the cohomology with support in $`Z` in degree $`2p`, locally in charts, and these
   local generators glue.
5. Extend the resulting class uniquely across the singular locus of $`Z`, which has codimension at
   least $`p+1`, so that its cohomology with support vanishes in degrees $`2p` and $`2p+1`.
   Forgetting the support gives $`\operatorname{cl}_X(Z)\in H^{2p}(X;\mathbb Q)`.
6. Identify the class with support with a fundamental class in Borel–Moore homology through the
   duality $`H^{\mathrm{BM}}_{2(d-p)}(Z\subset X;\mathbb Q)\simeq H^{2p}_Z(X;\mathbb Q)`, where
   $`d=\dim X`.
7. Extend $`\operatorname{cl}_X` additively to cycles and $`\mathbb Q`-linearly to rational cycles.
   The statement itself uses only the span of the classes of individual subvarieties.

Steps 1 and 2 are the subject of the section on Hodge classes, steps 3 to 6 of the two sections on
cycles, and step 7 of the section on the statement.

# Scope and status
%%%
tag := "scope-and-status"
%%%

Everything that enters the statement is constructed, for subvarieties of arbitrary codimension
and with arbitrary singularities. The class of a subvariety in cohomology with support, its image
in ordinary cohomology, and its Borel–Moore fundamental class are all defined in Lean from the
variety and the subvariety alone, with no hypotheses beyond smoothness, projectivity, and
integrality of the ambient variety.

Three classical facts about this construction are not yet formalized. None is needed to state the
conjecture, but they are needed for the usual equivalent formulations.

* The class of a subvariety is a Hodge class:
  $`\operatorname{cl}_X(Z)\in\operatorname{Hdg}^p(X;\mathbb Q)`. With it, the conjecture becomes
  the classical equality between the rational Hodge classes and the span of the algebraic classes.
* The map on cycles kills principal divisors, so that it descends to the rational Chow group
  $`\mathrm{CH}^p(X)_{\mathbb Q}`. Until then the statement uses the span of the classes of
  subvarieties rather than the image of a map out of the Chow group.
* The Borel–Moore homology used here is defined through the ambient space, as homology with
  support in $`Z`, and written $`H^{\mathrm{BM}}_i(Z\subset X;\mathbb Q)`. It has not been
  identified with an intrinsic Borel–Moore homology of $`Z`, independent of the embedding.

One consistency theorem is proved: in a pure Hodge structure of weight $`2p`, a rational vector
lies in $`F^p` if and only if it has Hodge type $`(p,p)`. This justifies defining Hodge classes
through the filtration alone.

# Degree and support conventions

A complex manifold of complex dimension $`d` has real dimension $`2d`, and a subvariety $`Z` of
complex codimension $`p` has real dimension $`2(d-p)`. Alexander–Poincaré duality in the smooth
ambient space $`X` identifies

$$`H^{\mathrm{BM}}_{2(d-p)}(Z\subset X;\mathbb Q)
  \simeq H_Z^{2d-2(d-p)}(X;\mathbb Q)=H_Z^{2p}(X;\mathbb Q).`

This is the origin of the indices `2 * (d - p)` and `2 * p` in the code. A class with support in
$`Z` lies in $`H_Z^{2p}(X;\mathbb Q)`; the map `forgetSupport` sends it to the ordinary group
$`H^{2p}(X;\mathbb Q)`, in which the conjecture is stated.
