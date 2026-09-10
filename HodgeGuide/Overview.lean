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
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
noncomputable section
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
```

The conjecture concerns a smooth projective variety over $`\mathbb C`. In Lean such a variety is an
object {lean}`X` of the over category {lean}`Over (Spec ↧ℂ)`: a scheme {lean}`X.left` together with
its structure morphism {lean}`X.hom`, a morphism {lean}`X.left ⟶ Spec ↧ℂ`. The hypotheses are the
instance arguments {lean}`IsIntegral X.left`, {lean}`Smooth X.hom` and {lean}`IsProjective X.hom`.
A codimension is a natural number {lean}`p`, while cohomological degrees are integers, so the class
of a codimension-$`p` cycle lives in degree {lean}`2 * (p : ℤ)`; the coercion is visible in the
types below.

The statement is a single proposition, comparing two subspaces of rational cohomology. Here it is
as declared in `HodgeConjecture/Statement.lean`:

```lean -show
namespace Guide.Overview.D1
```
```lean
def HodgeConjecture : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ),
    Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p
```
```lean -show
end Guide.Overview.D1
example : @Guide.Overview.D1.HodgeConjecture = @HodgeConjecture := rfl
```

The two subspaces are the rational Hodge classes and the algebraic subspace. Their definitions,
whose ingredients the following sections explain, read:

```lean -show
namespace Guide.Overview.D2
```
```lean
def hodgeClasses (K : Type) [Field K] [Algebra K ℂ] (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) : Submodule K (FieldCohomology K X (2 * p)) :=
  ((hodgePiece X p p (2 * p)).restrictScalars K).comap
    (fieldToDeRhamCohomologyLinear K X (2 * p))
```
```lean -show
end Guide.Overview.D2
example : @Guide.Overview.D2.hodgeClasses = @AlgebraicGeometry.ComplexPoint.hodgeClasses := rfl
```
```lean -show
namespace Guide.Overview.D3
```
```lean
def algebraicCycleClassSpan (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) : Submodule ℚ (FieldCohomology ℚ X (2 * (p : ℤ))) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx}
```
```lean -show
end Guide.Overview.D3
example : @Guide.Overview.D3.algebraicCycleClassSpan = @AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan := rfl
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
   $`\Omega_X^{\ge p}`, transport complex conjugation to de Rham cohomology, and set
   $`H^{p,q}=F^p\cap\overline{F^q}`. The Hodge classes $`\operatorname{Hdg}^p(X;\mathbb Q)` are the
   rational classes of degree $`2p` whose image under the comparison map lies in $`H^{p,p}`; over
   $`\mathbb Q` this is the same as lying in $`F^p`.
3. Represent an irreducible subvariety $`Z\subseteq X` of codimension $`p` by its generic point, a
   point of the scheme {lean}`X.left` of coheight $`p`, and form the cohomology of $`X(\mathbb C)`
   with support in $`Z`.
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

The guide follows this order: steps 1 and 2 are the subject of {ref "hodge-classes"}[Hodge classes],
step 3 of {ref "cycles"}[Cycles and cohomology with support], steps 4 to 6 of
{ref "class-of-a-subvariety"}[The class of a subvariety], and step 7 of
{ref "the-statement"}[The statement].

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

One consistency theorem is proved, in two forms. For coefficients fixed by complex conjugation,
in particular over $`\mathbb Q`, the $`(p,p)` condition defining Hodge classes is equivalent to
lying in $`F^p` alone, which is how Deligne states the conjecture; and in an abstract pure Hodge
structure of weight $`2p`, a rational vector lies in $`F^p` if and only if it has type $`(p,p)`.

# Degree and support conventions

A complex manifold of complex dimension $`d` has real dimension $`2d`, and a subvariety $`Z` of
complex codimension $`p` has real dimension $`2(d-p)`. Alexander–Poincaré duality in the smooth
ambient space $`X` identifies

$$`H^{\mathrm{BM}}_{2(d-p)}(Z\subset X;\mathbb Q)
  \simeq H_Z^{2d-2(d-p)}(X;\mathbb Q)=H_Z^{2p}(X;\mathbb Q).`

This is the origin of the indices {lean}`2 * ((d - p : ℕ) : ℤ)` and {lean}`2 * (p : ℤ)` in the
code. A class with support in
$`Z` lies in $`H_Z^{2p}(X;\mathbb Q)`; the map {name}`forgetSupport` sends it to the ordinary group
$`H^{2p}(X;\mathbb Q)`, in which the conjecture is stated.
