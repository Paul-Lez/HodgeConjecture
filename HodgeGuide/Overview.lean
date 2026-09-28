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
  (d p : ℕ) (x : X.left) (hi : coheight x = p) (n : ℤ)
```

The conjecture concerns a smooth projective variety over $`\mathbb C`. In Lean such a variety is an
object {lean}`X` of the over category {lean}`Over (Spec ↧ℂ)`: a scheme {lean}`X.left` together with
its structure morphism {lean}`X.hom`, a morphism {lean}`X.left ⟶ Spec ↧ℂ`. The down arrow is the
bundling notation described in {ref "notation"}[Notation]: {lean}`(↧ℂ : CommRingCat)` is the field
$`\mathbb C` viewed as an object of {lean}`CommRingCat`, so {lean}`Spec ↧ℂ` is its spectrum. The
hypotheses are the instance arguments {lean}`IsIntegral X.left`, {lean}`Smooth X.hom` and
{lean}`IsProjective X.hom`.
The over category, the spectrum, integral schemes and smooth morphisms are Mathlib's;
projectivity and the complex points of {lean}`X` are defined in the repository, see
{ref "complex-points"}[The variety and its complex points].
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
    Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p
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
    [Smooth X.hom] (p : ℕ) : Submodule K (H^(2 * p)(X; K)) :=
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
    [IsProjective X.hom] (p : ℕ) : Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x hx}
```
```lean -show
end Guide.Overview.D3
example : @Guide.Overview.D3.algebraicCycleClassSpan = @AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan := rfl
```

Mathematically it is the inclusion

$$`\operatorname{Hdg}^p(X,\mathbb Q)
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
   $`H^{p,q}=F^p\cap\overline{F^q}`. The Hodge classes $`\operatorname{Hdg}^p(X,\mathbb Q)` are the
   rational classes of degree $`2p` whose image under the comparison map lies in $`H^{p,p}`; over
   $`\mathbb Q` this is the same as lying in $`F^p`.
3. Represent an irreducible subvariety $`Z\subseteq X` of codimension $`p` by its generic point, a
   point of the scheme {lean}`X.left` of coheight $`p`, and form the cohomology of $`X(\mathbb C)`
   with support in $`Z`.
4. On the smooth locus of $`Z`, the complex orientation of the normal directions singles out a
   generator in degree $`2p` chart by chart. These local generators agree on overlaps, so they
   glue — not to a cohomology class, but to a *section* of $`\mathcal H^{2p}_Z`, the sheafification
   of $`V\mapsto H^{2p}(V,V\setminus Z;\mathbb Q)`, over the complement of the singular locus.
5. Cross from that sheaf to the cohomology group. Restriction to the complement of
   $`Z_{\mathrm{sing}}` is bijective on $`H^{2p}_Z`, because $`Z_{\mathrm{sing}}` has codimension
   at least $`p+1` and so supports nothing in degrees $`2p` and $`2p+1`; and on that complement
   $`2p` is the lowest degree in which the cohomology sheaves of $`R\Gamma_Z\mathbb Q` are
   nonzero, which makes the group $`H^{2p}_Z` the group of sections of $`\mathcal H^{2p}_Z`.
   Together these identify the section of step 4 with a class in $`H^{2p}_Z(X;\mathbb Q)`, and
   forgetting the support gives $`\operatorname{cl}_X(Z)\in H^{2p}(X;\mathbb Q)`.
6. Extend $`\operatorname{cl}_X` additively to cycles and $`\mathbb Q`-linearly to rational cycles.
   The statement itself uses only the span of the classes of individual subvarieties.

The guide follows this order: steps 1 and 2 are the subject of {ref "hodge-classes"}[Hodge classes],
step 3 of {ref "cycles"}[Cycles and cohomology with support], steps 4 and 5 of
{ref "class-of-a-subvariety"}[The class of a subvariety], and step 6 of
{ref "the-statement"}[The statement].

The classes themselves live in cohomology, with support and then without; local homology enters
only to normalize the chart generators in step 4. `Other/` also builds a Borel–Moore homology of
the pair $`Z\subset X` and the duality that identifies the class above with a fundamental class,
but nothing in the statement passes through that, so this guide leaves it aside.

# Scope and status
%%%
tag := "scope-and-status"
%%%

Everything that enters the statement is constructed. The class of a subvariety of any codimension,
singular or not, is defined outright, with no hypotheses beyond the smoothness, projectivity, and
integrality of the ambient variety that the statement itself assumes.

Two cases of the conjecture itself are proved, both unconditionally, and both in
`Other/AlgebraicGeometry/`.

* Codimension zero. Every degree-zero class is a Hodge class, and the class of $`X` itself spans
  $`H^0(X;\mathbb Q)`, so $`\operatorname{Hdg}^0(X,\mathbb Q)=A^0(X)`. The two inputs are that
  the analytification of a smooth integral complex scheme is connected and that the constructed
  class of the whole variety is nonzero; both are proved here. The second is the useful one: it
  shows that the construction of
  {ref "class-of-a-subvariety"}[the class of a subvariety] does not return zero, which is the way
  a statement of this shape can hold for the wrong reason.
* Above the dimension. For $`p>\dim X` both sides are $`\bot`: there is no point of coheight
  $`p`, and the Hodge classes vanish because $`F^p` does. The inclusion is then vacuous, but it
  does check that the two sides degenerate in the same place.

The two cases together exhaust the codimensions exactly when $`\dim X=0`, and the repository draws
that corollary: the conjecture holds in every codimension for a smooth projective complex variety
of dimension zero. That is the one class of varieties for which it is settled here, and it is
settled for a trivial reason, since such a variety is a single point.

See {ref "what-is-proved"}[What the repository proves about the statement] for the declarations.

Three classical facts about the construction are not formalized. None is needed to state the
conjecture, but they are needed for the usual equivalent formulations, and the first is what
stands between the two cases above and the general one.

* Cohomological purity: $`H^{2p}_Z(X;\mathbb Q)` is the line on the fundamental class, so that
  forgetting support is injective on it and $`\operatorname{cl}_X(Z)\ne0` for every subvariety
  $`Z`. The normalized local section the class is built from is proved nonzero for every
  component; purity is what would carry that through to ordinary cohomology. Without it the span
  $`A^p(X)` is not known to be as large as the classes generating it suggest.
* The class of a subvariety is a Hodge class:
  $`\operatorname{cl}_X(Z)\in\operatorname{Hdg}^p(X,\mathbb Q)`. This is the reverse inclusion,
  and it is what would turn the statement into the usual equality.
* Compatibility of the two singular comparisons. Constant-sheaf cohomology is identified with
  singular cohomology in two settings: ordinary cohomology, by
  `rationalCohomologyLinearEquivSingularCohomology`, and cohomology with support in a closed set,
  by `rationalCohomologyWithSupportAddEquivSingular`. Both are constructed and proved to be
  isomorphisms, under point-set hypotheses that a projective variety satisfies. What is missing is
  the square these two isomorphisms form with the map forgetting support on each side. Until that
  square is known to commute, the class constructed here cannot be matched with the topologist's
  fundamental class in singular cohomology.

# Degree and support conventions
%%%
tag := "degree-and-support-conventions"
%%%

A subvariety $`Z` of codimension $`p` in a smooth variety $`X` of dimension $`d` has $`p` complex
normal directions, so its class sits in the cohomological degree $`2p` that the complex
orientation of those directions can generate. This is the origin of the index
{lean}`2 * (p : ℤ)` throughout the code; the complementary index
{lean}`2 * ((d - p : ℕ) : ℤ)`, the real dimension of $`Z`, appears wherever a construction is
indexed by $`Z` rather than by its codimension. A class with support in $`Z` lies in
$`H_Z^{2p}(X;\mathbb Q)`; the map {name}`forgetSupport` sends it to the ordinary group
$`H^{2p}(X;\mathbb Q)`, in which the conjecture is stated.

Alongside that group there is a sheaf, $`\mathcal H^n_Z` on $`X(\mathbb C)`, the sheafification of
$`V\mapsto H^n(V,V\setminus Z;\mathbb Q)`. Roman $`H` is always the group and script
$`\mathcal H` always the sheaf, here and in the source. The class of a subvariety is built in the
sheaf and only afterwards transported to the group, so the two should not be read as the same
thing; see {ref "class-of-a-subvariety"}[The class of a subvariety].

# Notation
%%%
tag := "notation"
%%%

The repository introduces a small set of notations, listed here once. Each is declared next to the
object it names. The cohomology notations are scoped to the `AlgebraicGeometry.ComplexPoint`
namespace, so they are in force only where that namespace is open; the down arrow and the constant
sheaf are global.

* `↧X` is the bundling map `FooCat.of X` of a concrete category, with `FooCat` read off from the
  expected type: {lean}`(↧ℂ : CommRingCat)` is `CommRingCat.of ℂ` and
  {lean}`(↧(ComplexPoint X) : TopCat)` is `TopCat.of (ComplexPoint X)`. The expected type must be
  known, which is why the notation is always used in a position that fixes it. It is copied from
  two pending Mathlib pull requests and kept under `HodgeConjecture/Mathlib/` until those land.
* `𝓒(T; R)` is the constant sheaf of additive groups on the space `T` with value `R`, and
  `𝓒[T; A]` the same for an object `A` of `AddCommGrpCat`.
* `Ω•(X)` is the holomorphic de Rham complex of `X`, indexed by the integers, and `F^p Ω•(X)` its
  stupid truncation in form degrees at least `p`.
* `ℍ^n(X; 𝒦)` is the hypercohomology of a complex of sheaves `𝒦`, and `H^n(X; K)` the case of the
  constant sheaf `K` in degree zero, that is, cohomology of $`X(\mathbb C)` with coefficients in
  `K`.
* `H_[Z]^n(X; ℚ)` is rational cohomology with support in a closed set `Z`.
* `F^p H_dR^n(X)` is the Hodge filtration on de Rham cohomology, and `Hdg^p(X; K)` the Hodge
  classes of codimension `p` with coefficients in `K`.

In the cohomology notations the literature would name the variety; the argument written here is
instead the object `X` of the over category, which carries the variety `X.left` together with its
map to $`\operatorname{Spec}\mathbb C`.
