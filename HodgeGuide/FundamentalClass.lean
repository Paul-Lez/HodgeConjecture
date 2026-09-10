/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import Other.AlgebraicGeometry.CycleComponentSheafClass

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "The class of a subvariety" =>

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
```

# The class to be constructed

Let $`X` be smooth of complex dimension $`d`, and let $`Z\subseteq X` be an irreducible closed
subvariety of codimension $`p`, with smooth locus $`Z_{\mathrm{reg}}` and singular locus
$`Z_{\mathrm{sing}}`. Near a point of $`Z_{\mathrm{reg}}`, holomorphic coordinates identify the pair
$`(X,Z)` with $`(\mathbb C^d,\mathbb C^{d-p})`, so the cohomology of $`X` with support in
$`Z_{\mathrm{reg}}` is locally one-dimensional in degree $`2p` and zero below. The complex structure
orients the normal directions, and the orientation picks out a generator, the Thom class of the
normal bundle. Under Alexander–Poincaré duality this generator corresponds to the fundamental class

$$`[Z]_{\mathrm{BM}}\in
  H^{\mathrm{BM}}_{2(d-p)}(Z\subset X;\mathbb Q).`

The choice of generator is the essential point. Purity alone says that the local cohomology with
support in degree $`2p` is one-dimensional, which fixes a line but not the multiplicity-one
generator that a cycle class map needs. The formalization fixes the generator chart by chart using
the complex orientation.

For the topology see Goresky, [§5.2](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=22), on
Borel–Moore homology and the orientation sheaf, and
[§8.11](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=37), on fundamental classes of
oriented pseudomanifolds. Lee's
[Proposition 1.49](https://sites.math.washington.edu/~lee/Books/ICM/gsm-244-prev.pdf#page=32)
shows that a complex manifold carries a canonical orientation.

# Step 1: the class on the smooth locus

The smooth locus $`Z_{\mathrm{reg}}` is closed in the open set $`X\setminus Z_{\mathrm{sing}}`,
where it is a smooth closed immersion of relative dimension $`d-p`. Its codimension is recovered
as $`d-(d-p)=p`, which uses $`p\le d`, a consequence of smoothness; this is what makes the
natural-number subtraction in the types exact. Normal charts give local classes in degree $`2p`,
these classes agree on overlaps, and they glue to a section of the sheaf of relative cohomology
over $`X\setminus Z_{\mathrm{sing}}`.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothClosedLiftCoclassSection
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection_restrict
```

The restriction theorem says that on each chart the glued section is the class of that chart,
exactly and not merely up to a nonzero rational multiple.

# Step 2: extension across the singular locus

The singular locus $`Z_{\mathrm{sing}}` has a finite filtration by closed subsets whose successive
differences are smooth. Each layer has codimension at least $`p+1` in $`X`, so its cohomology with
support vanishes in degrees below $`2(p+1)`, in particular in degrees $`2p` and $`2p+1`. The long
exact sequence for the nested supports $`Z_{\mathrm{sing}}\subseteq Z` then shows that restriction

$$`H_Z^{2p}(X;\mathbb Q)\longrightarrow
  H_{Z_{\mathrm{reg}}}^{2p}(X\setminus Z_{\mathrm{sing}};\mathbb Q)`

is an isomorphism. Its inverse extends the class of Step 1 uniquely to a class with support in
all of $`Z`.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportExtensionIso
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedClassNormalizationIso
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedInjectiveClass_unique
```

The extension is a class in the cohomology of an injective resolution with supports. Transporting
it through the comparison with the mapping-cone model of the previous section gives the class of
the subvariety in cohomology with support, and forgetting the support gives its class in ordinary
cohomology.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafSupportedClass
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_eq_forgetSupport
```

Both definitions take only the variety, the generic point, its coheight, and the dimension $`d` as
arguments.

# Step 3: the Borel–Moore fundamental class

The formalization also constructs the homological side. Let $`\mathcal C_X^{\mathrm{BM}}` be the
sheafification of the presheaf of relative singular chains on $`X(\mathbb C)`. On a smooth complex
$`d`-fold its local homology is concentrated in degree $`2d`, cohomological degree $`-2d`, and the
complex orientations give an isomorphism in the derived category

$$`\mathcal C_X^{\mathrm{BM}}\simeq \underline{\mathbb Q}_X[2d].`

Taking derived sections with support in $`Z` and then homology defines the Borel–Moore homology of
$`Z` relative to the ambient space, and the isomorphism above gives duality in every degree:

$$`H_i^{\mathrm{BM}}(Z\subset X;\mathbb Q)
  \simeq H_Z^{2d-i}(X;\mathbb Q).`

```lean
#check AlgebraicGeometry.ComplexPoint.ComplexAmbientSheafBorelMooreHomology
#check AlgebraicGeometry.ComplexPoint.complexChainSheafPlusOrientationIso
#check AlgebraicGeometry.ComplexPoint.complexAmbientSheafBorelMooreHomologyIso
#check AlgebraicGeometry.ComplexPoint.complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport
```

The fundamental class $`[Z]_{\mathrm{BM}}` is defined as the image of the class of Step 2 under
the inverse of this duality, in degree $`i=2(d-p)`. Two theorems confirm that it is the expected
object: duality sends $`[Z]_{\mathrm{BM}}` back to the class with support, and the route through
Borel–Moore homology to ordinary cohomology gives the same class $`\operatorname{cl}_X(Z)`.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafBorelMooreFundamentalClass
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafBorelMooreFundamentalClass_duality
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafBorelMooreFundamentalClass_toFieldCohomology
```

Textbooks usually go the other way, from the fundamental class to the cycle class. The order here
is equivalent and suits the available tools: the normalization is carried out where the local Thom
class lives, in cohomology with support, and then transported.

# What Borel–Moore homology means here

The group $`H_i^{\mathrm{BM}}(Z\subset X;\mathbb Q)` is defined through the ambient space, as
derived sections of the chain sheaf of $`X` with support in $`Z`. This makes sense for singular
$`Z` and needs no dualizing complex, but it is a theory of the pair $`Z\subset X`. That it does not
depend on the embedding, and agrees with the Borel–Moore homology of $`Z` defined through a
compactification, is not proved; see {ref "scope-and-status"}[Scope and status]. Goresky,
[§§12.4–12.5](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=59), gives the sheaf-theoretic
account of the Borel–Moore chain sheaf and the dualizing complex that the shift by $`2d` above
reflects.
