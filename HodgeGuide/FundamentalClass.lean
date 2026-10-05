/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing
import Other.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
import Other.LinearAlgebra.HodgeStructure

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "The class of a subvariety" =>
%%%
tag := "class-of-a-subvariety"
%%%

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
noncomputable section
open CategoryTheory.Limits Opposite AlgebraicTopology.Singular
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
```

# The class to be constructed

Let $`X` be smooth of complex dimension $`d`, and let $`Z\subseteq X` be an irreducible closed
subvariety of codimension $`p`, with smooth locus $`Z_{\mathrm{reg}}` and singular locus
$`Z_{\mathrm{sing}}`. Near a point of $`Z_{\mathrm{reg}}`, holomorphic coordinates identify the pair
$`(X,Z)` with $`(\mathbb C^d,\mathbb C^{d-p})`; this is the geometric picture behind the
degree-$`2p` local coclass. The formalization proves the required off-degree vanishing and uses
normal charts to construct the coclass, but does not assert the stronger local one-dimensionality
statement as a theorem. The complex structure orients the normal directions, and the orientation
picks out a normalized Thom coclass. The class to be constructed is the global section of degree
$`2p` that restricts to that normalized coclass in every chart,

$$`\operatorname{cl}_X(Z)\in H^{2p}_Z(X;\mathbb Q),`

and then, after forgetting the support, in $`H^{2p}(X;\mathbb Q)`.

The choice of normalized coclass is the essential point. A full purity theorem would identify the local
degree-$`2p` group with a line, but that identification is not currently formalized here. The
formalization fixes the normalized coclass chart by chart using the complex orientation.

The class itself is a supported cohomology class, while its normalization uses the local-homology
construction that produces the normal orientation class. The statement of the conjecture does not
depend on that implementation detail. Goresky,
[§8.11](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=37), gives the topological picture of a
fundamental class this normalizes. Lee's
[Proposition 1.49](https://sites.math.washington.edu/~lee/Books/ICM/gsm-244-prev.pdf#page=32)
shows that a complex manifold carries a canonical orientation.

# Step 1: the class on the smooth locus

The smooth locus $`Z_{\mathrm{reg}}` is closed in the open set $`X\setminus Z_{\mathrm{sing}}`,
where it is a smooth closed immersion of relative dimension $`d-p`. Its codimension is recovered
as $`d-(d-p)=p`, which uses $`p\le d`, a consequence of smoothness; this is what makes the
natural-number subtraction in the types exact. Normal charts give local classes in degree $`2p`,
these classes agree on overlaps, and they glue to a section of the sheaf of relative cohomology
over $`X\setminus Z_{\mathrm{sing}}`.

```lean -show
namespace Guide.Subvariety.D1
```
```lean
def cycleComponentSmoothClosedLiftCoclassSection (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {p : ℕ}
    (hx : coheight x = p) :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (2 * p)).obj.obj (op ⊤) :=
  letI := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hdeg := cycleComponentSmoothClosedLift_codimension X x hx
  hdeg ▸ smoothClosedSupportCoclassSection
    (cycleComponentSmoothLocusAmbientOpenOver X x)
    (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (dim X.left - p) (dim X.left)
```
```lean -show
end Guide.Subvariety.D1
example : @Guide.Subvariety.D1.cycleComponentSmoothClosedLiftCoclassSection = @AlgebraicGeometry.ComplexPoint.cycleComponentSmoothClosedLiftCoclassSection := rfl
```
```lean -show
namespace Guide.Subvariety.D2
```
```lean
def cycleComponentSmoothSupportCoclassSection (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {p : ℕ}
    (hx : coheight x = p) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * p)).obj.obj
      (op (cycleComponentSmoothSupportAmbientOpen X x)) :=
  supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x hx)
```
```lean -show
end Guide.Subvariety.D2
example : @Guide.Subvariety.D2.cycleComponentSmoothSupportCoclassSection = @AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection := rfl
```

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection_restrict
```

The restriction theorem says that on each chart the glued section is the class of that chart,
exactly and not merely up to a nonzero rational multiple.

This section is nonzero whenever the smooth support has a complex point. Every neighborhood of
that point contains a smaller normal chart, where the coclass evaluates to one on the normal
class. It therefore stays nonzero under restriction to any neighborhood of that point, giving a
nonzero germ and hence a nonzero glued section.

```lean
#check AlgebraicGeometry.ComplexPoint.smoothClosedSupportCoclassSection_ne_zero
```

The smooth locus of a component always has a complex point, so this applies to every component,
in every codimension: the normalization does not silently produce zero anywhere.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection_ne_zero
```

Whether the resulting class in *ordinary* cohomology is nonzero is a different question, because
forgetting support may kill it. That step is settled only for the generic point, at the end of
this chapter, and in general it is cohomological purity; see
{ref "what-is-proved"}[What the repository proves about the statement].

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
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportExtensionIso
```

The current interface exposes the extension as an additive equivalence on supported cohomology,
and the normalization as an additive equivalence from supported classes to smooth-locus coclass
sections. Their concrete injective-resolution models remain implementation details.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportExtensionIso
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedClassNormalizationIso
```

```lean
```

The compact interface names the supported group and the smooth-locus section group.
The extension map takes any such section to its unique global supported class, using
the proved isomorphism above. Applying it to the normalized smooth-locus section gives
the component class.

```lean
#check AlgebraicGeometry.ComplexPoint.CycleComponentSupportedCohomology
#check AlgebraicGeometry.ComplexPoint.CycleComponentSmoothCoclassSections
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedInjectiveClass
```

```lean
example :
    CycleComponentSupportedCohomology X x p :=
  cycleComponentSupportedInjectiveClass X x hx
```

# Step 3: from support to ordinary cohomology

The supported class is transported through the canonical support-forgetting map to ordinary
hypercohomology, which is the class used by the statement.

```lean -show
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedInjectiveClass
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass
```
```lean
example : cycleComponentSheafClass X x hx =
    forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) (2 * p)
      (cycleComponentSupportedInjectiveClass X x hx) := rfl
```

These definitions take the variety, the generic point, and its coheight proof as arguments; the
cohomological degree $`2p` is determined by the codimension, with no independent dimension
parameter.

For the generic point of $`X` itself, the support is all of $`X(\mathbb C)`, so the public
support-forgetting map is injective. The nonzero normalized section therefore gives a nonzero class in
$`H^0(X;\mathbb Q)` in every dimension, without assuming analytic connectedness.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_genericPoint_ne_zero
```
```lean -show
example : cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) ≠ 0 :=
  cycleComponentSheafClass_genericPoint_ne_zero X
```
