/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import Other.AlgebraicGeometry.CodimensionZeroCoclassNonvanishing

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
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
```

# The class to be constructed

Let $`X` be smooth of complex dimension $`d`, and let $`Z\subseteq X` be an irreducible closed
subvariety of codimension $`p`, with smooth locus $`Z_{\mathrm{reg}}` and singular locus
$`Z_{\mathrm{sing}}`. Near a point of $`Z_{\mathrm{reg}}`, holomorphic coordinates identify the pair
$`(X,Z)` with $`(\mathbb C^d,\mathbb C^{d-p})`, so the cohomology of $`X` with support in
$`Z_{\mathrm{reg}}` is locally one-dimensional in degree $`2p` and zero below. The complex structure
orients the normal directions, and the orientation picks out a generator, the Thom class of the
normal bundle. The class to be constructed is the global section of degree $`2p` that restricts to
that generator in every chart,

$$`\operatorname{cl}_X(Z)\in H^{2p}_Z(X;\mathbb Q),`

and then, after forgetting the support, in $`H^{2p}(X;\mathbb Q)`.

The choice of generator is the essential point. Purity alone says that the local cohomology with
support in degree $`2p` is one-dimensional, which fixes a line but not the multiplicity-one
generator that a cycle class map needs. The formalization fixes the generator chart by chart using
the complex orientation.

The whole construction stays in cohomology with support; no homology theory is involved, and the
statement of the conjecture does not depend on one. Goresky,
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
      (2 * p)).obj.obj (op ⊤) := by
  let := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hdeg := cycleComponentSmoothClosedLift_codimension X x hx
  exact hdeg ▸ smoothClosedSupportCoclassSection
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
#check AlgebraicGeometry.ComplexPoint.cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree
```

```lean -show
namespace Guide.Subvariety.D3
```
```lean
def cycleComponentSupportExtensionIso (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {p : ℕ}
    (hx : coheight x = p) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))) ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          (2 * (p : ℤ))) := by
  let := cycleComponentSupportSectionRestriction_homology_isIso X x hx
  exact asIso (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)))
```
```lean -show
end Guide.Subvariety.D3
example : @Guide.Subvariety.D3.cycleComponentSupportExtensionIso = @AlgebraicGeometry.ComplexPoint.cycleComponentSupportExtensionIso := rfl
```
```lean -show
namespace Guide.Subvariety.D4
```
```lean
def cycleComponentSupportedClassNormalizationIso (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {p : ℕ}
    (hx : coheight x = p) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))) ≅
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * p)).obj.obj
          (op (cycleComponentSmoothSupportAmbientOpen X x)) := by
  refine cycleComponentSupportExtensionIso X x hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx ≪≫ ?_
  let e := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapIso
        (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * p))
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  dsimp only [TopCat.Sheaf.supportEvaluation, Functor.comp_obj] at e
  rw [he] at e
  exact e
```
```lean -show
end Guide.Subvariety.D4
example : @Guide.Subvariety.D4.cycleComponentSupportedClassNormalizationIso = @AlgebraicGeometry.ComplexPoint.cycleComponentSupportedClassNormalizationIso := rfl
```

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedInjectiveClass_unique
```

The compact interface names the supported group and the smooth-locus section group.
The extension map takes any such section to its unique global supported class, using
the proved isomorphism above. Applying it to the normalized smooth-locus section gives
the component class.

```lean
#check AlgebraicGeometry.ComplexPoint.CycleComponentSupportedCohomology
#check AlgebraicGeometry.ComplexPoint.CycleComponentSmoothCoclassSections
#check AlgebraicGeometry.ComplexPoint.cycleComponentExtendSmoothCoclass
#check AlgebraicGeometry.ComplexPoint.cycleComponentExtendSmoothCoclass_normalization
#check AlgebraicGeometry.ComplexPoint.cycleComponentExtendSmoothCoclass_unique
```

```lean
example :
    CycleComponentSupportedCohomology X x p :=
  cycleComponentExtendSmoothCoclass X x hx
    (cycleComponentSmoothSupportCoclassSection X x hx)
```

# Step 3: from support to ordinary cohomology

The extension is a class in the cohomology of an injective resolution with supports. Transporting
it through the comparison with the mapping-cone model of the previous section gives the class of
the subvariety in cohomology with support, and forgetting the support gives its class in ordinary
cohomology, which is the class the statement uses.

```lean -show
namespace Guide.Subvariety.D5
```
```lean
def cycleComponentSheafSupportedClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {p : ℕ}
    (hx : coheight x = p) :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass X x hx)
```
```lean -show
end Guide.Subvariety.D5
example : @Guide.Subvariety.D5.cycleComponentSheafSupportedClass = @AlgebraicGeometry.ComplexPoint.cycleComponentSheafSupportedClass := rfl
```
```lean -show
namespace Guide.Subvariety.D6
```
```lean
def cycleComponentSheafClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {p : ℕ}
    (hx : coheight x = p) : H^(2 * (p : ℤ))(X; ℚ) :=
  forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (cycleComponentSheafSupportedClass X x hx)
```
```lean -show
end Guide.Subvariety.D6
example : @Guide.Subvariety.D6.cycleComponentSheafClass = @AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass := rfl
```

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_eq_forgetSupport
```

Both definitions take only the variety, the generic point, its coheight, and the dimension $`d` as
arguments.

For the generic point of $`X` itself, the support is all of $`X(\mathbb C)`, so forgetting support
is an isomorphism. The nonzero normalized section therefore gives a nonzero class in
$`H^0(X;\mathbb Q)` in every dimension, without assuming analytic connectedness.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_genericPoint_ne_zero
```
```lean -show
example : cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) ≠ 0 :=
  cycleComponentSheafClass_genericPoint_ne_zero X
```
