/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing
import Other.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
import Other.AlgebraicGeometry.Cycle.FundamentalClass
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
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
  {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X) [IsIntegral Y.left] [IsClosedImmersion i.left]
  (hi : coheight (closedEmbeddingGenericPoint i) = p)
```

# The class to be constructed

Let $`X` be smooth of complex dimension $`d`, and let $`Z\subseteq X` be an irreducible closed
subvariety of codimension $`p`, with smooth locus $`Z_{\mathrm{reg}}` and singular locus
$`Z_{\mathrm{sing}}`.

Two distinct objects are called "cohomology with support" in this chapter, and the construction
moves from one to the other, so they are worth separating before anything else.

* The **group** $`H^n_Z(X;\mathbb Q)`, the cohomology of $`X(\mathbb C)` with support in
  $`Z(\mathbb C)`, built in {ref "cycles"}[Cycles and cohomology with support]. It is a single
  abelian group, and it is where the finished class lives. The same notation with an open
  $`U\subseteq X(\mathbb C)` in place of $`X` means the cohomology of $`U` with support in
  $`Z\cap U`.
* The **sheaf** $`\mathcal H^n_Z` on $`X(\mathbb C)`, the sheafification of the presheaf
  $`V\mapsto H^n(V,V\setminus Z;\mathbb Q)`. Relative cohomology is not a sheaf, so the
  sheafification is not a formality: a section of $`\mathcal H^n_Z` need not come from a single
  relative class. The sheaf is used through its sections $`\Gamma(U,\mathcal H^n_Z)` over an open
  $`U`, and through its stalks, which record the local picture at a point.

A section of the sheaf is not a class in the group, and the two are related only by a comparison
that must be proved. Step 1 builds a section, Step 2 proves the comparison and applies it, and
Step 3 forgets the support.

Near a point of $`Z_{\mathrm{reg}}`, holomorphic coordinates identify the pair $`(X,Z)` with
$`(\mathbb C^d,\mathbb C^{d-p})`. Classically the stalk of $`\mathcal H^{2p}_Z` at such a point is
one-dimensional and the stalks of $`\mathcal H^n_Z` vanish for $`n\ne2p`; the complex structure
orients the normal directions, and the orientation singles out a generator of that stalk, the Thom
class of the normal bundle. The vanishing off degree $`2p` is proved here, over all of
$`X(\mathbb C)\setminus Z_{\mathrm{sing}}(\mathbb C)`, and Step 2 uses it. One-dimensionality in
degree $`2p` is the ambient purity that is not formalized; see
{ref "scope-and-status"}[Scope and status].

The choice of generator is the essential point, and it is why the construction does not rest on
ambient purity. Purity would fix a line in the stalk, but a cycle class map needs the one generator
of that line that has multiplicity one. The formalization selects that generator chart by chart
from the complex orientation, without needing to know that the stalk is no larger than the line.

Local homology fixes the normalization, and it enters at one precise place. The generator of a
chart is *defined* as the unique relative cohomology class pairing to one with the local
fundamental homology class of that chart, carried across the universal-coefficient equivalence.
The modules under `AlgebraicTopology/LocalHomology/` are therefore in the statement's dependency
cone. What the construction does avoid is a duality theorem: the class is
assembled in cohomology with support throughout and never obtained as the dual of a homology
class of $`Z`. `Other/` builds a Borel–Moore homology of the pair $`Z\subset X` and the duality
identifying the two, but the statement does not pass through it. Goresky,
[§8.11](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=37), gives the topological picture of a
fundamental class this normalizes. Lee's
[Proposition 1.49](https://sites.math.washington.edu/~lee/Books/ICM/gsm-244-prev.pdf#page=32)
shows that a complex manifold carries a canonical orientation.

# Step 1: the class on the smooth locus

The smooth locus $`Z_{\mathrm{reg}}` is closed in the open set $`X\setminus Z_{\mathrm{sing}}`,
where it is a smooth closed immersion of relative dimension $`d-p`. Its codimension is recovered
as $`d-(d-p)=p`, which uses $`p\le d`, a consequence of smoothness; this is what makes the
natural-number subtraction in the types exact.

Each normal chart carries a relative cohomology class in degree $`2p`, the generator that the
orientation singles out. These classes agree where charts overlap, so their images in
$`\mathcal H^{2p}_Z` glue. What Step 1 delivers is therefore a section

$$`\Gamma\bigl(X(\mathbb C)\setminus Z_{\mathrm{sing}}(\mathbb C),\ \mathcal H^{2p}_Z\bigr),`

and not yet an element of any cohomology group. This is why the types below are sections of a
sheaf — {name}`supportRelativeCohomologySheaf` applied to an open — and not cohomology groups.

```lean -show
namespace Guide.Subvariety.D1
```
```lean
def closedEmbeddingSmoothClosedLiftCoclassSection {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [IsClosedImmersion i.left] {p : ℕ}
    (hi : coheight (closedEmbeddingGenericPoint i) = p) :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i)))
      (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
      (2 * p)).obj.obj (op ⊤) :=
  letI := closedEmbeddingSmoothLocusOver_hom_smoothOfRelativeDimension i hi
  have hdeg := closedEmbeddingSmoothClosedLift_codimension i hi
  hdeg ▸ smoothClosedSupportCoclassSection
    (closedEmbeddingSmoothLocusAmbientOpenOver i)
    (closedEmbeddingSmoothLocusOver i)
    (closedEmbeddingSmoothLocusClosedLiftOver i) (dim X.left - p) (dim X.left)
```
```lean -show
end Guide.Subvariety.D1
example : @Guide.Subvariety.D1.closedEmbeddingSmoothClosedLiftCoclassSection = @AlgebraicGeometry.ComplexPoint.closedEmbeddingSmoothClosedLiftCoclassSection := rfl
```
```lean -show
namespace Guide.Subvariety.D2
```
```lean
def closedEmbeddingSmoothSupportCoclassSection {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [IsClosedImmersion i.left] {p : ℕ}
    (hi : coheight (closedEmbeddingGenericPoint i) = p) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (closedEmbeddingSupport i) (2 * p)).obj.obj
      (op (closedEmbeddingSmoothSupportAmbientOpen i)) :=
  supportRelativeCohomologySectionOnOpen (closedEmbeddingSmoothClosedLiftAmbientMap i)
    (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i)
    (closedEmbeddingSupport i)
    (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
    (closedEmbeddingSmoothClosedLiftAmbientMap_support i)
    (2 * p) (closedEmbeddingSmoothSupportAmbientOpen i)
    (closedEmbeddingSmoothClosedLiftAmbientMap_imageOpen i)
    (closedEmbeddingSmoothClosedLiftCoclassSection i hi)
```
```lean -show
end Guide.Subvariety.D2
example : @Guide.Subvariety.D2.closedEmbeddingSmoothSupportCoclassSection = @AlgebraicGeometry.ComplexPoint.closedEmbeddingSmoothSupportCoclassSection := rfl
```

```lean
#check closedEmbeddingSmoothSupportCoclassSection_restrict
```

The restriction theorem says that on each chart the glued section is the class of that chart,
exactly and not merely up to a nonzero rational multiple.

This section is nonzero whenever the smooth support has a complex point. Every neighborhood of
that point contains a smaller normal chart, where the coclass evaluates to one on the normal
class. It therefore stays nonzero under restriction to any neighborhood of that point, giving a
nonzero germ and hence a nonzero glued section.

```lean
#check smoothClosedSupportCoclassSection_ne_zero
```

The smooth locus of a component always has a complex point, so this applies to every component,
in every codimension: the normalization does not silently produce zero anywhere.

```lean
#check closedEmbeddingSmoothSupportCoclassSection_ne_zero
```

Whether the resulting class in *ordinary* cohomology is nonzero is a different question, because
forgetting support may kill it. That step is settled only for the generic point, at the end of
this chapter, and in general it is cohomological purity; see
{ref "what-is-proved"}[What the repository proves about the statement].

# Step 2: from sections on the smooth locus to a global class

Write $`U=X(\mathbb C)\setminus Z_{\mathrm{sing}}(\mathbb C)`. Step 1 gave a section of
$`\mathcal H^{2p}_Z` over $`U`; the statement needs an element of $`H^{2p}_Z(X;\mathbb Q)`. The
two are identified by a composite of three isomorphisms, each for its own reason:

$$`H^{2p}_Z(X;\mathbb Q)
   \;\xrightarrow{\ \sim\ }\;H^{2p}_Z(U;\mathbb Q)
   \;\xrightarrow{\ \sim\ }\;\Gamma\bigl(U,\mathcal H^{2p}(R\Gamma_Z\mathbb Q)\bigr)
   \;\xrightarrow{\ \sim\ }\;\Gamma(U,\mathcal H^{2p}_Z).`

The first is restriction to $`U`, and it is what removes the singular locus from the problem.
$`Z_{\mathrm{sing}}` has a finite filtration by closed subsets whose successive differences are
smooth, each of codimension at least $`p+1` in $`X`, so cohomology supported on
$`Z_{\mathrm{sing}}` vanishes in degrees below $`2(p+1)`, in particular in $`2p` and $`2p+1`. The
long exact sequence of the nested supports $`Z_{\mathrm{sing}}\subseteq Z` then has zeros on both
sides of the restriction map.

```lean
#check closedEmbeddingSingularBoundarySectionCohomology_isZero_cycleDegree
```

The second passes from a cohomology group to a group of sections, and it is the step that purity
supplies. On $`U` the cohomology sheaves of $`R\Gamma_Z\mathbb Q` vanish in every degree other than
$`2p`, so $`2p` is the lowest degree in which they are nonzero. In that lowest degree the
cohomology of the sections over $`U` agrees with the sections of the cohomology sheaf, because no
lower degree contributes a correction.

```lean
#check closedEmbeddingSmoothRestrictedInjective_homology_isZero_of_ne
```

The third identifies $`\mathcal H^{2p}(R\Gamma_Z\mathbb Q)`, the cohomology sheaf of the supported
part of an injective resolution, with $`\mathcal H^{2p}_Z`, the sheafification of
$`V\mapsto H^{2p}(V,V\setminus Z;\mathbb Q)`. The comparison runs through the singular
resolution.

Of the two definitions quoted below, the first is the restriction isomorphism on its own and the
second is the whole composite, the normalization isomorphism
$`H^{2p}_Z(X;\mathbb Q)\cong\Gamma(U,\mathcal H^{2p}_Z)`. Its inverse extends a section on $`U`
uniquely across $`Z_{\mathrm{sing}}` to a class supported on all of $`Z`.

```lean -show
namespace Guide.Subvariety.D3
```
```lean
def closedEmbeddingSupportExtensionIso {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [IsClosedImmersion i.left] {p : ℕ}
    (hi : coheight (closedEmbeddingGenericPoint i) = p) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (closedEmbeddingAnalyticClosedSupport i))).homology (2 * (p : ℤ))) ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (closedEmbeddingSmoothSupportAmbientOpen i)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))).homology
          (2 * (p : ℤ))) :=
  letI := closedEmbeddingSupportSectionRestriction_homology_isIso i hi
  asIso (HomologicalComplex.homologyMap (closedEmbeddingSupportSectionRestriction i) (2 * (p : ℤ)))
```
```lean -show
end Guide.Subvariety.D3
example : @Guide.Subvariety.D3.closedEmbeddingSupportExtensionIso = @AlgebraicGeometry.ComplexPoint.closedEmbeddingSupportExtensionIso := rfl
```
```lean -show
namespace Guide.Subvariety.D4
```
```lean
def closedEmbeddingSupportedClassNormalizationIso {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
    [IsIntegral Y.left] [IsClosedImmersion i.left] {p : ℕ}
    (hi : coheight (closedEmbeddingGenericPoint i) = p) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (closedEmbeddingAnalyticClosedSupport i))).homology (2 * (p : ℤ))) ≅
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (closedEmbeddingSupport i) (2 * p)).obj.obj
          (op (closedEmbeddingSmoothSupportAmbientOpen i)) :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  closedEmbeddingSupportExtensionIso i hi ≪≫
    closedEmbeddingSmoothSupportLowestSectionCohomologyIso i hi ≪≫
      (he ▸ (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
        (closedEmbeddingSmoothSupportAmbientOpen i)).mapIso
          (complexSupportInjectiveCohomologySheafIsoRelative
            (closedEmbeddingAnalyticClosedSupport i) (2 * p)))
```
```lean -show
end Guide.Subvariety.D4
example : @Guide.Subvariety.D4.closedEmbeddingSupportedClassNormalizationIso = @AlgebraicGeometry.ComplexPoint.closedEmbeddingSupportedClassNormalizationIso := rfl
```

```lean
#check closedEmbeddingSupportedInjectiveClass_unique
```

The two ends of that isomorphism have short names, which keep the distinction visible in later
signatures: {name}`ClosedEmbeddingSupportedCohomology` is the group $`H^{2p}_Z(X;\mathbb Q)`, and
{name}`ClosedEmbeddingSmoothCoclassSections` is the group of sections
$`\Gamma(U,\mathcal H^{2p}_Z)`. Despite the shared word "cohomology", they are objects of
different kinds, and {name}`closedEmbeddingExtendSmoothCoclass`, the inverse of the normalization
isomorphism, is the only passage between them. Applying it to the normalized section of Step 1
gives the class of the component.

```lean
#check ClosedEmbeddingSupportedCohomology
#check ClosedEmbeddingSmoothCoclassSections
#check closedEmbeddingExtendSmoothCoclass
#check closedEmbeddingExtendSmoothCoclass_normalization
#check closedEmbeddingExtendSmoothCoclass_unique
```

```lean
example :
    ClosedEmbeddingSupportedCohomology i p :=
  closedEmbeddingExtendSmoothCoclass i hi
    (closedEmbeddingSmoothSupportCoclassSection i hi)
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
def closedEmbeddingSheafSupportedClass {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
    [IsIntegral Y.left] [IsClosedImmersion i.left] {p : ℕ}
    (hi : coheight (closedEmbeddingGenericPoint i) = p) :
    RationalCohomologyWithSupport X (closedEmbeddingSupport i) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (closedEmbeddingSupport i)
    (closedEmbeddingAnalyticClosedSupport i).isClosed (2 * (p : ℤ))).symm
      (closedEmbeddingSupportedInjectiveClass i hi)
```
```lean -show
end Guide.Subvariety.D5
example : @Guide.Subvariety.D5.closedEmbeddingSheafSupportedClass = @AlgebraicGeometry.ComplexPoint.closedEmbeddingSheafSupportedClass := rfl
```
```lean -show
namespace Guide.Subvariety.D6
```
```lean
def closedEmbeddingSheafClass {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
    [IsIntegral Y.left] [IsClosedImmersion i.left] {p : ℕ}
    (hi : coheight (closedEmbeddingGenericPoint i) = p) : H^(2 * (p : ℤ))(X; ℚ) :=
  forgetSupport X (closedEmbeddingSupport i) (2 * (p : ℤ))
    (closedEmbeddingSheafSupportedClass i hi)
```
```lean -show
end Guide.Subvariety.D6
example : @Guide.Subvariety.D6.closedEmbeddingSheafClass = @AlgebraicGeometry.ComplexPoint.closedEmbeddingSheafClass := rfl
```

```lean
#check closedEmbeddingSheafClass_eq_forgetSupport
```

Both definitions take only the variety, the generic point of the subvariety, and a proof that its
coheight is $`p`. No dimension is passed: the construction uses {lean}`dim X.left` internally.

For the generic point of $`X` itself, the support is all of $`X(\mathbb C)`, so forgetting support
is an isomorphism. The nonzero normalized section therefore gives a nonzero class in
$`H^0(X;\mathbb Q)` in every dimension, without assuming analytic connectedness.

```lean
#check closedEmbeddingSheafClass_genericPointEmbedding_ne_zero
```
```lean -show
example : closedEmbeddingSheafClass (genericPointEmbedding X)
    (coheight_genericPointEmbedding X) ≠ 0 :=
  closedEmbeddingSheafClass_genericPointEmbedding_ne_zero
```
