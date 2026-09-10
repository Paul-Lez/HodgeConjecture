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
%%%
tag := "class-of-a-subvariety"
%%%

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
noncomputable section
open CategoryTheory.Limits Opposite AlgebraicTopology.Singular
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)

local instance complexSheafBorelMooreSheafDerivedCategory (X : Over (Spec ↧ℂ)) : HasDerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _
local instance complexSheafBorelMooreGroupsDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _
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

```lean -show
namespace Guide.Subvariety.D1
```
```lean
def cycleComponentSmoothClosedLiftCoclassSection (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : coheight x = p) :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (2 * p)).obj.obj (op ⊤) := by
  let := cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x (d := d) hx
  have hdeg := cycleComponentSmoothClosedLift_codimension X x (d := d) hx
  exact hdeg ▸ smoothClosedSupportCoclassSection
    (cycleComponentSmoothLocusAmbientOpenOver X x)
    (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (d - p) d
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
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
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
    (cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx)
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
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : coheight x = p) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))) ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          (2 * (p : ℤ))) := by
  let := cycleComponentSupportSectionRestriction_homology_isIso X x (d := d) hx
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
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : coheight x = p) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))) ≅
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * p)).obj.obj
          (op (cycleComponentSmoothSupportAmbientOpen X x)) := by
  refine cycleComponentSupportExtensionIso X x (d := d) hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x (d := d) hx ≪≫ ?_
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

The extension is a class in the cohomology of an injective resolution with supports. Transporting
it through the comparison with the mapping-cone model of the previous section gives the class of
the subvariety in cohomology with support, and forgetting the support gives its class in ordinary
cohomology.

```lean -show
namespace Guide.Subvariety.D5
```
```lean
def cycleComponentSheafSupportedClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : coheight x = p) :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass X x (d := d) hx)
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
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : coheight x = p) : FieldCohomology ℚ X (2 * (p : ℤ)) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).symm
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
        (ambientRationalInjectiveComplex X)).f (2 * (p : ℤ))
      (cycleComponentSupportedInjectiveClass X x (d := d) hx))
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

```lean -show
namespace Guide.Subvariety.D7
```
```lean
def ComplexAmbientSheafBorelMooreHomology (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    (Z : Closeds (ComplexPoint X)) (i : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (-i)).obj
    (complexAmbientSheafBorelMooreObject X d Z)
```
```lean -show
end Guide.Subvariety.D7
example : @Guide.Subvariety.D7.ComplexAmbientSheafBorelMooreHomology = @AlgebraicGeometry.ComplexPoint.ComplexAmbientSheafBorelMooreHomology := rfl
```
```lean -show
namespace Guide.Subvariety.D8
```
```lean
def complexChainSheafPlusOrientationIso (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)] :
    complexChainSheafPlusObject X d ≅
      (complexConstantRationalSheafPlusObject X)⟦2 * (d : ℤ)⟧ :=
  complexChainSheafPlusIsoOfOrientation X d
    (complexOrientationHomologySheafIso X d).symm
```
```lean -show
end Guide.Subvariety.D8
example : @Guide.Subvariety.D8.complexChainSheafPlusOrientationIso = @AlgebraicGeometry.ComplexPoint.complexChainSheafPlusOrientationIso := rfl
```
```lean -show
namespace Guide.Subvariety.D9
```
```lean
def complexAmbientSheafBorelMooreHomologyIso (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    (Z : Closeds (ComplexPoint X)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology X d Z i ≅
      ComplexDerivedSupportedCohomology X Z (2 * (d : ℤ) - i) :=
  complexAmbientSheafBorelMooreHomologyIsoOfOrientation X d
    (complexOrientationHomologySheafIso X d).symm Z i
```
```lean -show
end Guide.Subvariety.D9
example : @Guide.Subvariety.D9.complexAmbientSheafBorelMooreHomologyIso = @AlgebraicGeometry.ComplexPoint.complexAmbientSheafBorelMooreHomologyIso := rfl
```
```lean -show
namespace Guide.Subvariety.D10
```
```lean
def complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    (Z : Closeds (ComplexPoint X)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology X d Z
        (2 * ((d - p : ℕ) : ℤ)) ≃+
      RationalCohomologyWithSupport X Z (2 * (p : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeIso X d Z p hp).addCommGroupIsoToAddEquiv.trans
    (complexDerivedSupportedCohomologyAddEquivRationalSupport X Z (2 * (p : ℤ)))
```
```lean -show
end Guide.Subvariety.D10
example : @Guide.Subvariety.D10.complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport = @AlgebraicGeometry.ComplexPoint.complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport := rfl
```

The fundamental class $`[Z]_{\mathrm{BM}}` is defined as the image of the class of Step 2 under
the inverse of this duality, in degree $`i=2(d-p)`. Two theorems confirm that it is the expected
object: duality sends $`[Z]_{\mathrm{BM}}` back to the class with support, and the route through
Borel–Moore homology to ordinary cohomology gives the same class $`\operatorname{cl}_X(Z)`.

```lean -show
namespace Guide.Subvariety.D11
```
```lean
def cycleComponentSheafBorelMooreFundamentalClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : coheight x = p) :
    ComplexAmbientSheafBorelMooreHomology X d (cycleComponentAnalyticClosedSupport X x)
      (2 * ((d - p : ℕ) : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
    (cycleComponentAnalyticClosedSupport X x) p
    (cycleComponentSheafClass_codimension_le X x (d := d) hx)).symm
      (cycleComponentSheafSupportedClass X x (d := d) hx)
```
```lean -show
end Guide.Subvariety.D11
example : @Guide.Subvariety.D11.cycleComponentSheafBorelMooreFundamentalClass = @AlgebraicGeometry.ComplexPoint.cycleComponentSheafBorelMooreFundamentalClass := rfl
```

```lean
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
