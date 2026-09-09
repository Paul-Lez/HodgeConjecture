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

#doc (Manual) "The normalized component class and its Borel--Moore dual" =>

# The mathematical target

Let $`X` be smooth of complex dimension $`d`, and let $`Z` be an irreducible component of
codimension $`p`. On the smooth locus $`Z_{\mathrm{reg}}`, complex coordinates canonically orient
the normal directions. The associated local Thom coclass has degree $`2p`. Equivalently, under
Alexander--Poincaré duality it corresponds to the top Borel--Moore class

$$`[Z]_{\mathrm{BM}}\in
  H^{\mathrm{BM}}_{2(d-p)}(Z\subset X;\mathbb Q).`

The normalization is essential. Merely knowing that a critical local group is one-dimensional
determines only a line; it does not choose the multiplicity-one generator needed for a cycle-class
map. The code fixes the generator chart by chart using the complex orientation.

For the topology behind this construction, see Goresky
[§§5.2--5.3](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=21) on Borel--Moore chains and local
orientations, and
[§§8.10--8.11](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=36) on fundamental classes of
oriented pseudomanifolds. Lee's
[Proposition 1.49](https://sites.math.washington.edu/~lee/Books/ICM/gsm-244-prev.pdf#page=32)
proves that a complex manifold has the canonical real orientation used in the normalization.

# Step 1: build the normalized class on the smooth locus

The component's smooth locus is realized as a smooth closed immersion into the complement of its
singular boundary. Its relative dimension is $`d-p`; the proof that
$`d-(d-p)=p` uses the coheight bound supplied by smoothness rather than truncated subtraction by
fiat. Normal charts provide local coclasses, and their compatibility glues them to a section of
the relative-cohomology sheaf on that open set.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothClosedLiftCoclassSection
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection_restrict
```

The restriction theorem records exact equality with the chart coclass. This is stronger than
nonvanishing or agreement up to an unspecified rational scalar.

# Step 2: extend uniquely across the singular boundary

The singular boundary is filtered by finitely many smooth locally closed layers. Every layer has
codimension at least $`p+1`, so its supported cohomology vanishes below $`2(p+1)`. In particular,
the groups in degrees $`2p` and $`2p+1` vanish. The long exact localization sequence for nested
supports therefore makes restriction

$$`H_Z^{2p}(X;\mathbb Q)\longrightarrow
  H_{Z_{\mathrm{reg}}}^{2p}(X\setminus Z_{\mathrm{sing}};\mathbb Q)`

an isomorphism. Its inverse is the unique extension operation used by the definition.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportExtensionIso
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedClassNormalizationIso
#check AlgebraicGeometry.ComplexPoint.cycleComponentSupportedInjectiveClass_unique
```

After transport through the proved injective-resolution and restriction-cone comparison, this
gives the public supported class and then the ordinary class obtained by forgetting support.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafSupportedClass
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_eq_forgetSupport
```

No fundamental-class, orientation, purity, extension, or vanishing structure occurs as an argument
to these definitions.

# Step 3: recover the ambient Borel--Moore fundamental class

The implementation also constructs the chain-sheaf side. Let $`\mathcal C_X^{\mathrm{BM}}` be the
sheafification of relative singular chains. Its local homology on a smooth complex $`d`-fold is
concentrated in cohomological degree $`-2d`. The exact local complex orientations give a derived
isomorphism

$$`\mathcal C_X^{\mathrm{BM}}\simeq \mathbb Q_X[2d].`

Applying actual derived sections with closed support $`Z` and taking homology yields, in every
integer degree,

$$`H_i^{\mathrm{BM}}(Z\subset X;\mathbb Q)
  \simeq H_Z^{2d-i}(X;\mathbb Q).`

```lean
#check AlgebraicGeometry.ComplexPoint.ComplexAmbientSheafBorelMooreHomology
#check AlgebraicGeometry.ComplexPoint.complexChainSheafPlusOrientationIso
#check AlgebraicGeometry.ComplexPoint.complexAmbientSheafBorelMooreHomologyIso
#check AlgebraicGeometry.ComplexPoint.complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport
```

The formal construction first obtains the normalized supported coclass, then applies the inverse of
this normalized duality to define its Borel--Moore fundamental class. The two following theorems
show that duality returns the supported class exactly and that the resulting cycle-class route
lands at the same ordinary class.

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafBorelMooreFundamentalClass
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafBorelMooreFundamentalClass_duality
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafBorelMooreFundamentalClass_toFieldCohomology
```

This order is mathematically equivalent to starting from the fundamental class, but it is better
suited to the proved purity-and-extension API: normalization is established where the local Thom
coclass lives, then transported across a constructed equivalence.

# Precisely what “Borel--Moore” means here

The group above is defined by derived closed-support sections of the actual chain sheaf in the
specified smooth ambient space. It allows singular $`Z` and needs no supplied dualizing object or
group-level duality. It is nevertheless an *ambient-supported* theory. The current code does not
prove that it is independent of the chosen closed embedding, nor identify it with a separately
defined intrinsic compactification-relative homology of $`Z`.

Goresky's treatment of the Borel--Moore chain sheaf and its dualizing role is in
[§§12.4--12.6](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=58). That reference contains the
sheaf-theoretic development reflected by the derived shift above, not merely the definition of
locally finite chains.
