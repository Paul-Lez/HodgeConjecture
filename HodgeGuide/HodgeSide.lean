/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "The Hodge side" =>

# From complex points to a de Rham complex

For a smooth complex scheme $`X`, the formalization works on its analytic complex-point space
$`X(\mathbb C)`. Holomorphic differential forms are first organized as presheaves. Exterior
differentiation gives the cochain complex

$$`\mathcal O_X \xrightarrow{d} \Omega_X^1 \xrightarrow{d}
  \Omega_X^2 \xrightarrow{d}\cdots,`

and degreewise sheafification produces `holomorphicDeRhamComplexInt`. The integer indexing is
important because later constructions use derived shifts, even though the complex itself is zero
in negative degrees.

```lean
#check AlgebraicGeometry.ComplexPoint.holomorphicDeRhamComplexInt
#check AlgebraicGeometry.ComplexPoint.constantsToHolomorphicDeRhamComplexInt
#check AlgebraicGeometry.ComplexPoint.constantsToHolomorphicDeRhamComplexInt_quasiIso
```

The last declaration is the holomorphic Poincaré lemma at the level of stalks: locally closed
holomorphic forms are exact, and locally constant holomorphic functions are precisely the kernel
in degree zero. Thus

$$`\underline{\mathbb C}_X \longrightarrow \Omega_X^\bullet`

is a quasi-isomorphism, not a definitional identification.

This is the analytic de Rham theorem in the exact form the code needs. See Goresky,
[§§3.10--3.11](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=16), for the Poincaré lemma,
the de Rham sheaf resolution, and its hypercohomology consequence.

# Cohomology without choosing a concrete derived category

The public cohomology types are small shifted morphisms in the localization of complexes at
quasi-isomorphisms. If $`\mathbb Z_X` denotes the constant integer sheaf, then the model is

$$`\mathbb H^n(X,K^\bullet)
  =\operatorname{Hom}_{D(X)}(\mathbb Z_X,K^\bullet[n]).`

Using the localization interface keeps a noncanonical derived-category implementation out of the
type. Rational cohomology and de Rham hypercohomology are special cases.

```lean
#check AlgebraicGeometry.ComplexPoint.Hypercohomology
#check AlgebraicGeometry.ComplexPoint.FieldCohomology
#check AlgebraicGeometry.ComplexPoint.DeRhamHypercohomology
#check AlgebraicGeometry.ComplexPoint.fieldToDeRhamCohomologyLinear
```

The comparison map starts with the inclusion of constant sheaves
$`\underline{\mathbb Q}_X\to\underline{\mathbb C}_X` and then uses the proved
constant-to-de Rham quasi-isomorphism. The map is proved $`\mathbb Q`-linear; no equality between
rational and de Rham cohomology is asserted.

# The filtration is an image, not a predicate invented afterward

The Hodge filtration is obtained from the stupid truncation

$$`F^p\Omega_X^\bullet=\sigma_{\ge p}\Omega_X^\bullet
  =[0\to\cdots\to0\to\Omega_X^p\to\Omega_X^{p+1}\to\cdots].`

The inclusion into the full complex induces a map on hypercohomology, and $`F^pH^n` is its image.
That definition is exactly the standard one; compare the
[Stacks Project, §50.7](https://stacks.math.columbia.edu/tag/0FM7) and Deligne's
[§1, especially pp. 45--46](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56).

```lean
#check AlgebraicGeometry.ComplexPoint.hodgeFilteredDeRhamComplex
#check AlgebraicGeometry.ComplexPoint.hodgeFilteredDeRhamInclusion
#check AlgebraicGeometry.ComplexPoint.filteredToDeRhamCohomology
#check AlgebraicGeometry.ComplexPoint.hodgeFiltrationSubmodule
```

Two sanity checks are proved in Lean: $`F^0` is the whole de Rham group, and $`F^p=0` when
$`p>\dim X`. Scalar compatibility is proved before the additive image is bundled as a complex or
rational submodule.

# Type `(p,p)`, and why one filtration condition suffices over `ℚ`

Complex conjugation is not $`\mathbb C`-linear, so it does not act on the holomorphic de Rham
complex. It acts on the constant sheaf $`\mathbb C`, where it is just the ring automorphism
applied to coefficients, and is transported to de Rham hypercohomology across the
constant-to-de Rham comparison. The $`(p,q)` piece is then *defined* as
$`F^p\cap\overline{F^q}` — an equality that holds in any pure Hodge structure, and that needs no
Hodge decomposition theorem to write down. Hodge classes are the classes landing in the $`(p,p)`
piece:

```lean
#check AlgebraicGeometry.ComplexPoint.deRhamConj
#check AlgebraicGeometry.ComplexPoint.hodgePiece
#check AlgebraicGeometry.ComplexPoint.hodgeClasses
#check HodgeStructure.Pure.ofBase_mem_filtration_iff
```

In symbols,

$$`\operatorname{Hdg}^p(X;K)
 =\{\alpha\in H^{2p}(X;K):\alpha_{\mathrm{dR}}\in F^p\cap\overline{F^p}\}.`

Over $`\mathbb Q` the conjugation condition is free, and the filtration condition alone cuts out
the Hodge classes. In a pure weight-$`2p` Hodge structure, complex conjugation fixes a rational
vector and exchanges $`H^{a,b}` with $`H^{b,a}`. Membership in $`F^p` forces both indices to be at
least $`p`; because they sum to $`2p`, only $`(p,p)` remains.
`Pure.ofBase_mem_filtration_iff` proves precisely this linear-algebra statement, and
`hodgeClasses_rat_eq_comap_hodgeFiltrationSubmodule` proves the corresponding statement for the
geometric definition.

```lean
#check AlgebraicGeometry.ComplexPoint.hodgeClasses_rat_eq_comap_hodgeFiltrationSubmodule
```

The reality of the coefficients is essential, and this is why the coefficient field is not left
arbitrary in that lemma. For a non-real $`K` the two conditions differ. Take $`K=\mathbb Q(i)` and
$`E=\mathbb C/(\mathbb Z+\mathbb Z i)`: the periods of $`dz` are $`1` and $`i`, so $`dz` is a
$`\mathbb Q(i)`-rational class spanning $`H^{1,0}(E)`, and on $`E\times E` the class
$`\mathrm{pr}_1^*dz\wedge \mathrm{pr}_2^*dz` is a nonzero $`\mathbb Q(i)`-rational class of type
$`(2,0)`. It lies in $`F^1H^2` but has zero $`(1,1)`-component, so an $`F^p`-only definition would
call it a Hodge class of codimension $`1`; since algebraic cycle classes are $`\mathbb Q`-rational
of type $`(1,1)`, no combination of them can reach it.

The final cohomology type does not bundle a `Pure` instance. The abstract theorem validates the
filtration criterion, while identifying the geometric cohomology with a full pure Hodge structure
is logically additional structure. Deligne’s formulation likewise identifies rational
$`F^p`-classes in degree $`2p` with rational classes of type $`(p,p)`; see
[§1, p. 46](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56).
