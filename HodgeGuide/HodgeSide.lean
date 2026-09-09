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

# Why one filtration condition detects type `(p,p)`

The final definition pulls the filtered de Rham subspace back along the rational comparison:

```lean
#check AlgebraicGeometry.ComplexPoint.hodgeClasses
#check HodgeStructure.Pure.ofBase_mem_filtration_iff
```

In symbols,

$$`\operatorname{Hdg}^p(X;\mathbb Q)
 =\{\alpha\in H^{2p}(X;\mathbb Q):\alpha_{\mathrm{dR}}\in F^p\}.`

Classically one expects a rational class of Hodge type `(p,p)`. Why is there no explicit
condition involving $`\overline{F^p}`? In a pure weight-$`2p` Hodge structure, complex
conjugation fixes a rational vector and exchanges $`H^{a,b}` with $`H^{b,a}`. Membership in
$`F^p` forces both indices to be at least $`p`; because they sum to $`2p`, only $`(p,p)`
remains. `Pure.ofBase_mem_filtration_iff` proves precisely this linear-algebra statement.

The final cohomology type does not bundle a `Pure` instance. The abstract theorem validates the
filtration criterion, while identifying the geometric cohomology with a full pure Hodge structure
is logically additional structure. Deligne’s formulation likewise identifies rational
$`F^p`-classes in degree $`2p` with rational classes of type $`(p,p)`; see
[§1, p. 46](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56).
