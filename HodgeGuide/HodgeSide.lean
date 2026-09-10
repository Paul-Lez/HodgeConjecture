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

#doc (Manual) "Hodge classes" =>

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
```

# The holomorphic de Rham complex

Let $`X` be a smooth complex scheme. The formalization works on the space $`X(\mathbb C)` of its
complex points with the analytic topology. Holomorphic differential forms on this space are first
assembled into presheaves, and exterior differentiation makes them a complex of presheaves

$$`\mathcal O_X \xrightarrow{d} \Omega_X^1 \xrightarrow{d}
  \Omega_X^2 \xrightarrow{d}\cdots.`

Sheafifying degree by degree gives the holomorphic de Rham complex. It is indexed by the integers
and vanishes in negative degrees, because the shifts used later act on $`\mathbb Z`-indexed
complexes.

```lean
#check AlgebraicGeometry.ComplexPoint.holomorphicDeRhamComplexInt
#check AlgebraicGeometry.ComplexPoint.constantsToHolomorphicDeRhamComplexInt
#check AlgebraicGeometry.ComplexPoint.constantsToHolomorphicDeRhamComplexInt_quasiIso
```

Constant functions give a morphism to the de Rham complex from the constant sheaf
$`\underline{\mathbb C}_X`, placed in degree zero. The last declaration is the holomorphic Poincaré
lemma: on stalks, a closed holomorphic form of positive degree is exact, and the closed holomorphic
functions are the locally constant ones, so

$$`\underline{\mathbb C}_X \longrightarrow \Omega_X^\bullet`

is a quasi-isomorphism. This is the analytic de Rham theorem in the form used below. Goresky's
notes, [§3.10](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=17), explain how the Poincaré
lemma exhibits the de Rham complex as a resolution of the constant sheaf and thereby computes its
cohomology.

# Cohomology as morphisms in the derived category

For a complex of sheaves $`K^\bullet` on $`X(\mathbb C)`, hypercohomology is defined as a group of
morphisms in the derived category,

$$`\mathbb H^n(X,K^\bullet)
  =\operatorname{Hom}_{D(X)}(\underline{\mathbb Z}_X,K^\bullet[n]),`

where $`\underline{\mathbb Z}_X` is the constant sheaf in degree zero. The derived category is never
constructed: Mathlib's {name}`Localization.SmallShiftedHom` provides these morphism groups in the
localization of complexes at quasi-isomorphisms without choosing a model for it. Rational
cohomology and de Rham cohomology are the cases $`K^\bullet=\underline{\mathbb Q}_X` and
$`K^\bullet=\Omega_X^\bullet`.

```lean
#check AlgebraicGeometry.ComplexPoint.Hypercohomology
#check AlgebraicGeometry.ComplexPoint.FieldCohomology
#check AlgebraicGeometry.ComplexPoint.DeRhamHypercohomology
#check AlgebraicGeometry.ComplexPoint.fieldToDeRhamCohomologyLinear
```

The comparison map $`H^n(X;\mathbb Q)\to H^n_{\mathrm{dR}}(X)` is induced by the composite
$`\underline{\mathbb Q}_X\to\underline{\mathbb C}_X\to\Omega_X^\bullet`. It is $`\mathbb Q`-linear
and injective; injectivity combines the quasi-isomorphism above with the injectivity of extending
scalars from $`\mathbb Q` to $`\mathbb C`. Nothing more is needed, since Hodge classes are defined
as a preimage along this map.

# The Hodge filtration

The Hodge filtration comes from the stupid truncation of the de Rham complex,

$$`F^p\Omega_X^\bullet=\sigma_{\ge p}\Omega_X^\bullet
  =[0\to\cdots\to0\to\Omega_X^p\to\Omega_X^{p+1}\to\cdots].`

Its inclusion into $`\Omega_X^\bullet` induces a map on hypercohomology, and
$`F^pH^n_{\mathrm{dR}}(X)` is the image of that map. This is the standard definition; compare the
[Stacks Project, §50.7](https://stacks.math.columbia.edu/tag/0FM7), and Deligne's article,
[p. 51](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=59), where the same
truncated complex appears.

```lean
#check AlgebraicGeometry.ComplexPoint.hodgeFilteredDeRhamComplex
#check AlgebraicGeometry.ComplexPoint.hodgeFilteredDeRhamInclusion
#check AlgebraicGeometry.ComplexPoint.filteredToDeRhamCohomology
#check AlgebraicGeometry.ComplexPoint.hodgeFiltrationSubmodule
```

The image is a priori an additive subgroup. Compatibility with scalars is proved, and
{name}`hodgeFiltrationSubmodule` bundles the image as a subspace over any coefficient field contained
in $`\mathbb C`. Two sanity checks are also proved: $`F^0` is all of $`H^n_{\mathrm{dR}}(X)`, and
$`F^p=0` for $`p>\dim X`.

# Hodge classes

The rational Hodge classes of degree $`2p` are the rational classes whose de Rham image lies in
$`F^p`:

$$`\operatorname{Hdg}^p(X;\mathbb Q)
 =\{\alpha\in H^{2p}(X;\mathbb Q):\alpha_{\mathrm{dR}}\in F^pH^{2p}_{\mathrm{dR}}(X)\}.`

In Lean this is the preimage of {name}`hodgeFiltrationSubmodule` under the comparison map, and the
notation {lean}`Hdg^p(ℚ; X)` abbreviates it.

```lean
#check AlgebraicGeometry.ComplexPoint.hodgeClasses
#check HodgeStructure.Pure.ofBase_mem_filtration_iff
```

The textbook definition asks instead for a rational class of Hodge type $`(p,p)`, which involves
the conjugate filtration $`\overline{F^p}` as well. The two definitions agree. In a pure Hodge
structure of weight $`2p`, complex conjugation fixes rational vectors and exchanges $`H^{a,b}`
with $`H^{b,a}`, so a rational vector in $`F^p=\bigoplus_{a\ge p}H^{a,2p-a}` also lies in
$`\overline{F^p}=\bigoplus_{b\ge p}H^{2p-b,b}`, and the only summand common to both is $`H^{p,p}`.
The lemma {name HodgeStructure.Pure.ofBase_mem_filtration_iff}`Pure.ofBase_mem_filtration_iff` is
this argument for an abstract pure Hodge structure,
as defined in `HodgeConjecture/Definitions/LinearAlgebra/HodgeStructure.lean`.

The cohomology of $`X` is not equipped with a pure Hodge structure in the formalization; that
would require the Hodge decomposition. The filtration condition is therefore taken as the
definition, and the lemma shows that it is the right one. Deligne likewise identifies the two
descriptions when stating the conjecture,
[p. 46](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=57).
