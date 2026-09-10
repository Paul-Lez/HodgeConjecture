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
%%%
tag := "hodge-classes"
%%%

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
noncomputable section
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

```lean -show
namespace Guide.Hodge.D1
```
```lean
def holomorphicDeRhamComplexInt (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex (TopCat.Sheaf AddCommGrpCat ↧(ComplexPoint X)) ℤ :=
  (holomorphicDeRhamComplex X (dim X.left)).extend ComplexShape.embeddingUpNat
```
```lean -show
end Guide.Hodge.D1
example : @Guide.Hodge.D1.holomorphicDeRhamComplexInt = @AlgebraicGeometry.ComplexPoint.holomorphicDeRhamComplexInt := rfl
```

Constant functions give a morphism to the de Rham complex from the constant sheaf
$`\underline{\mathbb C}_X`, placed in degree zero.

```lean -show
namespace Guide.Hodge.D2
```
```lean
def constantsToHolomorphicDeRhamComplexInt (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] : constantComplexSheafComplexInt X ⟶ holomorphicDeRhamComplexInt X :=
  HomologicalComplex.extendMap
    (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat
```
```lean -show
end Guide.Hodge.D2
example : @Guide.Hodge.D2.constantsToHolomorphicDeRhamComplexInt = @AlgebraicGeometry.ComplexPoint.constantsToHolomorphicDeRhamComplexInt := rfl
```

The instance below is the holomorphic Poincaré lemma:

```lean
#check AlgebraicGeometry.ComplexPoint.constantsToHolomorphicDeRhamComplexInt_quasiIso
```

It says that, on stalks, a closed holomorphic form of positive degree is exact, and the closed holomorphic
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

```lean -show
namespace Guide.Hodge.D3
```
```lean
abbrev Hypercohomology (X : Over (Spec ↧ℂ)) (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (n : ℤ) : Type 1 :=
  Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
    (constantIntegerSheafComplexInt X) K n
```
```lean -show
end Guide.Hodge.D3
example : @Guide.Hodge.D3.Hypercohomology = @AlgebraicGeometry.ComplexPoint.Hypercohomology := rfl
```
```lean -show
namespace Guide.Hodge.D4
```
```lean
abbrev FieldCohomology (K : Type) [Field K] (X : Over (Spec ↧ℂ)) (n : ℤ) : Type 1 :=
  Hypercohomology X (constantFieldSheafComplexInt K X) n
```
```lean -show
end Guide.Hodge.D4
example : @Guide.Hodge.D4.FieldCohomology = @AlgebraicGeometry.ComplexPoint.FieldCohomology := rfl
```
```lean -show
namespace Guide.Hodge.D5
```
```lean
abbrev DeRhamHypercohomology (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Type 1 :=
  Hypercohomology X (holomorphicDeRhamComplexInt X) n
```
```lean -show
end Guide.Hodge.D5
example : @Guide.Hodge.D5.DeRhamHypercohomology = @AlgebraicGeometry.ComplexPoint.DeRhamHypercohomology := rfl
```
```lean -show
namespace Guide.Hodge.D6
```
```lean
def fieldToDeRhamCohomologyLinear (K : Type) [Field K] [Algebra K ℂ] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    FieldCohomology K X n →ₗ[K] DeRhamHypercohomology X n where
  toFun := fieldToDeRhamCohomology K X n
  map_add' := (fieldToDeRhamCohomology K X n).map_add
  map_smul' := fieldToDeRhamCohomology_smul K X n
```
```lean -show
end Guide.Hodge.D6
example : @Guide.Hodge.D6.fieldToDeRhamCohomologyLinear = @AlgebraicGeometry.ComplexPoint.fieldToDeRhamCohomologyLinear := rfl
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

```lean -show
namespace Guide.Hodge.D7
```
```lean
def hodgeFilteredDeRhamComplex (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (holomorphicDeRhamComplexInt X).stupidTrunc (ComplexShape.embeddingUpIntGE p)
```
```lean -show
end Guide.Hodge.D7
example : @Guide.Hodge.D7.hodgeFilteredDeRhamComplex = @AlgebraicGeometry.ComplexPoint.hodgeFilteredDeRhamComplex := rfl
```
```lean -show
namespace Guide.Hodge.D8
```
```lean
def hodgeFilteredDeRhamInclusion (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (p : ℤ) : hodgeFilteredDeRhamComplex X p ⟶ holomorphicDeRhamComplexInt X :=
  HomologicalComplex.stupidTruncInclusion
    (holomorphicDeRhamComplexInt X) (ComplexShape.embeddingUpIntGE p)
```
```lean -show
end Guide.Hodge.D8
example : @Guide.Hodge.D8.hodgeFilteredDeRhamInclusion = @AlgebraicGeometry.ComplexPoint.hodgeFilteredDeRhamInclusion := rfl
```
```lean -show
namespace Guide.Hodge.D9
```
```lean
def filteredToDeRhamCohomology (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : FilteredDeRhamHypercohomology X p n →+ DeRhamHypercohomology X n :=
  hypercohomologyMap X (hodgeFilteredDeRhamInclusion X p) n
```
```lean -show
end Guide.Hodge.D9
example : @Guide.Hodge.D9.filteredToDeRhamCohomology = @AlgebraicGeometry.ComplexPoint.filteredToDeRhamCohomology := rfl
```
```lean -show
namespace Guide.Hodge.D10
```
```lean
def hodgeFiltrationSubmodule (K : Type) [Field K] [Algebra K ℂ] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) : Submodule K (DeRhamHypercohomology X n) where
  carrier := hodgeFiltration X p n
  zero_mem' := (hodgeFiltration X p n).zero_mem
  add_mem' := (hodgeFiltration X p n).add_mem
  smul_mem' := fun q _ h => hodgeFiltration_smul_mem K X p n q h
```
```lean -show
end Guide.Hodge.D10
example : @Guide.Hodge.D10.hodgeFiltrationSubmodule = @AlgebraicGeometry.ComplexPoint.hodgeFiltrationSubmodule := rfl
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

```lean -show
namespace Guide.Hodge.D11
```
```lean
def hodgeClasses (K : Type) [Field K] [Algebra K ℂ] (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) : Submodule K (FieldCohomology K X (2 * p)) :=
  (hodgeFiltrationSubmodule K X p (2 * p)).comap
    (fieldToDeRhamCohomologyLinear K X (2 * p))
```
```lean -show
end Guide.Hodge.D11
example : @Guide.Hodge.D11.hodgeClasses = @AlgebraicGeometry.ComplexPoint.hodgeClasses := rfl
```

```lean
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
