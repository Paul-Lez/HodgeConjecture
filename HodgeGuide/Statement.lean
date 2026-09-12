/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeConjecture.Statement
import Other.AlgebraicGeometry.CodimensionZeroCoclassNonvanishing
import Other.AlgebraicGeometry.CycleClassDimension
import Other.AlgebraicGeometry.SheafCycleClass
import Other.AlgebraicGeometry.SmoothAnalytificationConnected

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "The statement" =>
%%%
tag := "the-statement"
%%%

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
noncomputable section
universe u u_1
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)
```

# From subvarieties to cycles

With the class of a subvariety in hand, summing over the components of a cycle with their
multiplicities gives an additive map on integral cycles, and extension of scalars gives a
$`\mathbb Q`-linear map on rational cycles. The evaluation formulas
below hold for all integer and rational coefficients.

```lean -show
namespace Guide.Statement.D5
```
```lean
def sheafCycleClassOnCycles (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] (p : ℕ) :
    codimensionCycleSubgroup V.scheme p →+ H^(2 * (p : ℤ))(V.over; ℚ) :=
  cycleClassOnCyclesOfComponents (cycleComponentSheafClass V.over (d := d))
```
```lean -show
end Guide.Statement.D5
example : @Guide.Statement.D5.sheafCycleClassOnCycles = @AlgebraicGeometry.ComplexPoint.sheafCycleClassOnCycles := rfl
```

```lean
#check AlgebraicGeometry.ComplexPoint.sheafCycleClassOnCycles_single
```

```lean -show
namespace Guide.Statement.D6
```
```lean
def rationalSheafCycleClassOnCycles
    (V : SmoothProjectiveComplexVariety) (d : ℕ)
    [SmoothOfRelativeDimension d V.structureMap] (p : ℕ) :
    TensorProduct ℤ ℚ (codimensionCycleSubgroup V.scheme p) →ₗ[ℚ]
      H^(2 * (p : ℤ))(V.over; ℚ) :=
  TensorProduct.AlgebraTensorModule.lift (sheafCycleClassRationalExtensionBilinear V d p)
```
```lean -show
end Guide.Statement.D6
example : @Guide.Statement.D6.rationalSheafCycleClassOnCycles = @AlgebraicGeometry.ComplexPoint.rationalSheafCycleClassOnCycles := rfl
```

```lean
#check AlgebraicGeometry.ComplexPoint.rationalSheafCycleClassOnCycles_tmul_single
```

These maps take a {name}`SmoothProjectiveComplexVariety`, a scheme with its structure morphism to
$`\operatorname{Spec}\mathbb C`, together with a natural number {lean}`d` and an instance saying
that the structure morphism is smooth of relative dimension {lean}`d`. The construction of the
class of a subvariety needs that dimension. For a smooth integral complex scheme the instance
holds at {lean}`dim X.left`, so a caller supplies {lean}`dim X.left` and typeclass search finds the
certificate.

{name}`algebraicCycleClassSpan`, defined next, evaluates each class at {lean}`dim X.left` directly,
so the statement mentions the scheme and its structure morphism alone.

# The algebraic subspace

For every point {lean}`x` of coheight $`p` in {lean}`X.left`, the construction of the previous
section gives a class

$$`\operatorname{cl}_X(\overline{\{x\}})\in H^{2p}(X;\mathbb Q).`

The algebraic subspace is the rational span of these classes:

$$`A^p(X)=\sum_{\operatorname{coht}(x)=p}
  \mathbb Q\,\operatorname{cl}_X(\overline{\{x\}}).`

```lean -show
namespace Guide.Statement.D2
```
```lean
def algebraicCycleClassSpan (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) : Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx}
```
```lean -show
end Guide.Statement.D2
example : @Guide.Statement.D2.algebraicCycleClassSpan = @AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan := rfl
```

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_mem_algebraicCycleClassSpan
```

In Lean the span is the supremum, over all points {lean}`x` and all proofs {lean}`hx` of
{lean}`coheight x = p`, of the line spanned by
{lean}`cycleComponentSheafClass X x (d := dim X.left) hx`, where the named argument fixes the
dimension at {lean}`dim X.left`.

# The proposition

Here is the full statement, as declared in `HodgeConjecture/Statement.lean`. The copy shown here
is elaborated when the site is built, and the build checks that it is definitionally equal to the
declaration in the repository.

```lean -show
namespace Guide.Statement.D1
```
```lean
def HodgeConjecture : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ),
    Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p
```
```lean -show
end Guide.Statement.D1
example : @Guide.Statement.D1.HodgeConjecture = @HodgeConjecture := rfl
```

It quantifies over a scheme {lean}`X` over $`\mathbb C` that is integral with smooth and projective
structure morphism, and over a natural number {lean}`p`. The conclusion is the inclusion of subspaces

$$`\operatorname{Hdg}^p(X;\mathbb Q)\le A^p(X):`

every rational Hodge class of degree $`2p` is a rational linear combination of classes of
algebraic subvarieties of codimension $`p`. This is the conjecture as Deligne states it,
[pp. 45–46](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56). The reverse
inclusion, that every algebraic class is a Hodge class, is a theorem that has not yet been
formalized, so the formulation as an equality $`\operatorname{Hdg}^p(X;\mathbb Q)=A^p(X)` is not
yet available.

# What the repository proves about the statement
%%%
tag := "what-is-proved"
%%%

The conjecture is stated, not proved. Two of its cases are proved outright.

The easy case is $`p>\dim X`. A smooth variety has no point of coheight above its dimension, so
the span is $`\bot`; and $`F^p` vanishes there, so the Hodge classes are $`\bot` too. The
inclusion holds because both sides are zero. It settles nothing about the conjecture, but it does
check that the two sides degenerate together, which a mismatch in the degree conventions would
break.

```lean
#check AlgebraicGeometry.ComplexPoint.hodgeClasses_eq_bot_of_lt
#check AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan_eq_bot_of_lt
```

Codimension zero is the substantial one. Both sides are computed, and they agree:

$$`\operatorname{Hdg}^0(X;\mathbb Q)=A^0(X)=H^0(X;\mathbb Q).`

```lean
#check AlgebraicGeometry.ComplexPoint.rationalHodgeClasses_zero_eq_algebraicCycleClassSpan
```

The left-hand side is everything, because $`F^0` is; that is the sanity check of
{ref "hodge-classes"}[Hodge classes]. The right-hand side is the line on a single class, that of
the generic point of {lean}`X.left`, since on an integral scheme no other point has coheight zero.
That line is all of $`H^0(X;\mathbb Q)` for two reasons: the analytification of a smooth integral
complex scheme is connected, so $`H^0` is itself a line, and the class is nonzero. Connectedness
is proved here, from Noether normalization and a local étale chart, rather than assumed.

```lean
#check AlgebraicGeometry.ComplexPoint.hodgeClasses_zero_eq_top
#check AlgebraicGeometry.ComplexPoint.connectedSpace
#check AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass_genericPoint_ne_zero
```

The nonvanishing is the part that tests the construction. Its proof runs the chain of
{ref "class-of-a-subvariety"}[The class of a subvariety] backwards: the normalized local section
is nonzero at any complex point of the smooth locus, the two normalization comparisons are
isomorphisms, and forgetting support is injective here because the generic component is supported
on all of $`X(\mathbb C)`. So the construction does not return zero, at least for this one
subvariety, on a variety of any dimension.

For a component of positive codimension the same chain stops at the last step. The normalized
section is still nonzero, for every component:

```lean
#check AlgebraicGeometry.ComplexPoint.cycleComponentSmoothSupportCoclassSection_ne_zero
```

but forgetting support need not be injective on $`H^{2p}_Z(X;\mathbb Q)`, and showing that it is
on the fundamental-class line is cohomological purity, which is open; see
{ref "scope-and-status"}[Scope and status]. Until it is settled, $`A^p(X)` is generated by classes
not yet known to be nonzero, so it could be smaller than the classical right-hand side, making
the statement stronger than the conjecture rather than weaker.

# Reading the source

The shortest route through the implementation is:

1. `HodgeConjecture/Statement.lean`, the statement;
2. `HodgeConjecture/Definitions/AlgebraicGeometry/HodgeFiltration.lean`, cohomology and the Hodge
   filtration;
3. `HodgeConjecture/Definitions/AlgebraicGeometry/CohomologyWithSupport.lean`, the mapping-cone
   model of cohomology with support;
4. `HodgeConjecture/Definitions/AlgebraicGeometry/CycleComponentSmoothSupportCoclassSection.lean`,
   the class on the smooth locus;
5. `HodgeConjecture/Definitions/AlgebraicGeometry/CycleComponentSupportExtension.lean`, its
   extension across the singular locus;
6. `HodgeConjecture/Definitions/AlgebraicGeometry/CycleComponentSheafClass.lean`, the class of a
   subvariety;
7. `HodgeConjecture/Definitions/AlgebraicGeometry/AlgebraicCycleClassSpan.lean`, the span the
   statement compares against;
8. `Other/AlgebraicGeometry/SheafCycleClass.lean`, the maps on cycles;
9. `Other/AlgebraicGeometry/CodimensionZeroClassComparison.lean` and
   `CodimensionZeroCoclassNonvanishing.lean`, the codimension-zero case.

`Other/AlgebraicGeometry/ComplexSheafBorelMoore.lean` and its rational comparison are not on this
route. They build Borel–Moore homology of the pair $`Z\subset X` and its duality with cohomology
with support; both live in `Other/`, so the import check that guards
`HodgeConjecture/Statement.lean` guarantees the statement does not reach them.

Things to keep track of while reading: integer versus natural-number degrees, real versus complex
dimension, whether a class has been normalized, whether its support has been forgotten, and
whether a class is supported or ordinary.
