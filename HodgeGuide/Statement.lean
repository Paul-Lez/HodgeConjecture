/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeConjecture.Statement
import Other.AlgebraicGeometry.ChowCycleClassDescent
import Other.AlgebraicGeometry.SheafCycleClass

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
open AlgebraicGeometry.ChowGroup
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
    CodimensionCycle V.scheme p →+ H^(2 * (p : ℤ))(V.over; ℚ) :=
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
    TensorProduct ℤ ℚ (CodimensionCycle V.scheme p) →ₗ[ℚ]
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

Whether these maps factor through rational equivalence is a separate question, taken up below.

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

# Why a span rather than a map on Chow groups
%%%
tag := "why-a-span"
%%%

The repository defines {name}`ChowGroup` and {name}`RationalChowGroup`, and the classes of subvarieties give an
additive map on cycles. To descend this map to the Chow group, one must show that it vanishes on
every principal-divisor relation. The descent itself is formalized as a construction that takes
this vanishing as a hypothesis, but the vanishing has not been proved for the classes constructed
here.

```lean -show
namespace Guide.Statement.D3
```
```lean
def ChowGroup.cycleClassOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (hprincipal : ∀ D : PrincipalDivisor X p,
      cycleClassOnAlgebraicCyclesOfComponents componentClass D.pushforwardCycle = 0) :
    ChowGroup X p →+ M :=
  liftCycleClass (cycleClassOnCyclesOfComponents componentClass)
    (rationalEquivalenceSubgroup_le_cycleClassOnCyclesOfComponents_ker
      componentClass hprincipal)
```
```lean -show
end Guide.Statement.D3
example : @Guide.Statement.D3.ChowGroup.cycleClassOfComponents.{u, u_1} = @AlgebraicGeometry.ChowGroup.cycleClassOfComponents.{u, u_1} := rfl
```
```lean -show
namespace Guide.Statement.D4
```
```lean
def ChowGroup.rationalCycleClassOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M] [Module ℚ M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (hprincipal : ∀ D : PrincipalDivisor X p,
      cycleClassOnAlgebraicCyclesOfComponents componentClass D.pushforwardCycle = 0) :
    RationalChowGroup X p →ₗ[ℚ] M :=
  rationalExtension (cycleClassOfComponents componentClass hprincipal)
```
```lean -show
end Guide.Statement.D4
example : @Guide.Statement.D4.ChowGroup.rationalCycleClassOfComponents.{u, u_1} = @AlgebraicGeometry.ChowGroup.rationalCycleClassOfComponents.{u, u_1} := rfl
```

```lean
#check AlgebraicGeometry.ChowGroup.cycleClassOfComponents_mk
```

The span of the classes of subvarieties is exactly the image that the descended map would have,
so nothing is lost by using it. The statement says "rational linear combinations of classes of
subvarieties" without claiming a factorization through rational equivalence.

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
7. `HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexSheafBorelMoore.lean` and
   `ComplexSheafBorelMooreRationalComparison.lean`, Borel–Moore homology and duality;
8. `Other/AlgebraicGeometry/SheafCycleClass.lean`, the maps on cycles;
9. `Other/AlgebraicGeometry/ChowCycleClassDescent.lean`, descent to Chow groups.

Things to keep track of while reading: integer versus natural-number degrees, real versus complex
dimension, whether a class has been normalized, whether its support has been forgotten, and
whether a map is defined on cycles or on their quotient by rational equivalence.
