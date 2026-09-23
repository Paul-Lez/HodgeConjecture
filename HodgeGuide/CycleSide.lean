/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import Other.AlgebraicGeometry.Cycle.SheafClass

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Cycles and cohomology with support" =>
%%%
tag := "cycles"
%%%

```lean -show
open AlgebraicGeometry CategoryTheory ComplexPoint Order TopologicalSpace
noncomputable section
universe u
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d p : ℕ) (x : X.left) (hx : coheight x = p) (n : ℤ)

local instance analyticSupportHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)
```

# Cycles are indexed by generic points

The *coheight* of a point $`x` of a scheme is the codimension of its closure $`\overline{\{x\}}`,
an irreducible closed subset with generic point $`x`. A codimension-$`p` cycle is a locally finite
integer combination of points of coheight $`p`. The formalization uses this description
throughout, in place of a separate type of subvarieties.

```lean -show
namespace Guide.Cycles.D1
```
```lean
def codimensionCycleSubgroup (X : Scheme.{u}) (p : ℕ) : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier c := ∀ x, c x ≠ 0 → coheight x = p
  zero_mem' x hx := (hx rfl).elim
  add_mem' := by
    intro a b ha hb x hx
    by_cases hax : a x = 0
    · exact hb x (by simpa [hax] using hx)
    · exact ha x hax
  neg_mem' := by
    intro a ha x hx
    refine ha x fun h ↦ hx ?_
    change -(a x) = 0
    simp [h]
```
```lean -show
end Guide.Cycles.D1
example : @Guide.Cycles.D1.codimensionCycleSubgroup.{u} = @AlgebraicGeometry.codimensionCycleSubgroup.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D2
```
```lean
open scoped Classical in
noncomputable def codimensionCycleSubgroup.single {X : Scheme.{u}} {p : ℕ} (x : X) (hx : coheight x = p)
    (n : ℤ) : codimensionCycleSubgroup X p :=
  ⟨Function.locallyFinsuppWithin.single x n, by
    intro y hy
    by_cases h : y = x
    · simpa [h] using hx
    · simp [Function.locallyFinsuppWithin.single_apply, h] at hy⟩
```
```lean -show
end Guide.Cycles.D2
example : @Guide.Cycles.D2.codimensionCycleSubgroup.single.{u} = @AlgebraicGeometry.codimensionCycleSubgroup.single.{u} := rfl
```
# The support of a subvariety

For a point {lean}`x` of {lean}`X.left`, {lean}`cycleComponent X.left x` is the reduced closed
subscheme with underlying space $`\overline{\{x\}}`, and {name}`cycleComponentι` is its closed
immersion into {lean}`X.left`. The
support of the subvariety in $`X(\mathbb C)` is the preimage of $`\overline{\{x\}}` under the map
from complex points to scheme points, and it is closed in the analytic topology.

```lean -show
namespace Guide.Cycles.D5
```
```lean
def cycleComponent (X : Scheme) (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subscheme
```
```lean -show
end Guide.Cycles.D5
example : @Guide.Cycles.D5.cycleComponent.{u} = @AlgebraicGeometry.cycleComponent.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D6
```
```lean
def cycleComponentι (X : Scheme) (x : X) : cycleComponent X x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι
```
```lean -show
end Guide.Cycles.D6
example : @Guide.Cycles.D6.cycleComponentι.{u} = @AlgebraicGeometry.cycleComponentι.{u} := rfl
```
```lean -show
namespace Guide.Cycles.D7
```
```lean
def cycleComponentSupport (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) : Set (ComplexPoint X) :=
  Point.underlying ⁻¹' closure {x}
```
```lean -show
end Guide.Cycles.D7
example : @Guide.Cycles.D7.cycleComponentSupport = @AlgebraicGeometry.cycleComponentSupport := rfl
```

```lean
#check isClosed_cycleComponentSupport
```

Only the ambient variety is assumed smooth. A subvariety may be singular, and the construction of
its class in the next section handles that case from the start.

# Cohomology with support

Let $`Z\subseteq X(\mathbb C)` be closed, with open complement $`U`. Mathlib defines sheaf
cohomology as an `Ext` group: $`H^n(X;F)=\operatorname{Ext}^n(\mathbb Z_X,F)`, and the
cohomology of an open $`U` as $`\operatorname{Ext}^n(\mathbb Z[U],F)`, where $`\mathbb Z[U]` is
the free abelian sheaf on the presheaf represented by $`U`. The formalization follows this
pattern. For opens $`W\le V`, the sheaf $`\mathbb Z[V,W]` is the cokernel of
$`\mathbb Z[W]\to\mathbb Z[V]`, and the cohomology of the pair $`(V,W)` is
$`\operatorname{Ext}^n(\mathbb Z[V,W],F)`. Cohomology with support in $`Z` is the case of the pair
$`(X,U)`. The short exact sequence $`0\to\mathbb Z[U]\to\mathbb Z[X]\to\mathbb Z[X,U]\to0`
gives the long exact sequence

$$`\cdots\to H^n_Z(X;F)\to H^n(X;F)\to H^n(U;F)\to H^{n+1}_Z(X;F)\to\cdots`

as the contravariant `Ext` sequence, {name}`CategoryTheory.Sheaf.relH.sequence_exact`. Forgetting
support is its first map: precomposition with $`\mathbb Z[X]\to\mathbb Z[X,U]`, followed by the
identification of $`\mathbb Z[X]` with the constant sheaf $`\mathbb Z_X`. The group has its own
notation, `H_[Z]^n(X; K)`.

```lean -show
universe v w
namespace Guide.Cycles.D8
```
```lean
abbrev pairSheaf {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] {U V : C} (f : U ⟶ V) : Sheaf J AddCommGrpCat.{v} :=
  Limits.cokernel ((Sheaf.freeAbelianSheaf J).map f)
```
```lean -show
end Guide.Cycles.D8
example : @Guide.Cycles.D8.pairSheaf = @CategoryTheory.Sheaf.pairSheaf := rfl
```
```lean -show
namespace Guide.Cycles.D9
```
```lean
abbrev relH {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (f : U ⟶ V) : Type w :=
  Abelian.Ext (Sheaf.pairSheaf (J := J) f) F n
```
```lean -show
end Guide.Cycles.D9
example : @Guide.Cycles.D9.relH = @CategoryTheory.Sheaf.relH := rfl
```
```lean -show
namespace Guide.Cycles.D10
```
```lean
abbrev supportH (X : TopCat.{u})
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] (Z : Closeds X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) : Type w :=
  Sheaf.relH F n (homOfLE (le_top : Z.compl ≤ ⊤))
```
```lean -show
end Guide.Cycles.D10
example : @Guide.Cycles.D10.supportH = @TopCat.Sheaf.supportH := rfl
```
```lean -show
namespace Guide.Cycles.D11
```
```lean
def forgetSupport (K : Type) [Field K] (X : Over (Spec ↧ℂ)) (Z : Closeds (ComplexPoint X))
    (n : ℕ) : H_[Z]^n(X; K) →+ H^n(X; K) :=
  (Sheaf.H'.addEquivTerminal Limits.isTerminalTop _ n).toAddMonoidHom.comp
    (Sheaf.relH.forget _ (homOfLE (le_top : Z.compl ≤ ⊤)) n)
```
```lean -show
end Guide.Cycles.D11
example : @Guide.Cycles.D11.forgetSupport = @AlgebraicGeometry.ComplexPoint.forgetSupport := rfl
```

For the triangle and the exact sequence of a pair see Goresky,
[§§7.14–7.15](https://www.math.ias.edu/~goresky/pdf/all.pdf#page=31); for the derived-functor
description see the Stacks Project,
[§20.21](https://stacks.math.columbia.edu/tag/0A39).
