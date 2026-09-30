/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.InvertibleSheafRationalSection

/-!
# Cartier data representing an invertible sheaf
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

open Scheme.Modules

variable {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S] {L : S.Modules}

/--
Cartier data `c` *represents* the sheaf of modules `L` when there are local generators of `L`
on the members of the cover of `c` whose transition functions are the ratios of the local
equations of `c`: if `u` is a unit of the structure sheaf with `u • gᵢ = gⱼ` on the overlap,
then `u · fⱼ = fᵢ` in the function field.

Equivalently, the local sections `fᵢ • gᵢ` glue to one nonzero rational section of `L`, and
`c.divisor` is the divisor of that section.
-/
def Scheme.CartierData.Represents (c : S.CartierData) (L : S.Modules) : Prop :=
  ∃ g : ∀ i : c.ι, Γ(L, c.opens i),
    (∀ i, Generates (g i)) ∧
    ∀ (i j : c.ι) (u : Γ(S, c.opens i ⊓ c.opens j)), IsUnit u →
      u • resSection L inf_le_left (g i) = resSection L inf_le_right (g j) →
      haveI := c.nonempty_inf i j
      S.germToFunctionField (c.opens i ⊓ c.opens j) u * c.fn j = c.fn i

end AlgebraicGeometry
