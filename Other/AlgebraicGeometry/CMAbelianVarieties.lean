/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.NumberTheory.NumberField.CMField
import all Mathlib.AlgebraicGeometry.Group.Abelian
public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
## CM Abelian varieties

This file defines a CM Abelian variety. The definition here consists only of the inclusion
of a CM field into the rational endomorphisms of the Abelian variety, where the CM field,
as a `ℚ`-vector space, has dimension exactly twice the Krull dimension of the Abelian variety.

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

variable {K : Type*} [Field K]

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G : AddGrp C} [IsCommAddMonObj G.X]

/--
The endomorphism ring of a commutative group object has a natural ring structure.
This instance is currently an open PR in mathlib (#43539), and should be removed
once it is merged.
-/
instance : Ring (End G) := sorry

section Commutativity

variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

attribute [to_additive_do_translate] Scheme Scheme.instCategory
attribute [to_additive (attr := instance) isClosedImmersion_zero_left]
  instIsClosedImmersionLeftSchemeOneOverSpecOf
attribute [to_additive] isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed
attribute [to_additive] isCommMonObj_of_isProper_of_geometricallyIntegral

/-- Abelian varieties are commutative. -/
instance : IsCommAddMonObj A := isCommAddMonObj_of_isProper_of_geometricallyIntegral A

end Commutativity

section EndomorphismRing

open TensorProduct AddGrp

/-- For an abelian variety `A`, defined over a field `K`, the algebra of rational endomorphisms is
`End⁰ A = ℚ ⊗[ℤ] End A`, where the endomorphisms are defined over `K`. -/
abbrev RationalEnd (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
  := ℚ ⊗[ℤ] (End (mk A))

namespace RationalEnd

scoped notation "End⁰ " A:max => RationalEnd A

end RationalEnd

end EndomorphismRing

section CMStructure

open NumberField RationalEnd

variable (A : Over (Spec ↧K))
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

/-- A complex multiplication structure `ι : CMStructure A F` for an abelian variety `A` over a
field `K` and a CM field `F` is made of an inclusion `F →+* End⁰ A` together with a proof
that `[F : ℚ] = 2 * dim A`, where `End⁰ A = ℚ ⊗[ℤ] End A` is the algebra of all the rational
endomorphisms of `A`. Note that the endomorphisms are defined over the base field `K`.
Alternative definitions that exist:
1. Some authors define `End A` over the algebraic closure of `K` (this is not equivalent to
our definition, in fact it is weaker).
2. Some authors only require that `F` is a product of CM fields (this is not equivalent to our
definition, in fact it is weaker).
3. In characteristic zero, some authors define a CM abelian variety of CM type `(F, Φ)`, where
`Φ` is read off of the action of `F` on the Lie algebra of `A` (this definition is equivalent
to our definition in characteristic zero). -/
structure CMStructure (F : Type*) [Field F] [NumberField F] [IsCMField F] where
  /-- The inclusion of the CM field into the algebra of rational endomorphisms -/
  incl : F →+* End⁰ A
  /-- The dimension of the CM field is twice the Krull dimension of the abelian variety -/
  finrank_of_CM_field : Module.finrank ℚ F = 2 * topologicalKrullDim A.left

end CMStructure
