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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportComparison

/-!
# Singular comparison with support

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportComparison`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

section

variable {A S I : CochainComplex C ℤ}
  [A.IsStrictlyGE 0] [S.IsStrictlyGE 0] [I.IsStrictlyGE 0]
  (a : A ⟶ S) [Mono a] [QuasiIso a]
  (r : A ⟶ I)

/-- Replacing the source of a restriction map by a monic quasi-isomorphic resolution induces a
quasi-isomorphism of mapping cones. -/
def sourceReplacementConeMap (hI : ∀ n : ℤ, Injective (I.X n)) :
    mappingCone r ⟶ mappingCone (liftToInjective a r hI) :=
  mappingCone.map r (liftToInjective a r hI) a (𝟙 I)
    (by rw [Category.comp_id, comp_liftToInjective])

noncomputable instance sourceReplacementConeMap_quasiIso
    [HasDerivedCategory C]
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    QuasiIso (sourceReplacementConeMap a r hI) :=
  mappingCone.map_quasiIso_of_vertical_quasiIso r (liftToInjective a r hI)
    a (𝟙 I) (by rw [Category.comp_id, comp_liftToInjective])

end

end CochainComplex

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

variable [IsIntegral X.left] [Smooth X.hom]

attribute [local instance] bettiSupportComparisonHasDerivedCategory

attribute [local instance] bettiSupportComparisonMono

attribute [local instance] bettiSupportComparisonQuasiIso

/-- A strict chain-level extension of restriction from rational constants to the chosen derived
pushforward complex across the singular-cochain resolution. -/
def singularResolutionRestriction
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    singularCochainSheafComplexInt X ℚ ⟶
      derivedPushforwardComplementConstantRationalComplexInt X Z :=
  CochainComplex.liftToInjective
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ)

/-- Replacing rational constants by their singular-cochain resolution gives a quasi-isomorphic
mapping-cone model for supported cohomology. -/
def rationalSupportConeToSingularResolutionCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalCohomologyWithSupportComplex X Z ⟶
      CochainComplex.mappingCone (singularResolutionRestriction X Z hZ) :=
  CochainComplex.sourceReplacementConeMap
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ)

noncomputable instance rationalSupportConeToSingularResolutionCone_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (rationalSupportConeToSingularResolutionCone X Z hZ) := by
  change QuasiIso (CochainComplex.sourceReplacementConeMap
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ))
  infer_instance

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{0}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

end Topology.IsOpenEmbedding

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

section

variable {A S I : CochainComplex C ℤ}
  [A.IsStrictlyGE 0] [S.IsStrictlyGE 0] [I.IsStrictlyGE 0]
  (a : A ⟶ S) [Mono a] [QuasiIso a]
  (r : A ⟶ I)

end

end CochainComplex

namespace AlgebraicTopology.Singular

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

variable [IsIntegral X.left] [Smooth X.hom]

attribute [local instance] bettiSupportComparisonHasDerivedCategory
  bettiSupportComparisonMono bettiSupportComparisonQuasiIso

set_option backward.isDefEq.respectTransparency false in
/-- The singular-resolution restriction strictly extends restriction of rational constants. -/
lemma rationalToSingular_comp_singularResolutionRestriction
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalToSingularCochainComplexInt X ≫
        singularResolutionRestriction X Z hZ =
      rationalRestrictionComplexInt X Z :=
  CochainComplex.comp_liftToInjective
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ)

end AlgebraicGeometry.ComplexPoint
