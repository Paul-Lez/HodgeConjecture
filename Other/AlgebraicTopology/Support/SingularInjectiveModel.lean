/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel
public import Other.AlgebraicTopology.Sheaf.OpenInjectiveResolutionLemmas

/-!
# Comparing the singular cochains with an injective resolution

On a space with a contractible open basis the singular-cochain augmentation resolves the constant
rational sheaf, and the augmentation extends to a chosen injective resolution.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomologicalComplex

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})
/-- Let `X` be a topological space. This is the integer-indexed complex in a chosen injective
resolution `ℚ_X → I^•` of the constant rational sheaf, with zero terms in negative degrees. -/
def rationalConstantInjectiveComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  -- An injective resolution `ℚ_X → I^•`.
  (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).cocomplex.extend
    ComplexShape.embeddingUpNat

instance rationalConstantInjectiveComplex_isStrictlyGE :
    (rationalConstantInjectiveComplex X).IsStrictlyGE 0 := by
  dsimp [rationalConstantInjectiveComplex]
  infer_instance

instance rationalConstantInjectiveComplex_injective (n : ℤ) :
    Injective ((rationalConstantInjectiveComplex X).X n) :=
  CochainComplex.injective_extend_nat _
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective n

variable (hX : ∀ (x : X) (V : Opens X), x ∈ V →
  ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)

/-- Let `X` be a topological space with a basis of contractible open sets. Write `C^•` for the
sheafified rational singular cochains and `ℚ_X → I^•` for a chosen injective resolution. This
chooses a map `C^• → I^•` whose composite with the constant-cochain inclusion `ℚ_X[0] → C^•`
equals the resolution augmentation. Complexes are indexed by natural numbers. -/
def singularToConstantInjectiveResolution :
    singularCochainSheafComplex ℚ X ⟶
      (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).cocomplex :=
  letI : Mono (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_mono ℚ X
  letI : QuasiIso (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hX
  CochainComplex.liftToInjectiveNat (constantsToSingularCochainSheafComplex ℚ X)
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective

/-- The comparison fixes the prescribed rational constant augmentation exactly. -/
@[reassoc (attr := simp)]
lemma constants_comp_singularToConstantInjectiveResolution :
    constantsToSingularCochainSheafComplex ℚ X ≫ singularToConstantInjectiveResolution X hX =
      (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι := by
  let : Mono (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_mono ℚ X
  let : QuasiIso (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hX
  exact CochainComplex.comp_liftToInjectiveNat _ _
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective

instance singularToConstantInjectiveResolution_quasiIso :
    QuasiIso (singularToConstantInjectiveResolution X hX) := by
  let a := constantsToSingularCochainSheafComplex ℚ X
  let : QuasiIso a :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hX
  have : QuasiIso (a ≫ singularToConstantInjectiveResolution X hX) := by
    rw [constants_comp_singularToConstantInjectiveResolution]
    exact (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).quasiIso
  exact quasiIso_of_comp_left a _

/-- Let `X` be a topological space with a basis of contractible open sets. This map from sheafified
rational singular cochains to a chosen injective resolution of `ℚ_X` extends the identity on
constant coefficients. Both complexes are indexed by integers and zero in negative degrees. -/
def singularToConstantInjectiveComplex :
    rationalSingularCochainComplex X ⟶ rationalConstantInjectiveComplex X :=
  HomologicalComplex.extendMap (singularToConstantInjectiveResolution X hX)
    ComplexShape.embeddingUpNat

instance singularToConstantInjectiveComplex_quasiIso :
    QuasiIso (singularToConstantInjectiveComplex X hX) :=
  (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance

/-- Let `X` have a basis of contractible open sets and let `U ⊆ X` be open. This map `Γ_{X \ U}(C^•)
→ Γ_{X \ U}(I^•)` restricts the augmentation-preserving comparison from sheafified rational
singular cochains `C^•` to an injective resolution `I^•` of `ℚ_X` to the subsheaves of sections
vanishing on `U`. -/
def supportedSingularToInjectiveComplex (U : Opens X) :
    supportedRationalSingularCochainComplex X U ⟶
      ((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
        (rationalConstantInjectiveComplex X) :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
    (singularToConstantInjectiveComplex X hX)

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V]

/-- Supported singular cochains compute the supported injective model, at the level of sheaf
complexes. -/
instance supportedSingularToInjectiveComplex_quasiIso (U : Opens X) :
    QuasiIso (supportedSingularToInjectiveComplex X hX U) :=
  TopCat.Sheaf.sheafSectionsSupportedOutside_map_quasiIso_of_flasque X U
    (singularToConstantInjectiveComplex X hX) 0 0 (fun _ => inferInstance) (fun _ => inferInstance)

end AlgebraicTopology.Singular
