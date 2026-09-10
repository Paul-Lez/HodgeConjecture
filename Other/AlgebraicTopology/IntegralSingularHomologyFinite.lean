/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.FiniteGoodCoverNerveHomology
public import Other.AlgebraicTopology.SingularExcisionScalar
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.RingTheory.Finiteness.Basic

import Other.AlgebraicTopology.SingularSubdivisionCochainSheaf

/-!
# Finiteness of integral singular homology in the `ModuleCat ℤ` model

`integralSingularHomology_module_finite` proves that a space with a finite good cover has
finitely generated integral singular homology, for the singular chain complex with values in
`AddCommGrpCat`.  This file transports that statement to the singular chain complex with
values in `ModuleCat ℤ` (the model used on the cochain side), by identifying the two complexes
through the forgetful equivalence `forget₂ (ModuleCat ℤ) AddCommGrpCat`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- The inverse of the coefficient map `integralToScalarChainComponent ℤ X n`. -/
def scalarToIntegralChainComponent (X : SSet.{0}) (n : ℕ) :
    (scalarForget ℤ).obj ((ScalarSimplicialChainComplex ℤ X).X n) ⟶
      (X.chainComplex (AddCommGrpCat.of ℤ)).X n :=
  (isColimitOfPreserves (scalarForget ℤ)
    (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)).desc
    (Cocone.mk _
      { app := fun x ↦ AddCommGrpCat.ofHom (Int.castAddHom ℤ) ≫
          X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as
        naturality := fun ⟨x⟩ ⟨y⟩ f ↦ by
          obtain rfl := Discrete.eq_of_hom f
          simp })

@[reassoc]
lemma forget_iota_scalarToIntegralChainComponent (X : SSet.{0}) (n : ℕ) (x : X _⦋n⦌) :
    (scalarForget ℤ).map (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x) ≫
        scalarToIntegralChainComponent X n =
      AddCommGrpCat.ofHom (Int.castAddHom ℤ) ≫
        X.ιChainComplex (R := AddCommGrpCat.of ℤ) x :=
  (isColimitOfPreserves (scalarForget ℤ)
    (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)).fac _ (Discrete.mk x)

lemma integralToScalarChainComponent_scalarToIntegralChainComponent (X : SSet.{0}) (n : ℕ) :
    integralToScalarChainComponent ℤ X n ≫ scalarToIntegralChainComponent X n = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_integralToScalarChainComponent_assoc, forget_iota_scalarToIntegralChainComponent,
    Category.comp_id, ← Category.assoc, ← AddCommGrpCat.ofHom_comp, Int.castAddHom_int,
    AddMonoidHom.id_comp, AddCommGrpCat.ofHom_id, Category.id_comp]

lemma scalarToIntegralChainComponent_integralToScalarChainComponent (X : SSet.{0}) (n : ℕ) :
    scalarToIntegralChainComponent X n ≫ integralToScalarChainComponent ℤ X n = 𝟙 _ := by
  refine (isColimitOfPreserves (scalarForget ℤ)
    (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)).hom_ext fun ⟨x⟩ ↦ ?_
  change (scalarForget ℤ).map (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x) ≫
    (scalarToIntegralChainComponent X n ≫ integralToScalarChainComponent ℤ X n) =
    (scalarForget ℤ).map (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x) ≫ 𝟙 _
  rw [forget_iota_scalarToIntegralChainComponent_assoc, iota_integralToScalarChainComponent,
    Category.comp_id, ← Category.assoc, ← AddCommGrpCat.ofHom_comp, Int.castAddHom_int,
    AddMonoidHom.id_comp, AddCommGrpCat.ofHom_id]
  exact Category.id_comp _

/-- The coefficient map from integral chains to `ℤ`-module chains is an isomorphism in each
degree. -/
def integralToScalarChainComponentIso (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ≅
      (scalarForget ℤ).obj ((ScalarSimplicialChainComplex ℤ X).X n) where
  hom := integralToScalarChainComponent ℤ X n
  inv := scalarToIntegralChainComponent X n
  hom_inv_id := integralToScalarChainComponent_scalarToIntegralChainComponent X n
  inv_hom_id := scalarToIntegralChainComponent_integralToScalarChainComponent X n

/-- The integral simplicial chain complex is isomorphic to the underlying complex of abelian
groups of the simplicial chain complex with coefficients in the `ℤ`-module `ℤ`. -/
def integralChainComplexIso (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ≅
      ((scalarForget ℤ).mapHomologicalComplex _).obj (ScalarSimplicialChainComplex ℤ X) :=
  HomologicalComplex.Hom.isoOfComponents (integralToScalarChainComponentIso X) fun i j hij ↦ by
    simp only [ComplexShape.down_Rel] at hij
    subst hij
    exact integralToScalarChainComponent_comm_d ℤ X j

/-- Forgetting the `ℤ`-module structure commutes with taking homology of the simplicial chain
complex with coefficients in `ℤ`. -/
def scalarForgetHomologyIso (X : SSet.{0}) (n : ℕ) :
    (((scalarForget ℤ).mapHomologicalComplex _).obj (ScalarSimplicialChainComplex ℤ X)).homology n
      ≅ (scalarForget ℤ).obj ((ScalarSimplicialChainComplex ℤ X).homology n) :=
  ShortComplex.mapHomologyIso ((ScalarSimplicialChainComplex ℤ X).sc n) (scalarForget ℤ)

/-- The integral homology of a simplicial set, computed in `AddCommGrpCat`, is additively
equivalent to its homology computed in `ModuleCat ℤ`. -/
def integralHomologyAddEquiv (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).homology n ≃+
      (ScalarSimplicialChainComplex ℤ X).homology n :=
  ((HomologicalComplex.homologyMapIso (integralChainComplexIso X) n).addCommGroupIsoToAddEquiv).trans
    (scalarForgetHomologyIso X n).addCommGroupIsoToAddEquiv

/-- Transport of finite generation of integral simplicial homology from the `AddCommGrpCat`
model to the `ModuleCat ℤ` model. -/
theorem module_finite_scalarHomology_of_module_finite_integralHomology (X : SSet.{0}) (n : ℕ)
    (h : Module.Finite ℤ ((X.chainComplex (AddCommGrpCat.of ℤ)).homology n)) :
    Module.Finite ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).homology n) :=
  Module.Finite.equiv (integralHomologyAddEquiv X n).toIntLinearEquiv

/-- A space with a finite good cover has finitely generated integral singular homology in every
degree, for the singular chain complex with coefficients in the `ℤ`-module `ℤ`. -/
theorem singularChainComplex_homology_module_finite_of_finiteGoodCover
    {ι : Type} [LinearOrder ι] {X : TopCat.{0}} {U : ι → Set X} (h : FiniteGoodCover X U) (n : ℕ) :
    Module.Finite ℤ (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).homology n) :=
  module_finite_scalarHomology_of_module_finite_integralHomology (TopCat.toSSet.obj X) n
    (FiniteGoodCover.integralSingularHomology_module_finite h n)

example {ι : Type} [LinearOrder ι] {X : TopCat.{0}} {U : ι → Set X} (h : FiniteGoodCover X U)
    (n : ℕ) : Module.Finite ℤ ((SingularChainComplex ℤ X).homology n) :=
  singularChainComplex_homology_module_finite_of_finiteGoodCover h n

end AlgebraicTopology.Singular
