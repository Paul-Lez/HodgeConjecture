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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import HodgeConjecture.Mathlib.Algebra.Category.ModuleCat.Sheafification
public import HodgeConjecture.Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The holomorphic de Rham complex in `ModuleCat ℂ`

This file gives the ModuleCat-valued counterparts of the holomorphic de Rham objects. The
underlying linear maps are the maps on holomorphic forms from `AnalyticDifferentialForms`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Sheaves of complex vector spaces on the analytic space of `X`. -/
abbrev AnalyticModuleSheaf :=
  TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))

/-- The presheaf of holomorphic `p`-forms with its complex vector-space structure. -/
def holomorphicDeRhamModulePresheaf [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X)) where
  obj U := ModuleCat.of ℂ (HolomorphicForm X d U p)
  map {U V} i := ModuleCat.ofHom (holomorphicFormRestriction X d i p)
  map_id U := by
    apply ModuleCat.hom_ext
    exact holomorphicFormRestriction_id X d U p
  map_comp i j := by
    apply ModuleCat.hom_ext
    exact holomorphicFormRestriction_comp X d i j p

/-- Holomorphic differential forms vanish in degrees above the complex dimension, already before
sheafification. -/
private lemma holomorphicDeRhamModulePresheaf_isZero_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    IsZero (holomorphicDeRhamModulePresheaf X d p) := by
  apply Functor.isZero
  intro U
  let : Subsingleton ((holomorphicDeRhamModulePresheaf X d p).obj U) :=
    ⟨fun x y => by
      rw [holomorphicForm_eq_zero_of_lt X d U hp x,
        holomorphicForm_eq_zero_of_lt X d U hp y]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Exterior differentiation as a morphism of complex-valued presheaves. -/
def holomorphicDeRhamModuleDifferential [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamModulePresheaf X d p ⟶
      holomorphicDeRhamModulePresheaf X d (p + 1) where
  app U := ModuleCat.ofHom (holomorphicFormDifferential X d U p)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    ext x
    exact (holomorphicFormRestriction_differential X d i p x).symm

lemma holomorphicDeRhamModuleDifferential_comp
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamModuleDifferential X d p ≫
      holomorphicDeRhamModuleDifferential X d (p + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  ext x
  exact holomorphicFormDifferential_squared X d U p x

/-- The nonnegative complex of presheaves of complex vector spaces given by holomorphic forms. -/
def holomorphicDeRhamModulePresheafComplex [SmoothOfRelativeDimension d X.hom] :
    CochainComplex
      (TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamModulePresheaf X d)
    (holomorphicDeRhamModuleDifferential X d)
    (holomorphicDeRhamModuleDifferential_comp X d)

@[simp] lemma holomorphicDeRhamModulePresheafComplex_d
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (holomorphicDeRhamModulePresheafComplex X d).d p (p + 1) =
      holomorphicDeRhamModuleDifferential X d p := by
  simp [holomorphicDeRhamModulePresheafComplex]

/-- The sheafification of the presheaf of holomorphic `p`-forms in `ModuleCat ℂ`. -/
def holomorphicDeRhamModuleSheaf [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    AnalyticModuleSheaf X :=
  letI J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (presheafToSheaf J (ModuleCat ℂ)).obj
    (holomorphicDeRhamModulePresheaf X d p)

/-- The sheaf of holomorphic `p`-forms is zero for `p` above the complex dimension. -/
lemma holomorphicDeRhamModuleSheaf_isZero_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    IsZero (holomorphicDeRhamModuleSheaf X d p) := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  exact (presheafToSheaf J (ModuleCat ℂ)).map_isZero
    (holomorphicDeRhamModulePresheaf_isZero_of_lt X d hp)

/-- Exterior differentiation on the sheaves of complex-valued holomorphic forms. -/
def holomorphicDeRhamModuleSheafDifferential
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamModuleSheaf X d p ⟶
      holomorphicDeRhamModuleSheaf X d (p + 1) :=
  letI J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (presheafToSheaf J (ModuleCat ℂ)).map
    (holomorphicDeRhamModuleDifferential X d p)

/-- The holomorphic de Rham complex of sheaves of complex vector spaces in natural degrees. -/
def holomorphicDeRhamModuleComplex [SmoothOfRelativeDimension d X.hom] :
    CochainComplex (AnalyticModuleSheaf X) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamModuleSheaf X d)
    (holomorphicDeRhamModuleSheafDifferential X d)
    (fun p => by
      let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
      change (presheafToSheaf J (ModuleCat ℂ)).map
          (holomorphicDeRhamModuleDifferential X d p) ≫
        (presheafToSheaf J (ModuleCat ℂ)).map
          (holomorphicDeRhamModuleDifferential X d (p + 1)) = 0
      rw [← Functor.map_comp, holomorphicDeRhamModuleDifferential_comp,
        Functor.map_zero])

@[simp] lemma holomorphicDeRhamModuleComplex_d
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (holomorphicDeRhamModuleComplex X d).d p (p + 1) =
      holomorphicDeRhamModuleSheafDifferential X d p := by
  simp [holomorphicDeRhamModuleComplex]

/-- The constant presheaf of complex vector spaces on the analytic space of `X`. -/
def constantComplexModulePresheaf :
    TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X)) :=
  (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (ModuleCat.of ℂ ℂ)

/-- The constant sheaf of complex vector spaces on the analytic space of `X`. -/
def constantComplexModuleSheaf : AnalyticModuleSheaf X :=
  letI J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J (ModuleCat ℂ)).obj (ModuleCat.of ℂ ℂ)

/-- Restrict the scalars on an analytic sheaf from `ℂ` to `ℤ`. -/
abbrev analyticModuleSheafToModuleInt :
    AnalyticModuleSheaf X ⥤
      TopCat.Sheaf (ModuleCat ℤ) (TopCat.of (ComplexPoint X)) :=
  CategoryTheory.Sheaf.restrictScalars
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (algebraMap ℤ ℂ)

/-- Forget the complex vector-space structure on an analytic sheaf. -/
abbrev analyticModuleSheafToAddCommGrp :
    AnalyticModuleSheaf X ⥤ TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  analyticModuleSheafToModuleInt X ⋙
    sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (forget₂ (ModuleCat ℤ) AddCommGrpCat)

instance analyticModuleSheafToAddCommGrp_preservesZeroMorphisms :
    (analyticModuleSheafToAddCommGrp X).PreservesZeroMorphisms := by
  refine ⟨fun F G => ?_⟩
  rfl

instance analyticModuleSheafToAddCommGrp_additive :
    (analyticModuleSheafToAddCommGrp X).Additive := by
  refine ⟨?_⟩
  intro X Y f g
  rfl

noncomputable instance analyticModuleSheafToAddCommGrp_preservesFiniteLimits :
    PreservesFiniteLimits (analyticModuleSheafToAddCommGrp X) := by
  let h₁ : PreservesFiniteLimits (analyticModuleSheafToModuleInt X) :=
    CategoryTheory.Sheaf.restrictScalars_preservesFiniteLimits _ _
  let h₂ : PreservesFiniteLimits
      (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (forget₂ (ModuleCat ℤ) AddCommGrpCat)) :=
    ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteLimits _
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

noncomputable instance analyticModuleSheafToAddCommGrp_preservesFiniteColimits :
    PreservesFiniteColimits (analyticModuleSheafToAddCommGrp X) := by
  exact CategoryTheory.Sheaf.moduleForget_preservesFiniteColimits _
    (ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteColimits _)

instance analyticModuleSheafToAddCommGrp_reflectsIsomorphisms :
    (analyticModuleSheafToAddCommGrp X).ReflectsIsomorphisms := by
  let h₁ : (analyticModuleSheafToModuleInt X).ReflectsIsomorphisms :=
    CategoryTheory.Sheaf.restrictScalars_reflectsIsomorphisms _ _
  let h₂ :
      (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (forget₂ (ModuleCat ℤ) AddCommGrpCat)).ReflectsIsomorphisms := by
    infer_instance
  exact @reflectsIsomorphisms_comp _ _ _ _ _ _ _ _ h₁ h₂

noncomputable instance analyticModuleSheafToAddCommGrp_preservesHomology :
    (analyticModuleSheafToAddCommGrp X).PreservesHomology :=
  Functor.preservesHomologyOfExact _

noncomputable def analyticModuleSheafificationForgetNatIso :
    (presheafToSheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (ModuleCat ℂ) ⋙
      analyticModuleSheafToAddCommGrp X) ≅
      (Functor.whiskeringRight
          (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ (ModuleCat ℂ) AddCommGrpCat).obj
        (forget₂ (ModuleCat ℂ) AddCommGrpCat) ⋙
        presheafToSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat :=
  Functor.isoWhiskerRight
      (CategoryTheory.sheafComposeNatIso
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (ModuleCat.restrictScalars (algebraMap ℤ ℂ))
        (sheafificationAdjunction
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (ModuleCat ℂ))
        (sheafificationAdjunction
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (ModuleCat ℤ))).symm
      (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (forget₂ (ModuleCat ℤ) AddCommGrpCat)) ≪≫
    Functor.isoWhiskerLeft
      ((Functor.whiskeringRight
        (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ (ModuleCat ℂ) (ModuleCat ℤ)).obj
          (ModuleCat.restrictScalars (algebraMap ℤ ℂ)))
      (CategoryTheory.sheafComposeNatIso
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (forget₂ (ModuleCat ℤ) AddCommGrpCat)
        (sheafificationAdjunction
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (ModuleCat ℤ))
        (sheafificationAdjunction
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat)).symm

/-- Forgetting scalars commutes with sheafification of a complex presheaf. -/
noncomputable def analyticModuleSheafificationForgetIso
    (P : TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) :
    (analyticModuleSheafToAddCommGrp X).obj
        ((presheafToSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (ModuleCat ℂ)).obj P) ≅
      (presheafToSheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj
        (P ⋙ (forget₂ (ModuleCat ℂ) AddCommGrpCat)) :=
  (analyticModuleSheafificationForgetNatIso X).app P

lemma analyticModuleSheafificationForgetIso_hom_naturality
    {P Q : TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))}
    (f : P ⟶ Q) :
    (analyticModuleSheafificationForgetIso X P).hom ≫
        (presheafToSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).map
          (Functor.whiskerRight f (forget₂ (ModuleCat ℂ) AddCommGrpCat)) =
      (analyticModuleSheafToAddCommGrp X).map
          ((presheafToSheaf
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (ModuleCat ℂ)).map f) ≫
        (analyticModuleSheafificationForgetIso X Q).hom :=
  ((analyticModuleSheafificationForgetNatIso X).hom.naturality f).symm

noncomputable def holomorphicDeRhamModuleSheaf_forgetIso
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (analyticModuleSheafToAddCommGrp X).obj
        (holomorphicDeRhamModuleSheaf X d p) ≅
      holomorphicDeRhamSheaf X d p :=
  analyticModuleSheafificationForgetIso X (holomorphicDeRhamModulePresheaf X d p)

noncomputable def constantComplexModuleSheaf_forgetIso :
    (analyticModuleSheafToAddCommGrp X).obj (constantComplexModuleSheaf X) ≅
      𝓒(↧(ComplexPoint X); ℂ) :=
  analyticModuleSheafificationForgetIso X (constantComplexModulePresheaf X)

noncomputable def holomorphicDeRhamModuleComplex_forgetIso
    [SmoothOfRelativeDimension d X.hom] :
    ((analyticModuleSheafToAddCommGrp X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (holomorphicDeRhamModuleComplex X d) ≅
  holomorphicDeRhamComplex X d :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => by
      change (analyticModuleSheafToAddCommGrp X).obj
          (holomorphicDeRhamModuleSheaf X d p) ≅ holomorphicDeRhamSheaf X d p
      exact holomorphicDeRhamModuleSheaf_forgetIso X d p)
    (fun p q hpq => by
      obtain rfl := hpq
      dsimp only [holomorphicDeRhamModuleComplex, holomorphicDeRhamComplex,
        holomorphicDeRhamModuleSheafDifferential, holomorphicDeRhamSheafDifferential]
      let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
      rw [CochainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
      simp only [CochainComplex.of_d]
      change
        (analyticModuleSheafificationForgetIso X
          (holomorphicDeRhamModulePresheaf X d p)).hom ≫
            (presheafToSheaf J AddCommGrpCat).map
              (holomorphicDeRhamDifferential X d p) =
          (analyticModuleSheafToAddCommGrp X).map
              ((presheafToSheaf J (ModuleCat ℂ)).map
                (holomorphicDeRhamModuleDifferential X d p)) ≫
            (analyticModuleSheafificationForgetIso X
              (holomorphicDeRhamModulePresheaf X d (p + 1))).hom
      have h := analyticModuleSheafificationForgetIso_hom_naturality X
        (holomorphicDeRhamModuleDifferential X d p)
      have hF :
          Functor.whiskerRight (holomorphicDeRhamModuleDifferential X d p)
              (forget₂ (ModuleCat ℂ) AddCommGrpCat) =
            holomorphicDeRhamDifferential X d p := by
        ext U
        rfl
      rw [hF] at h
      exact h)

noncomputable def constantsToHolomorphicDeRhamModuleComplex_forgetIso :
    ((analyticModuleSheafToAddCommGrp X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀ (AnalyticModuleSheaf X)).obj
          (constantComplexModuleSheaf X)) ≅
      (CochainComplex.single₀
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
          𝓒(↧(ComplexPoint X); ℂ) :=
  (HomologicalComplex.singleMapHomologicalComplex
      (analyticModuleSheafToAddCommGrp X) (.up ℕ) 0).app (constantComplexModuleSheaf X) ≪≫
    (CochainComplex.single₀ _).mapIso (constantComplexModuleSheaf_forgetIso X)

/-- The map from complex constants to holomorphic zero-forms as a map of complex presheaves. -/
def constantsToHolomorphicDeRhamModuleZero
    [SmoothOfRelativeDimension d X.hom] :
    constantComplexModulePresheaf X ⟶ holomorphicDeRhamModulePresheaf X d 0 where
  app U := ModuleCat.ofHom (holomorphicFormOfConstant X d U)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (holomorphicFormRestriction_ofConstant X d i c).symm

lemma constantsToHolomorphicDeRhamModuleZero_comp_differential
    [SmoothOfRelativeDimension d X.hom] :
    constantsToHolomorphicDeRhamModuleZero X d ≫
      holomorphicDeRhamModuleDifferential X d 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact holomorphicFormDifferential_ofConstant X d U c

/-- The map from the constant sheaf to the sheaf of holomorphic zero-forms. -/
def constantsToHolomorphicDeRhamModuleZeroSheaf
    [SmoothOfRelativeDimension d X.hom] :
    constantComplexModuleSheaf X ⟶ holomorphicDeRhamModuleSheaf X d 0 :=
  letI J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (presheafToSheaf J (ModuleCat ℂ)).map
    (constantsToHolomorphicDeRhamModuleZero X d)

lemma constantsToHolomorphicDeRhamModuleZeroSheaf_comp_differential
    [SmoothOfRelativeDimension d X.hom] :
    constantsToHolomorphicDeRhamModuleZeroSheaf X d ≫
      holomorphicDeRhamModuleSheafDifferential X d 0 = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J (ModuleCat ℂ)).map
      (constantsToHolomorphicDeRhamModuleZero X d) ≫
    (presheafToSheaf J (ModuleCat ℂ)).map
      (holomorphicDeRhamModuleDifferential X d 0) = 0
  rw [← Functor.map_comp, constantsToHolomorphicDeRhamModuleZero_comp_differential,
    Functor.map_zero]

/-- The constant complex in degree zero maps to the holomorphic de Rham complex. -/
def constantsToHolomorphicDeRhamModuleComplex
    [SmoothOfRelativeDimension d X.hom] :
    (CochainComplex.single₀ (AnalyticModuleSheaf X)).obj
        (constantComplexModuleSheaf X) ⟶
      holomorphicDeRhamModuleComplex X d :=
  (CochainComplex.fromSingle₀Equiv (holomorphicDeRhamModuleComplex X d)
    (constantComplexModuleSheaf X)).symm
      ⟨constantsToHolomorphicDeRhamModuleZeroSheaf X d, by
        rw [holomorphicDeRhamModuleComplex_d]
        exact constantsToHolomorphicDeRhamModuleZeroSheaf_comp_differential X d⟩

noncomputable def constantsToHolomorphicDeRhamModuleComplex_forgetArrowIso
    [SmoothOfRelativeDimension d X.hom] :
    Arrow.mk (((analyticModuleSheafToAddCommGrp X).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
      (constantsToHolomorphicDeRhamModuleComplex X d)) ≅
    Arrow.mk (constantsToHolomorphicDeRhamComplex X d) :=
  Arrow.isoMk (constantsToHolomorphicDeRhamModuleComplex_forgetIso X)
    (holomorphicDeRhamModuleComplex_forgetIso X d) (by
      apply HomologicalComplex.Hom.ext
      funext p
      rcases p with _ | p
      · dsimp [constantsToHolomorphicDeRhamModuleComplex_forgetIso,
          holomorphicDeRhamModuleComplex_forgetIso,
          constantsToHolomorphicDeRhamModuleComplex]
        exact analyticModuleSheafificationForgetIso_hom_naturality X
          (constantsToHolomorphicDeRhamModuleZero X d)
      · dsimp [constantsToHolomorphicDeRhamModuleComplex_forgetIso,
          holomorphicDeRhamModuleComplex_forgetIso,
          constantsToHolomorphicDeRhamModuleComplex]
        simp [CochainComplex.fromSingle₀Equiv, HomologicalComplex.mkHomFromSingle]
        exact (zero_comp).symm)

instance constantsToHolomorphicDeRhamModuleComplex_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (constantsToHolomorphicDeRhamModuleComplex X (dim X.left)) := by
  let F := analyticModuleSheafToAddCommGrp X
  let f := constantsToHolomorphicDeRhamModuleComplex X (dim X.left)
  let f' := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map f
  have hf' : QuasiIso f' := by
    apply (quasiIso_iff_of_arrow_mk_iso f' (constantsToHolomorphicDeRhamComplex X (dim X.left))
      (constantsToHolomorphicDeRhamModuleComplex_forgetArrowIso X (dim X.left))).mpr
    infer_instance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f F).mp hf'

/-- The constant complex as a bounded-below complex of sheaves of complex vector spaces. -/
abbrev constantComplexModuleSheafIntPlus :
    CochainComplex.Plus (AnalyticModuleSheaf X) :=
  (CochainComplex.Plus.single₀ (AnalyticModuleSheaf X)).obj
    (constantComplexModuleSheaf X)

/-- The constant complex as an integer-indexed complex of sheaves of complex vector spaces. -/
abbrev constantComplexModuleSheafInt :
    CochainComplex (AnalyticModuleSheaf X) ℤ :=
  (constantComplexModuleSheafIntPlus X).obj

/-- The integer-indexed holomorphic de Rham complex in `ModuleCat ℂ`. -/
def holomorphicDeRhamModuleComplexInt
    [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex (AnalyticModuleSheaf X) ℤ :=
  (holomorphicDeRhamModuleComplex X (dim X.left)).extend ComplexShape.embeddingUpNat

instance [IsIntegral X.left] [Smooth X.hom] :
    (holomorphicDeRhamModuleComplexInt X).IsStrictlyGE 0 := by
  unfold holomorphicDeRhamModuleComplexInt
  infer_instance

/-- The integer-indexed holomorphic de Rham complex vanishes in every degree above the complex
dimension. -/
lemma holomorphicDeRhamModuleComplexInt_isZero_X_of_lt
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (hn : (dim X.left : ℤ) < n) :
    IsZero ((holomorphicDeRhamModuleComplexInt X).X n) := by
  have hn0 : 0 ≤ n := by lia
  let p := n.toNat
  have hp : (p : ℤ) = n := by
    simp [p, Int.toNat_of_nonneg hn0]
  have hdp : dim X.left < p := by lia
  exact (holomorphicDeRhamModuleSheaf_isZero_of_lt X (dim X.left) hdp).of_iso
    ((holomorphicDeRhamModuleComplex X (dim X.left)).extendXIso
      ComplexShape.embeddingUpNat hp)

/-- The integer-indexed holomorphic de Rham complex is strictly supported in degrees at most the
complex dimension. -/
noncomputable instance holomorphicDeRhamModuleComplexInt_isStrictlyLE
    [IsIntegral X.left] [Smooth X.hom] :
    (holomorphicDeRhamModuleComplexInt X).IsStrictlySupported
      (ComplexShape.embeddingUpIntLE (dim X.left)) where
  isZero n hn := by
    rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hn
    exact holomorphicDeRhamModuleComplexInt_isZero_X_of_lt X n hn

/-- The constant-to-de Rham map in integer degrees. -/
def constantsToHolomorphicDeRhamModuleComplexInt
    [IsIntegral X.left] [Smooth X.hom] :
    constantComplexModuleSheafInt X ⟶ holomorphicDeRhamModuleComplexInt X :=
  HomologicalComplex.extendMap
    (constantsToHolomorphicDeRhamModuleComplex X (dim X.left)) ComplexShape.embeddingUpNat

instance constantsToHolomorphicDeRhamModuleComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (constantsToHolomorphicDeRhamModuleComplexInt X) :=
  (HomologicalComplex.quasiIso_extendMap_iff
    (constantsToHolomorphicDeRhamModuleComplex X (dim X.left))
    ComplexShape.embeddingUpNat).2 inferInstance

/-- The integer-indexed holomorphic de Rham complex as a bounded-below complex. -/
abbrev holomorphicDeRhamModuleComplexPlus
    [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex.Plus (AnalyticModuleSheaf X) :=
  ⟨holomorphicDeRhamModuleComplexInt X, ⟨0, inferInstance⟩⟩

end AlgebraicGeometry.ComplexPoint
