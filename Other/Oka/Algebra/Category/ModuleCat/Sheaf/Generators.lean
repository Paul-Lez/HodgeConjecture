/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Data.Finite.Sum
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Other.Oka.CategoryTheory.Sites.Over

/-! # Finite-type sheaves of modules -/

@[expose] public section

universe w u v' u' v₂ u₂

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

section

variable [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]


@[simps]
noncomputable def LocalGeneratorsData.ofEpi {M N : SheafOfModules.{u} R}
    (σ : M.LocalGeneratorsData.{w}) (f : M ⟶ N) [∀ (X : C), Epi (f.over X)] :
    N.LocalGeneratorsData.{w} where
  I := σ.I
  X := σ.X
  coversTop := σ.coversTop
  generators i := (σ.generators i).ofEpi (f.over (σ.X i))

instance {M N : SheafOfModules.{u} R} (σ : M.LocalGeneratorsData.{w}) (f : M ⟶ N)
    [∀ (X : C), Epi (f.over X)] [σ.IsFiniteType] : (σ.ofEpi f).IsFiniteType where
  isFiniteType i :=
    haveI : (σ.generators i).IsFiniteType :=
      LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i
    inferInstanceAs ((σ.generators i).ofEpi (f.over (σ.X i))).IsFiniteType


lemma IsFiniteType.of_epi_over {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [∀ (X : C), Epi (f.over X)] [M.IsFiniteType] : N.IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨σ, _⟩ := IsFiniteType.exists_localGeneratorsData M
    exact ⟨σ.ofEpi f, inferInstance⟩


lemma IsFiniteType.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] :
    N.IsFiniteType :=
  haveI (X : C) : Epi (e.hom.over X) := inferInstance
  .of_epi_over e.hom


lemma isFiniteType_of_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    [M.IsFiniteType] : N.IsFiniteType :=
  .of_iso (asIso f)

instance {M : SheafOfModules.{u} R} (σ : M.LocalGeneratorsData.{w}) [σ.IsFiniteType] :
    σ.shrink.IsFiniteType where
  isFiniteType i := LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i.2.choose

variable (R) in
@[inherit_doc IsFiniteType]
abbrev isFiniteType : ObjectProperty (SheafOfModules.{u} R) :=
  IsFiniteType

instance : (isFiniteType R).IsClosedUnderIsomorphisms where
  of_iso e h := letI := h; .of_iso e


lemma IsFiniteType.of_epi [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [Epi f] [M.IsFiniteType] : N.IsFiniteType :=
  haveI (X : C) : Epi (f.over X) := inferInstance
  .of_epi_over f

end

section map

variable [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {D : Type u₂} [Category.{v₂, u₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]

variable (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)


@[simps I X]
noncomputable def LocalGeneratorsData.pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.LocalGeneratorsData) :
    LocalGeneratorsData ((pushforward φ).obj M) where
  I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
    refine K.superset_covering ?_ <| G.cover_lift K _ (P.coversTop (G.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  generators i :=
    letI G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
    letI ψ : S.over i.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1) (J.over (P.X i.2.1))).obj
          (R.over (P.X i.2.1)) :=
      ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
    letI overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      SheafOfModules.pushforward (𝟙 _)
    letI e : (SheafOfModules.pushforward ψ).obj (unit (R.over (P.X i.snd.fst))) ≅
      unit (S.over i.fst) := overS.mapIso η
    haveI : PreservesColimitsOfSize.{u, u, _} (SheafOfModules.pushforward ψ) := h _ _ _
    (P.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm

instance (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.LocalGeneratorsData) [P.IsFiniteType] :
    (P.pushforward G φ η h).IsFiniteType where
  isFiniteType i :=
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := P) i.2.1
    ⟨inferInstanceAs (Finite (P.generators i.2.1).I)⟩


lemma isFiniteType_pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    IsFiniteType ((pushforward φ).obj M) := by
  obtain ⟨P, _⟩ := IsFiniteType.exists_localGeneratorsData M
  exact ⟨(P.pushforward G φ η h).shrink, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in

lemma isFiniteType_pushforward_of_isLeftAdjoint (η : (pushforward φ).obj (unit R) ≅ unit S)
    [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    IsFiniteType ((pushforward φ).obj M) := by
  apply +allowSynthFailures isFiniteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

end map

section bind

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]


noncomputable def LocalGeneratorsData.bind {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, LocalGeneratorsData (M.over (X i))) :
    M.LocalGeneratorsData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i ↦ (D i).coversTop)
  generators i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    (((D i.1).generators i.2).map e.inverse (.refl _)).ofEpi
      (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over (X i.1)).over ((D i.1).X i.2)))).hom

instance {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, LocalGeneratorsData (M.over (X i)))
    [∀ i, (D i).IsFiniteType] : (LocalGeneratorsData.bind M X hX D).IsFiniteType where
  isFiniteType i :=
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := D i.1) i.2
    ⟨inferInstanceAs (Finite ((D i.1).generators i.2).I)⟩


lemma IsFiniteType.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, IsFiniteType (M.over (X i))] :
    M.IsFiniteType := by
  have h (i : I) := IsFiniteType.exists_localGeneratorsData (M.over (X i))
  choose D hD using h
  haveI := hD
  exact ⟨(LocalGeneratorsData.bind M X hX D).shrink, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in

lemma IsFiniteType.over
    [HasPullbacks C] [HasBinaryProducts C] (M : SheafOfModules.{u} R) (X : C)
    [M.IsFiniteType] : IsFiniteType (M.over X) :=
  isFiniteType_pushforward_of_isLeftAdjoint _ _ (Iso.refl _)


lemma IsFiniteType.of_coversTop_of_forall {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, IsFiniteType (R := R.over (X i)) (M.over (X i))) :
    M.IsFiniteType :=
  haveI := h
  .of_coversTop M X hX

end bind

section biprod

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]


noncomputable def freeGeneratingSections (I : Type u) :
    (free (R := R) I).GeneratingSections where
  I := I
  s := freeSection
  epi := by
    rw [show (freeSection : I → _) = (free (R := R) I).freeHomEquiv (𝟙 _) from rfl,
      Equiv.symm_apply_apply]
    infer_instance

instance (I : Type u) [Finite I] : (freeGeneratingSections (R := R) I).IsFiniteType :=
  ⟨inferInstanceAs (Finite I)⟩


noncomputable def GeneratingSections.biprod {A B : SheafOfModules.{u} R}
    (σA : A.GeneratingSections) (σB : B.GeneratingSections) :
    (A ⊞ B).GeneratingSections where
  I := σA.I ⊕ σB.I
  s := (A ⊞ B).freeHomEquiv
    ((freeSumIso σA.I σB.I).inv ≫ coprod.map σA.π σB.π ≫ (biprod.isoCoprod A B).inv)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

instance {A B : SheafOfModules.{u} R} (σA : A.GeneratingSections) (σB : B.GeneratingSections)
    [σA.IsFiniteType] [σB.IsFiniteType] : (σA.biprod σB).IsFiniteType :=
  ⟨inferInstanceAs (Finite (σA.I ⊕ σB.I))⟩

end biprod

section ofGeneratingSections

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C]


lemma IsFiniteType.of_generatingSections {M : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) [σ.IsFiniteType] : M.IsFiniteType where
  exists_localGeneratorsData :=
    ⟨σ.localGeneratorsData, ⟨fun _ ↦ ⟨inferInstanceAs (Finite σ.I)⟩⟩⟩

end ofGeneratingSections

section freeBiprod

variable {C : Type u} [SmallCategory C] [HasPullbacks C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}


lemma isFiniteType_over_free_biprod {I : Type u} [Finite I] (M : SheafOfModules.{u} R) {X : C}
    (σ : (M.over X).GeneratingSections) [σ.IsFiniteType] :
    IsFiniteType (R := R.over X) ((free (R := R) I ⊞ M).over X) := by
  haveI : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : IsFiniteType (R := R.over X) ((free (R := R.over X) I) ⊞ (M.over X)) :=
    IsFiniteType.of_generatingSections (M := (free (R := R.over X) I) ⊞ (M.over X))
      ((freeGeneratingSections I).biprod σ)
  exact IsFiniteType.of_iso (M := (free (R := R.over X) I) ⊞ (M.over X))
    (biprod.mapIso (overFreeIso I X) (Iso.refl _) ≪≫ (overBiprodIso (free (R := R) I) M X).symm)


lemma isFiniteType_free_biprod {I : Type u} [Finite I] (M : SheafOfModules.{u} R)
    [M.IsFiniteType] : (free (R := R) I ⊞ M).IsFiniteType := by
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData M
  refine IsFiniteType.of_coversTop_of_forall (free (R := R) I ⊞ M) σ.X σ.coversTop (fun i ↦ ?_)
  haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i
  exact isFiniteType_over_free_biprod M (σ.generators i)

end freeBiprod

section overOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}


lemma isFiniteType_overOverEquivalence_functor_obj {X : C} {Y : Over X}
    (M' : SheafOfModules.{u} (R.over Y.left)) [M'.IsFiniteType] :
    IsFiniteType (R := (R.over X).over Y) ((overOverEquivalence X Y).functor.obj M') := by
  exact isFiniteType_pushforward_of_isLeftAdjoint (Over.iteratedSliceEquiv Y).functor (𝟙 _)
    (by exact Iso.refl _)


lemma isFiniteType_overOverEquivalence_inverse_obj {X : C} {Y : Over X}
    (N' : SheafOfModules.{u} ((R.over X).over Y)) [N'.IsFiniteType] :
    IsFiniteType (R := R.over Y.left) ((overOverEquivalence X Y).inverse.obj N') := by
  exact isFiniteType_pushforward_of_isLeftAdjoint (Over.iteratedSliceEquiv Y).inverse (𝟙 _)
    (by exact Iso.refl _)


lemma IsFiniteType.of_overOverEquivalence_functor_obj {X : C} {Y : Over X}
    {M' : SheafOfModules.{u} (R.over Y.left)}
    (h : IsFiniteType (R := (R.over X).over Y) ((overOverEquivalence X Y).functor.obj M')) :
    M'.IsFiniteType :=
  haveI := h
  haveI : IsFiniteType (R := R.over Y.left)
      ((overOverEquivalence (R := R) X Y).inverse.obj
        ((overOverEquivalence (R := R) X Y).functor.obj M')) :=
    isFiniteType_overOverEquivalence_inverse_obj _
  IsFiniteType.of_iso (M := (overOverEquivalence (R := R) X Y).inverse.obj
      ((overOverEquivalence (R := R) X Y).functor.obj M'))
    ((overOverEquivalence (R := R) X Y).unitIso.symm.app M')


lemma IsFiniteType.of_overOverEquivalence_inverse_obj {X : C} {Y : Over X}
    {N' : SheafOfModules.{u} ((R.over X).over Y)}
    (h : IsFiniteType (R := R.over Y.left) ((overOverEquivalence X Y).inverse.obj N')) :
    N'.IsFiniteType :=
  haveI := h
  haveI : IsFiniteType (R := (R.over X).over Y)
      ((overOverEquivalence (R := R) X Y).functor.obj
        ((overOverEquivalence (R := R) X Y).inverse.obj N')) :=
    isFiniteType_overOverEquivalence_functor_obj _
  IsFiniteType.of_iso (M := (overOverEquivalence (R := R) X Y).functor.obj
      ((overOverEquivalence (R := R) X Y).inverse.obj N'))
    ((overOverEquivalence (R := R) X Y).counitIso.app N')

end overOver

section restrict

variable [HasPullbacks C] [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]


noncomputable def GeneratingSections.restrict {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (σ : (M.over Y).GeneratingSections) : (M.over X).GeneratingSections :=
  (σ.map (overMap R f) (overMapUnitIso f).symm).ofEpi (((overFunctorMap R f).app M).hom)


instance GeneratingSections.isFiniteType_restrict {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (σ : (M.over Y).GeneratingSections) [σ.IsFiniteType] : (σ.restrict f).IsFiniteType := by
  unfold GeneratingSections.restrict
  infer_instance

end restrict

end SheafOfModules
