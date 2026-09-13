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

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.MapOfLocalStalks

/-!
# Assembling constant-sheaf maps from locally represented stalk maps

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.MapOfLocalStalks`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

variable (A : AddCommGrpCat.{u}) (g : ∀ x : X, A ⟶ F.presheaf.stalk x)
  (hlocal : ∀ (a : A) (x : X), ∃ (U : Opens X) (_ : x ∈ U) (s : F.presheaf.obj (op U)),
    ∀ (y : X) (hy : y ∈ U), F.presheaf.germ U y hy s = g y a)

/-- The global section map is additive because equality can be checked on stalks. -/
def globalMapOfLocallyRepresentable : A ⟶ F.presheaf.obj (op ⊤) :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ sectionOfLocallyRepresentable F (fun x ↦ g x a) (hlocal a)
      map_zero' := by
        apply TopCat.Presheaf.section_ext F
        intro x _
        change F.presheaf.Γgerm x (sectionOfLocallyRepresentable F
          (fun x ↦ g x 0) (hlocal 0)) = F.presheaf.Γgerm x 0
        rw [sectionOfLocallyRepresentable_germ, map_zero, map_zero]
      map_add' := by
        intro a b
        apply TopCat.Presheaf.section_ext F
        intro x _
        change F.presheaf.Γgerm x _ = F.presheaf.Γgerm x (_ + _)
        simp only [map_add, sectionOfLocallyRepresentable_germ] }

/-- The actual presheaf map from constants, prior to sheafification. -/
def constantPresheafMapOfLocallyRepresentable :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ F.presheaf where
  app U := globalMapOfLocallyRepresentable F A g hlocal ≫
    F.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality {U V} i := by
    dsimp
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
    rfl

/-- Gluing followed by sheafification constructs the constant-sheaf map. -/
def constantSheafMapOfLocallyRepresentable :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A ⟶ F :=
  ⟨sheafifyLift (Opens.grothendieckTopology X)
    (constantPresheafMapOfLocallyRepresentable F A g hlocal) F.property⟩

variable {F}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical constant-sheaf stalk identification, directed from the coefficient
group to the stalk. Its map is the germ of an actual constant section. -/
def constantSheafStalkIso (A : AddCommGrpCat.{u}) (x : X) :
    A ≅ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).obj := by
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
  letI : IsIso (P.Γgerm x) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro a b hab
      obtain ⟨U, hx, i, j, hij⟩ := P.germ_eq (U := ⊤) (V := ⊤)
        x True.intro True.intro a b hab
      exact hij
    · intro t
      obtain ⟨U, hx, a, rfl⟩ := P.exists_germ_eq t
      exact ⟨a, (P.Γgerm_res_apply (i := homOfLE (show U ≤ ⊤ from le_top)) x hx a).symm⟩
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  exact asIso (P.Γgerm x) ≪≫
    asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))

variable (F)

end TopCat.Sheaf

end

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

variable (A : AddCommGrpCat.{u}) (g : ∀ x : X, A ⟶ F.presheaf.stalk x)
  (hlocal : ∀ (a : A) (x : X), ∃ (U : Opens X) (_ : x ∈ U) (s : F.presheaf.obj (op U)),
    ∀ (y : X) (hy : y ∈ U), F.presheaf.germ U y hy s = g y a)

/-- The global additive map has exactly the specified stalk maps. -/
@[reassoc]
theorem globalMapOfLocallyRepresentable_germ (x : X) :
    globalMapOfLocallyRepresentable F A g hlocal ≫ F.presheaf.Γgerm x = g x := by
  apply AddCommGrpCat.hom_ext
  ext a
  exact sectionOfLocallyRepresentable_germ F (fun x ↦ g x a) (hlocal a) x

/-- The sheaf map agrees with the explicitly constructed map on constant sections. -/
@[reassoc]
theorem constantSheafMapOfLocallyRepresentable_unit :
    toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≫
      (constantSheafMapOfLocallyRepresentable F A g hlocal).hom =
      constantPresheafMapOfLocallyRepresentable F A g hlocal :=
  toSheafify_sheafifyLift _ _ _

variable {F}

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- Exact stalk normalization of the assembled sheaf map. -/
@[reassoc]
theorem constantSheafMapOfLocallyRepresentable_stalk (x : X) :
    (constantSheafStalkIso A x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (constantSheafMapOfLocallyRepresentable F A g hlocal).hom = g x := by
  simp only [constantSheafStalkIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Functor.map_comp, constantSheafMapOfLocallyRepresentable_unit]
  dsimp only [TopCat.Presheaf.Γgerm]
  erw [TopCat.Presheaf.stalkFunctor_map_germ]
  change globalMapOfLocallyRepresentable F A g hlocal ≫ F.presheaf.map (𝟙 _) ≫
    F.presheaf.Γgerm x = g x
  rw [CategoryTheory.Functor.map_id, Category.id_comp, globalMapOfLocallyRepresentable_germ]

/-- If the specified stalk maps are isomorphisms, the assembled sheaf map is an
isomorphism. This uses the actual stalk formula, not a chosen sheaf equivalence. -/
theorem constantSheafMapOfLocallyRepresentable_isIso (hg : ∀ x : X, IsIso (g x)) :
    IsIso (constantSheafMapOfLocallyRepresentable F A g hlocal) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).2
  intro x
  have hfac := constantSheafMapOfLocallyRepresentable_stalk F A g hlocal x
  have : IsIso ((constantSheafStalkIso A x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (constantSheafMapOfLocallyRepresentable F A g hlocal).hom) := by
    rw [hfac]
    exact hg x
  exact IsIso.of_isIso_comp_left (constantSheafStalkIso A x).hom _

end TopCat.Sheaf
