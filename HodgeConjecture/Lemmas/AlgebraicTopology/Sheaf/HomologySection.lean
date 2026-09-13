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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.ChainStalk

/-!
# Sections of the homology sheaf from actual relative homology

Exact sheafification sends presheaf homology to the actual homology sheaf. The unit
therefore sends a relative singular homology class on an open support to a section of
the homology sheaf. The germ comparison records the actual restriction to local relative
homology, which is essential for preserving normalized fundamental classes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomologicalComplex Opposite

universe u

namespace CategoryTheory.ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]

end CategoryTheory.ShortComplex

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The stalk functor with its domain displayed as a functor category, to align the
canonical additive structures used in functor-category homology comparisons. -/
abbrev additivePresheafStalkFunctor (x : X) :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance additivePresheafStalkFunctor_additive (x : X) :
    (additivePresheafStalkFunctor X x).Additive where
  map_add := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_add

/-- The exact sheaf stalk functor, with the categorical sheaf domain displayed. -/
abbrev additiveSheafStalkFunctor (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance additiveSheafStalkFunctor_additive (x : X) :
    (additiveSheafStalkFunctor X x).Additive where
  map_add := (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_add

instance additiveSheafStalkFunctor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (additiveSheafStalkFunctor X x) := by
  change PreservesFiniteColimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  infer_instance

instance additiveSheafStalkFunctor_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (additiveSheafStalkFunctor X x) := by
  change PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Sheafification leaves stalks unchanged, naturally in the additive presheaf. -/
def additivePresheafStalkSheafificationIso (x : X) :
    additivePresheafStalkFunctor X x ≅
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        additiveSheafStalkFunctor X x :=
  NatIso.ofComponents (fun P ↦ by
    letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
    exact asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))) (by
    intro P Q f
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (toSheafify _ Q) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (toSheafify _ P) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (sheafifyMap _ f)
    simpa only [Functor.map_comp] using
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).congr_map
        (toSheafify_naturality (Opens.grothendieckTopology X) f))

instance additivePresheafStalkFunctor_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (additivePresheafStalkFunctor X x) :=
  preservesFiniteLimits_of_natIso (additivePresheafStalkSheafificationIso X x).symm

instance additivePresheafStalkFunctor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (additivePresheafStalkFunctor X x) :=
  inferInstanceAs (PreservesFiniteColimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))

end AlgebraicTopology.Singular
