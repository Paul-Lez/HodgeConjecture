/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Colimits of sheaves of modules

The functor from sheaves of modules to their underlying sheaves of abelian groups preserves
colimits. In particular, it preserves epimorphisms.
-/

@[expose] public noncomputable section

universe w' w v v' u u'

open CategoryTheory Limits

namespace SheafOfModules

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The underlying-sheaf functor preserves colimits of any shape available in
`AddCommGrpCat`. -/
instance preservesColimitsOfShape_toSheaf (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (toSheaf.{v} R) where
  preservesColimit {F} := by
    have hL : PreservesColimitsOfShape K (PresheafOfModules.sheafification.{v} (𝟙 R.obj)) :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits.1
    have hLT : PreservesColimitsOfShape K
        (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R) :=
      preservesColimitsOfShape_of_natIso (PresheafOfModules.sheafificationCompToSheaf _).symm
    have : PreservesColimit ((F ⋙ forget R) ⋙
        PresheafOfModules.sheafification.{v} (𝟙 R.obj)) (toSheaf.{v} R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves _ (colimit.isColimit (F ⋙ forget R)))
        (isColimitOfPreserves
          (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R)
          (colimit.isColimit (F ⋙ forget R)))
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification.{v} (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    exact preservesColimit_of_iso_diagram _ e.symm

/-- The underlying-sheaf functor preserves finite colimits. -/
instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf.{v} R) where

end

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The underlying-sheaf functor preserves epimorphisms. -/
instance preservesEpimorphisms_toSheaf : (toSheaf.{v} R).PreservesEpimorphisms where
  preserves {_ _} f hf :=
    have : Epi f := hf
    Preadditive.epi_of_isZero_cokernel _
      (IsZero.of_iso (Functor.map_isZero _ (isZero_cokernel_of_epi f))
        (PreservesCokernel.iso (toSheaf.{v} R) f).symm)

end


end SheafOfModules
