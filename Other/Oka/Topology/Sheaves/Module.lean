/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Topology.Sheaves.Module
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Equivalence

/-! # Coherence and restriction to an open subspace -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Limits

universe u

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{u})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

lemma sheafOfModulesEquivOver_H₂ :
    (U.overPullbackSheafEquivOver.app R).inv.hom ≫
      U.overEquivalence.symm.functor.op.whiskerLeft
        (U.sheafRestrictSheafEquivOver.app R).inv.hom ≫
        Functor.whiskerRight (NatTrans.op U.overEquivalence.symm.unit)
          (U.sheafRestrict.obj R).obj = 𝟙 _ := by
  ext : 2
  simp [overPullbackSheafEquivOver, sheafRestrictSheafEquivOver, eqToHom_map, overEquivalence,
    IsOpenMap.functor]


theorem isCoherent_sheafOfModulesEquivOver_functor_obj_iff (M : SheafOfModules.{u} (R.over U)) :
    ((U.sheafOfModulesEquivOver R).functor.obj M).IsCoherent ↔ M.IsCoherent :=
  ⟨fun h => SheafOfModules.isCoherent_of_isCoherent_pushforward_of_equivalence
      U.overEquivalence.symm _ _ rfl (sheafOfModulesEquivOver_H₂ U R)
      (U.sheafOfModulesEquivOverUnit R) M h,
    fun _ => SheafOfModules.isCoherent_pushforward_of_equivalence
      U.overEquivalence.symm _ _ rfl (sheafOfModulesEquivOver_H₂ U R)
      (U.sheafOfModulesEquivOverUnit R) M⟩

end TopologicalSpace.Opens
