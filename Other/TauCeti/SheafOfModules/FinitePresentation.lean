/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Finite presentation of locally free sheaves

Adapted from `TauCeti/Algebra/Category/ModuleCat/Sheaf/FinitePresentation.lean` at Tau Ceti
commit `6b10e2573adea2abab44b08630b9c69e73048090`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- Locally free data with finite local bases exhibits a finitely presented sheaf. -/
theorem LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation
    {q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M} (hfree : q.IsLocallyFreeData)
    (hfinite : q.IsFiniteType) :
    M.IsFinitePresentation := by
  let : q.IsLocallyFreeData := hfree
  refine ⟨q.quasiCoherentData, ⟨fun i ↦ ?_⟩⟩
  refine
    { isFiniteType_generators := ?_
      isFiniteType_relations := ?_ }
  · change (q.generators i).IsFiniteType
    exact hfinite.isFiniteType i
  · refine ⟨?_⟩
    change Finite (ULift Empty)
    infer_instance

end SheafOfModules

end

end TauCeti
