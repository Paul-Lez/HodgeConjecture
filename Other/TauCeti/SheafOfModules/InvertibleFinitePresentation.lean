/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Other.TauCeti.SheafOfModules.FinitePresentation
public import Other.TauCeti.SheafOfModules.Invertible

/-!
# Finite presentation of invertible sheaves

Adapted from
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/FinitePresentation.lean` at Tau Ceti commit
`6b10e2573adea2abab44b08630b9c69e73048090`.
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

/-- An invertible sheaf of modules is finitely presented. -/
instance IsInvertible.isFinitePresentation [hM : IsInvertible M] :
    M.IsFinitePresentation := by
  obtain ⟨q, hq⟩ := hM.exists_isInvertible
  apply LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation hq.isLocallyFreeData
  exact ⟨fun i ↦ by
    let : Subsingleton (q.generators i).I := hq.basisSubsingleton i
    exact ⟨Finite.of_subsingleton⟩⟩

end SheafOfModules

end

end TauCeti
