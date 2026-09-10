/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Free sheaves on one generator

This file is adapted from `TauCeti/Algebra/Category/ModuleCat/Sheaf/Free.lean` at
Tau Ceti commit `b8d215394069a6c5713292fadcfa49746702a0eb`.
See `Other/TauCeti/README.md` for source and compatibility details.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf on one generator is canonically isomorphic to the tensor unit. -/
def freePUnitIsoUnit (S : Sheaf J RingCat.{u}) :
    _root_.SheafOfModules.free.{u, v₁, u₁} (R := S) PUnit.{u + 1} ≅
      _root_.SheafOfModules.unit.{v₁, u₁, u} S :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit.{v₁, u₁, u} S)

end SheafOfModules

end


end TauCeti
