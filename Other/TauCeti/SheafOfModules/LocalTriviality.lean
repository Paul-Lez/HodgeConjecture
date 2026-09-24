/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Other.TauCeti.SheafOfModules.Invertible

/-!
# Local trivializations of invertible sheaves

This file is adapted from `TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/LocalTriviality.lean` at
Tau Ceti commit `b8d215394069a6c5713292fadcfa49746702a0eb`.
See `Other/TauCeti/README.md` for source and compatibility details.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- A local trivialization atlas for a sheaf of modules. It consists of a cover of the terminal
object and, over every member of the cover, an isomorphism from the standard free rank-one
sheaf to the restriction of `M`. -/
structure LocalTrivializations (M : SheafOfModules.{u} R) where
  /-- The indexing type of the trivializing cover. -/
  I : Type u₁
  /-- The objects of the trivializing cover. -/
  X : I → C
  /-- The chosen objects cover the terminal object. -/
  coversTop : J.CoversTop X
  /-- The isomorphism from the standard free rank-one sheaf to `M` on each member of the
  cover. -/
  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)

namespace LocalGeneratorsData.IsInvertible

/-- A rank-one free presentation on a member of a cover, standardized to an isomorphism from
the free sheaf on `PUnit`. -/
def trivializationIso {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) PUnit ≅ M.over (q.X i) := by
  letI : Nonempty (q.generators i).I := hq.basisNonempty i
  letI : Subsingleton (q.generators i).I := hq.basisSubsingleton i
  exact
    ((_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
      Equiv.punitOfNonemptyOfSubsingleton.symm.toIso).trans
      (@asIso _ _ _ _ (q.generators i).π (hq.isLocallyFreeData.isIso i))

/-- The forward map of the standardized trivialization is the relabelling of the free basis,
followed by the original local free presentation. -/
@[simp]
lemma trivializationIso_hom {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) : (hq.trivializationIso i).hom =
      (_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).map
        (@Equiv.punitOfNonemptyOfSubsingleton (q.generators i).I
          (hq.basisNonempty i) (hq.basisSubsingleton i)).symm.toIso.hom ≫
        (q.generators i).π :=
  by
    simp only [trivializationIso, Iso.trans_hom, Functor.mapIso_hom]
    -- the residual goal is `(asIso (q.generators i).π).hom = (q.generators i).π`; `asIso_hom`
    -- no longer rewrites under the composition after the bump, and `asIso` stores its `hom`
    -- field as the given morphism, so this is definitional.
    rfl

end LocalGeneratorsData.IsInvertible

namespace LocalTrivializations

/-- Transport local trivializations along an isomorphism of sheaves of modules. -/
def ofIso (t : LocalTrivializations M) (e : M ≅ N) : LocalTrivializations N where
  I := t.I
  X := t.X
  coversTop := t.coversTop
  iso i := t.iso i ≪≫ (SheafOfModules.overFunctor R (t.X i)).mapIso e

/-- Transporting local trivializations preserves the indexing type. -/
@[simp]
lemma ofIso_I (t : LocalTrivializations M) (e : M ≅ N) : (t.ofIso e).I = t.I := (rfl)

/-- Transporting local trivializations preserves the covering objects. -/
@[simp]
lemma ofIso_X (t : LocalTrivializations M) (e : M ≅ N) :
    (t.ofIso e).X = fun i ↦ t.X ((ofIso_I t e).mp i) := (rfl)

/-- The transported trivializations are obtained by composing with the restricted isomorphism. -/
@[simp]
lemma ofIso_iso (t : LocalTrivializations M) (e : M ≅ N) (i : (t.ofIso e).I) : (t.ofIso e).iso i =
      cast (by rw [ofIso_X])
        (t.iso ((ofIso_I t e).mp i) ≪≫
          (SheafOfModules.overFunctor R (t.X ((ofIso_I t e).mp i))).mapIso e) := (rfl)

/-- Local trivializations exhibit a sheaf as invertible. -/
theorem isInvertible (t : LocalTrivializations M) : IsInvertible M := by
  let q : SheafOfModules.LocalGeneratorsData.{u₁} M :=
    { I := t.I
      X := t.X
      coversTop := t.coversTop
      generators i :=
        (_root_.SheafOfModules.free.generatingSections
          (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom }
  refine ⟨q, ?_⟩
  refine
    { isLocallyFreeData :=
        { isIso := by
            -- `q` uses the atlas's cover and the standard free generators, so unfold that local
            -- witness to express its isomorphism condition directly in terms of `t`.
            change ∀ i : t.I, IsIso
              ((_root_.SheafOfModules.free.generatingSections
                (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom).π
            intro i
            rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
            simpa only [_root_.SheafOfModules.free.generatingSections_π, Category.id_comp] using
              inferInstanceAs (IsIso (t.iso i).hom) }
      basisNonempty := fun i ↦ ?_
      basisSubsingleton := fun i ↦ ?_ }
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Nonempty PUnit)
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Subsingleton PUnit)

/-- Every invertible sheaf admits local trivializations by the standard free rank-one sheaf. -/
def ofIsInvertible (M : SheafOfModules.{u} R) [hM : IsInvertible M] :
    LocalTrivializations M := by
  let q := hM.exists_isInvertible.choose
  let hq := hM.exists_isInvertible.choose_spec
  exact
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      iso i := hq.trivializationIso i }

/-- A sheaf of modules is invertible exactly when it admits a local trivialization atlas by
the standard free rank-one sheaf. -/
theorem nonempty_iff_isInvertible :
    Nonempty (LocalTrivializations M) ↔ IsInvertible M := by
  constructor
  · rintro ⟨t⟩
    exact t.isInvertible
  · intro hM
    let := hM
    exact ⟨ofIsInvertible M⟩

end LocalTrivializations

end SheafOfModules

end

end TauCeti
