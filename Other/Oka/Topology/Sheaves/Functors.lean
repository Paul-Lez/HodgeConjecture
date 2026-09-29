/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.Sheaves.Functors

/-!
# Pushforward along an embedding is fully faithful

For a continuous map `i : X ⟶ Y` which is **inducing** ; the topology on `X` is the one pulled
back from `Y`, so in particular for any embedding, open or closed ; pushing forward loses no
information about morphisms:

`(F ⟶ G) ≃ (i_* F ⟶ i_* G)`

for presheaves `F G` on `X`, and the same for sheaves. Mathlib has the pushforward functor
(`Mathlib/Topology/Sheaves/Functors.lean`, the file this one extends) and the fact that it
preserves stalks at points of the image
(`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`), but not this; and the
stalk statement does not imply it, since a morphism of sheaves is not determined by its stalk
maps.

## Why it is true, and what the proof needs

Faithfulness is immediate: for `i` inducing, every open `V ⊆ X` is `i⁻¹ U` for some open
`U ⊆ Y`, and `(i_* F)(U) = F(i⁻¹ U) = F(V)`, so two morphisms that agree after pushing forward
agree on every open.

Fullness is where the work is. Given `τ : i_* F ⟶ i_* G` one wants to *define* a component at
each `V`, and the naive route ; choose `U` with `i⁻¹ U = V` and take `τ_U` ; has to be shown
independent of the choice, and produces a component whose type only matches after transporting
along `i⁻¹ U = V`. Both problems disappear by making the choice canonical:
`TopCat.Presheaf.coimageOpens i V` is the **largest** open of `Y` whose preimage is contained in
`V`, i.e. the right adjoint of `Opens.map i`. It is monotone and satisfies

* `TopCat.Presheaf.opens_map_coimageOpens_le`: `i⁻¹ (coimageOpens i V) ≤ V`, always;
* `TopCat.Presheaf.le_opens_map_coimageOpens`: `V ≤ i⁻¹ (coimageOpens i V)` when `i` is
  inducing;
* `TopCat.Presheaf.le_coimageOpens`: `U ≤ coimageOpens i (i⁻¹ U)`, always.

The component at `V` is then `τ` at `coimageOpens i V`, conjugated by the *restriction maps*
belonging to the first two inequalities. No `eqToHom` and no transport appear anywhere: the two
inequalities are used as morphisms of the poset `Opens X`, and everything reduces to the fact
that parallel morphisms in a poset are equal. The third inequality is what makes the
construction a section of the pushforward.

No sheaf condition is used, so the presheaf statement is the primitive one and the sheaf
statement is read off from it.

## Main definitions

- `TopCat.Presheaf.coimageOpens`: the right adjoint of `Opens.map i`.
- `TopCat.Presheaf.pushforwardFullyFaithful` and `TopCat.Presheaf.pushforwardHomEquiv`, whose
  forward map is the pushforward itself (`TopCat.Presheaf.pushforwardHomEquiv_apply`).
- `TopCat.Sheaf.pushforwardFullyFaithful` and `TopCat.Sheaf.pushforwardHomEquiv`.

## Main results

- `TopCat.Presheaf.pushforward_faithful` and `TopCat.Presheaf.pushforward_full`.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite Topology
open scoped AlgebraicGeometry

universe w v u

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X Y : TopCat.{w}} (i : X ⟶ Y)

section CoimageOpens

/-- The largest open set of `Y` whose preimage is contained in a given open set of `X`: the
right adjoint of `Opens.map i`. -/
def coimageOpens (V : Opens X) : Opens Y :=
  sSup {U : Opens Y | (Opens.map i).obj U ≤ V}

variable {i}

/-- **For an inducing map, every open set of the source is the preimage of an open set of the
target.** This is the whole input from topology. -/
lemma exists_opens_map_obj_eq (hi : IsInducing i) (V : Opens X) :
    ∃ U : Opens Y, (Opens.map i).obj U = V := by
  obtain ⟨t, ht, hpre⟩ := hi.isOpen_iff.1 V.isOpen
  exact ⟨⟨t, ht⟩, Opens.ext hpre⟩

/-- The unit of the adjunction `Opens.map i ⊣ coimageOpens i`. -/
lemma le_coimageOpens (U : Opens Y) : U ≤ coimageOpens i ((Opens.map i).obj U) :=
  le_sSup (Set.mem_setOf.2 (le_refl _))

/-- The counit of the adjunction `Opens.map i ⊣ coimageOpens i`. -/
lemma opens_map_coimageOpens_le (V : Opens X) : (Opens.map i).obj (coimageOpens i V) ≤ V := by
  rintro x hx
  obtain ⟨-, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, hxU⟩ := hx
  exact hU hxU

lemma coimageOpens_mono : Monotone (coimageOpens i) := fun _ _ h ↦
  sSup_le_sSup fun _ (hU : _ ≤ _) ↦ Set.mem_setOf.2 (hU.trans h)

/-- **For an inducing map the counit is an isomorphism**, i.e. `i⁻¹ (coimageOpens i V) = V`; only
this inequality is used, the other being `opens_map_coimageOpens_le`. -/
lemma le_opens_map_coimageOpens (hi : IsInducing i) (V : Opens X) :
    V ≤ (Opens.map i).obj (coimageOpens i V) := by
  obtain ⟨U, hU⟩ := exists_opens_map_obj_eq hi V
  calc V = (Opens.map i).obj U := hU.symm
    _ ≤ (Opens.map i).obj (coimageOpens i V) :=
        (Opens.map i).monotone (le_sSup (Set.mem_setOf.2 (le_of_eq hU)))

end CoimageOpens

section FullyFaithful

variable {i} {F G : X.Presheaf C}

/-- Given `τ : i_* F ⟶ i_* G` for an inducing map `i`, the morphism `F ⟶ G` it comes from: at
`V` it is `τ` at `coimageOpens i V`, conjugated by the restriction maps of
`opens_map_coimageOpens_le` and `le_opens_map_coimageOpens`. -/
def pushforwardPreimage (hi : IsInducing i) (τ : i _* F ⟶ i _* G) : F ⟶ G where
  app W := F.map (homOfLE (opens_map_coimageOpens_le W.unop)).op ≫
      τ.app (op (coimageOpens i W.unop)) ≫
      G.map (homOfLE (le_opens_map_coimageOpens hi W.unop)).op
  naturality W W' k := by
    have hle : W'.unop ≤ W.unop := k.unop.le
    have hτ := τ.naturality (homOfLE (coimageOpens_mono (i := i) hle)).op
    have hF : F.map k ≫ F.map (homOfLE (opens_map_coimageOpens_le W'.unop)).op =
        F.map (homOfLE (opens_map_coimageOpens_le W.unop)).op ≫
          F.map ((Opens.map i).map (homOfLE (coimageOpens_mono (i := i) hle))).op := by
      rw [← F.map_comp, ← F.map_comp]
      exact congrArg F.map (Subsingleton.elim _ _)
    have hG : G.map (homOfLE (le_opens_map_coimageOpens hi W.unop)).op ≫ G.map k =
        G.map ((Opens.map i).map (homOfLE (coimageOpens_mono (i := i) hle))).op ≫
          G.map (homOfLE (le_opens_map_coimageOpens hi W'.unop)).op := by
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (Subsingleton.elim _ _)
    have hτ' : F.map ((Opens.map i).map (homOfLE (coimageOpens_mono (i := i) hle))).op ≫
          τ.app (op (coimageOpens i W'.unop)) =
        τ.app (op (coimageOpens i W.unop)) ≫
          G.map ((Opens.map i).map (homOfLE (coimageOpens_mono (i := i) hle))).op := hτ
    rw [← Category.assoc, hF]
    simp only [Category.assoc]
    -- `rw` cannot use `hG` here: the object between `τ.app _` and `G.map _` is spelled through
    -- `(pushforward C i).obj G`, so the pattern does not match syntactically even though it
    -- matches up to unfolding. `congrArg` is checked up to definitional equality and goes
    -- straight through.
    have step : τ.app (op (coimageOpens i W.unop)) ≫
          G.map (homOfLE (le_opens_map_coimageOpens hi W.unop)).op ≫ G.map k =
        F.map ((Opens.map i).map (homOfLE (coimageOpens_mono (i := i) hle))).op ≫
          τ.app (op (coimageOpens i W'.unop)) ≫
          G.map (homOfLE (le_opens_map_coimageOpens hi W'.unop)).op :=
      (congrArg (fun z ↦ τ.app (op (coimageOpens i W.unop)) ≫ z) hG).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ G.map (homOfLE (le_opens_map_coimageOpens hi W'.unop)).op)
              hτ'.symm).trans (Category.assoc _ _ _)))
    exact congrArg (fun z ↦ F.map (homOfLE (opens_map_coimageOpens_le W.unop)).op ≫ z) step.symm

/-- `pushforwardPreimage` is a section of the pushforward: pushing it forward returns `τ`. -/
lemma pushforward_map_pushforwardPreimage (hi : IsInducing i) (τ : i _* F ⟶ i _* G) :
    (pushforward C i).map (pushforwardPreimage hi τ) = τ := by
  ext U
  have hτ := τ.naturality (homOfLE (le_coimageOpens (i := i) U)).op
  have hGeq : G.map (homOfLE (le_opens_map_coimageOpens hi ((Opens.map i).obj U))).op =
      ((pushforward C i).obj G).map (homOfLE (le_coimageOpens (i := i) U)).op :=
    congrArg G.map (Subsingleton.elim _ _)
  have hFid : F.map (homOfLE (opens_map_coimageOpens_le ((Opens.map i).obj U))).op ≫
      ((pushforward C i).obj F).map (homOfLE (le_coimageOpens (i := i) U)).op = 𝟙 _ :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (Subsingleton.elim _ (𝟙 _))).trans (F.map_id _))
  refine (congrArg (fun z ↦ F.map (homOfLE
    (opens_map_coimageOpens_le ((Opens.map i).obj U))).op ≫
      τ.app (op (coimageOpens i ((Opens.map i).obj U))) ≫ z) hGeq).trans ?_
  refine (congrArg (fun z ↦ F.map (homOfLE
    (opens_map_coimageOpens_le ((Opens.map i).obj U))).op ≫ z) hτ.symm).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ τ.app (op U)) hFid).trans (Category.id_comp _))

variable (i) in
/-- **The pushforward of presheaves along an inducing map is faithful**: every open set of the
source is the preimage of one of the target, so no component is forgotten. -/
lemma pushforward_faithful (hi : IsInducing i) : (pushforward C i).Faithful where
  map_injective {F G _ _} h := by
    ext W
    obtain ⟨U, rfl⟩ := exists_opens_map_obj_eq hi W
    exact congrArg (fun (t : i _* F ⟶ i _* G) ↦ t.app (op U)) h

variable (i) in
/-- **The pushforward of presheaves along an inducing map is fully faithful.**

No sheaf condition is used; see `TopCat.Sheaf.pushforwardFullyFaithful` for the sheaf form. -/
def pushforwardFullyFaithful (hi : IsInducing i) : (pushforward C i).FullyFaithful where
  preimage τ := pushforwardPreimage hi τ
  map_preimage τ := pushforward_map_pushforwardPreimage hi τ
  preimage_map _ := by
    haveI := pushforward_faithful (C := C) i hi
    exact (pushforward C i).map_injective (pushforward_map_pushforwardPreimage hi _)

variable (i) in
lemma pushforward_full (hi : IsInducing i) : (pushforward C i).Full :=
  (pushforwardFullyFaithful i hi).full

variable (i) in
/-- Morphisms of presheaves on `X` are the same as morphisms of their pushforwards along an
inducing map. -/
def pushforwardHomEquiv (hi : IsInducing i) (F G : X.Presheaf C) :
    (F ⟶ G) ≃ (i _* F ⟶ i _* G) :=
  (pushforwardFullyFaithful i hi).homEquiv

/-- The equivalence of `TopCat.Presheaf.pushforwardHomEquiv` is the pushforward itself, and not
some other bijection: this is what makes the statement say what it is meant to say. -/
@[simp]
lemma pushforwardHomEquiv_apply (hi : IsInducing i) (F G : X.Presheaf C) (σ : F ⟶ G) :
    pushforwardHomEquiv i hi F G σ = (pushforward C i).map σ :=
  rfl

@[simp]
lemma pushforwardHomEquiv_symm_apply (hi : IsInducing i) (F G : X.Presheaf C)
    (τ : i _* F ⟶ i _* G) :
    (pushforwardHomEquiv i hi F G).symm τ = pushforwardPreimage hi τ :=
  rfl

end FullyFaithful

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C] {X Y : TopCat.{w}} (i : X ⟶ Y)

/-- **The pushforward of sheaves along an inducing map is fully faithful.** A morphism of
sheaves is a morphism of the underlying presheaves, so this is
`TopCat.Presheaf.pushforwardFullyFaithful` with the bookkeeping. -/
noncomputable def pushforwardFullyFaithful (hi : IsInducing i) :
    (pushforward C i).FullyFaithful where
  preimage α := ⟨Presheaf.pushforwardPreimage hi α.1⟩
  map_preimage α :=
    CategoryTheory.Sheaf.hom_ext (Presheaf.pushforward_map_pushforwardPreimage hi α.1)
  preimage_map _ := by
    haveI := Presheaf.pushforward_faithful (C := C) i hi
    exact CategoryTheory.Sheaf.hom_ext ((Presheaf.pushforward C i).map_injective
      (Presheaf.pushforward_map_pushforwardPreimage hi _))

/-- Morphisms of sheaves on `X` are the same as morphisms of their pushforwards along an
inducing map. -/
noncomputable def pushforwardHomEquiv (hi : IsInducing i) (F G : X.Sheaf C) :
    (F ⟶ G) ≃ ((pushforward C i).obj F ⟶ (pushforward C i).obj G) :=
  (pushforwardFullyFaithful i hi).homEquiv

/-- The equivalence of `TopCat.Sheaf.pushforwardHomEquiv` is the pushforward itself. -/
@[simp]
lemma pushforwardHomEquiv_apply (hi : IsInducing i) (F G : X.Sheaf C) (σ : F ⟶ G) :
    pushforwardHomEquiv i hi F G σ = (pushforward C i).map σ :=
  rfl

end TopCat.Sheaf

end
