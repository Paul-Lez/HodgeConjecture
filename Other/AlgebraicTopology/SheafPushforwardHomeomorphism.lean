/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sheaves.Functors

/-!
# Direct image along a homeomorphism

A homeomorphism induces an equivalence of presheaf categories by precomposition on
open sets.  This file restricts that equivalence to sheaves.  In particular, direct
image along an isomorphism of topological spaces preserves injective sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace TopCat.Sheaf

variable (A : Type u) [Category.{v} A]

/-- Direct image along an isomorphism of topological spaces is an equivalence of
sheaf categories. -/
def pushforwardEquivalenceOfIso {X Y : TopCat.{w}} (H : X ≅ Y) :
    Sheaf A X ≌ Sheaf A Y where
  functor := pushforward A H.hom
  inverse := pushforward A H.inv
  unitIso := NatIso.ofComponents
    (fun F =>
      let e := (TopCat.Presheaf.presheafEquivOfIso A H).unitIso.app F.1
      { hom := ⟨e.hom⟩
        inv := ⟨e.inv⟩
        hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
        inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id })
    (fun {F G} f => by
      apply ObjectProperty.hom_ext
      exact (TopCat.Presheaf.presheafEquivOfIso A H).unitIso.hom.naturality f.1)
  counitIso := NatIso.ofComponents
    (fun F =>
      let e := (TopCat.Presheaf.presheafEquivOfIso A H).counitIso.app F.1
      { hom := ⟨e.hom⟩
        inv := ⟨e.inv⟩
        hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
        inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id })
    (fun {F G} f => by
      apply ObjectProperty.hom_ext
      exact (TopCat.Presheaf.presheafEquivOfIso A H).counitIso.hom.naturality f.1)
  functor_unitIso_comp F := by
    apply ObjectProperty.hom_ext
    exact (TopCat.Presheaf.presheafEquivOfIso A H).functor_unitIso_comp F.1

/-- The direct-image functor along a supplied topological isomorphism is an
equivalence.  This theorem is intended for installing a local instance when the
isomorphism is known explicitly. -/
theorem pushforward_isEquivalence_of_iso {X Y : TopCat.{w}} (H : X ≅ Y) :
    (pushforward A H.hom).IsEquivalence :=
  (pushforwardEquivalenceOfIso A H).isEquivalence_functor

end TopCat.Sheaf
