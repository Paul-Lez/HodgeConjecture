import Other.AlgebraicTopology.ClosedEmbeddingSheafExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u v

namespace TopCat.Sheaf

variable (A : Type u) [Category.{v} A]

noncomputable def equivOfIso {X Y : TopCat.{v}} (H : X ≅ Y) :
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

instance {X Y : TopCat.{v}} (H : X ≅ Y) :
    (pushforward A H.hom).IsEquivalence :=
  (equivOfIso A H).isEquivalence_functor

end TopCat.Sheaf
