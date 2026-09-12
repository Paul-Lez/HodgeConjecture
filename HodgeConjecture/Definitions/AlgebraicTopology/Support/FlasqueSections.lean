/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsNaturality
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Supported sections preserve flasqueness

A supported section over `V` glues with zero on the excluded open `U` to a section on
`V ⊔ U`. Flasqueness extends that section to `W ⊔ U` when `V ≤ W`, and its restriction to
`W` vanishes on `W ⊓ U`, so it lies in the kernel defining supported sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U V : Opens X) (F : Sheaf AddCommGrpCat.{u} X)

/-- Restriction-pushforward on an ambient open is literally evaluation on its
intersection with the excluded open. -/
def supportedOutsideIntersectionIso :
    ((openRestrictionPushforward X U).obj F).obj.obj (op V) ≅ F.obj.obj (op (V ⊓ U)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf U V)))

/-- The preceding identification preserves the actual restriction morphism. -/
@[reassoc]
theorem toOpenRestrictionPushforward_intersection :
    (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) ≫
      (supportedOutsideIntersectionIso X U V F).hom =
        F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The literal supported-section inclusion restricts to zero on the intersection. -/
@[reassoc]
theorem supportedOutsideInclusion_restrict_intersection :
    ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) ≫
      F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op = 0 := by
  rw [← toOpenRestrictionPushforward_intersection X U V F, ← Category.assoc]
  have h := congrArg (fun f => f.hom.app (op V))
    (sheafSectionsSupportedOutsideInclusion_restriction X U F)
  change ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) ≫
    ((toOpenRestrictionPushforward X U).app F).hom.app (op V) = 0 at h
  rw [h, zero_comp]

/-- A section zero on the intersection lifts into the actual supported-section kernel.
The proof uses its canonical on-open kernel comparison, not a chosen support lift. -/
theorem exists_supportedOutsideSection_of_restrict_eq_zero
    (s : F.obj.obj (op V))
    (hs : F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s = 0) :
    ∃ t : ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V),
      ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) t = s := by
  let r := ((toOpenRestrictionPushforward X U).app F).hom.app (op V)
  have hr : r s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (supportedOutsideIntersectionIso X U V F).hom).1
    rw [map_zero]
    exact (ConcreteCategory.congr_hom
      (toOpenRestrictionPushforward_intersection X U V F) s).trans hs
  let e := sheafSectionsSupportedOutsideOnOpenIso X U V F ≪≫ AddCommGrpCat.kernelIsoKer r
  let a : r.hom.ker := ⟨s, hr⟩
  refine ⟨e.inv a, ?_⟩
  have he : e.hom ≫ AddCommGrpCat.ofHom r.hom.ker.subtype =
      ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) := by
    simp only [e, Iso.trans_hom, Category.assoc,
      AddCommGrpCat.kernelIsoKer_hom_comp_subtype]
    exact sheafSectionsSupportedOutsideOnOpenIso_hom_ι X U V F
  rw [← he]
  change (AddCommGrpCat.ofHom r.hom.ker.subtype) (e.hom (e.inv a)) = s
  have hai : e.hom (e.inv a) = a := ConcreteCategory.congr_hom e.inv_hom_id a
  rw [hai]
  rfl

variable {V} {W : Opens X}

end TopCat.Sheaf
