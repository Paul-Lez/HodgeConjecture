/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.FlasqueSections

/-!
# Constructions used only in proofs

These were built to prove the results about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.FlasqueSections`.
The statement of the conjecture never inspects them: every path from the statement to one
of them runs through a proof, so proof irrelevance makes their bodies immaterial.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U V : Opens X) (F : Sheaf AddCommGrpCat.{u} X)

/-- Pairwise sheaf gluing extends a supported section by zero across `U`, as an actual
additive morphism from the defining kernel. -/
def supportedOutsideGlueZero :
    ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ⟶ F.obj.obj (op (V ⊔ U)) :=
  F.interUnionPullbackConeLift V U
    (PullbackCone.mk
      (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V))
      (0 : ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ⟶ F.obj.obj (op U))
      (by rw [supportedOutsideInclusion_restrict_intersection, zero_comp]))

/-- Gluing with zero preserves the given section on its original open. -/
@[reassoc (attr := simp)]
theorem supportedOutsideGlueZero_restrict_left :
    supportedOutsideGlueZero X U V F ≫
      F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op =
        ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) :=
  F.interUnionPullbackConeLift_left V U _

/-- The same glued section is exactly zero on the excluded open. -/
@[reassoc (attr := simp)]
theorem supportedOutsideGlueZero_restrict_right :
    supportedOutsideGlueZero X U V F ≫
      F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op = 0 :=
  F.interUnionPullbackConeLift_right V U _

variable {V} {W : Opens X}

/-- Every supported section extends along an open inclusion when the original sheaf
is flasque. The extension is produced by gluing with zero before extending. -/
theorem sheafSectionsSupportedOutside_restriction_surjective [F.IsFlasque]
    (hVW : V ≤ W) :
    Function.Surjective (((sheafSectionsSupportedOutside X U).obj F).obj.map
      (homOfLE hVW).op) := by
  intro a
  let G := (sheafSectionsSupportedOutside X U).obj F
  let ι := (sheafSectionsSupportedOutsideInclusion X U).app F
  have hsup : V ⊔ U ≤ W ⊔ U := sup_le_sup_right hVW U
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE hsup).op)).mp inferInstance
      (supportedOutsideGlueZero X U V F a)
  have htU : F.obj.map (homOfLE (le_sup_right : U ≤ W ⊔ U)).op t = 0 := by
    calc
      _ = F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op
          (F.obj.map (homOfLE hsup).op t) := by
        rw [← Functor.map_comp_apply]
        rfl
      _ = F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op
          (supportedOutsideGlueZero X U V F a) := by rw [ht]
      _ = 0 := ConcreteCategory.congr_hom (supportedOutsideGlueZero_restrict_right X U V F) a
  let b := F.obj.map (homOfLE (le_sup_left : W ≤ W ⊔ U)).op t
  have hb : F.obj.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op b = 0 := by
    calc
      _ = F.obj.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op
          (F.obj.map (homOfLE (le_sup_right : U ≤ W ⊔ U)).op t) := by
        dsimp [b]
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        rfl
      _ = 0 := by rw [htU, map_zero]
  obtain ⟨c, hc⟩ := exists_supportedOutsideSection_of_restrict_eq_zero X U W F b hb
  have hι : Function.Injective (ι.hom.app (op V)) := by
    apply (AddCommGrpCat.mono_iff_injective _).mp
    change Mono (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V))
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X U V F]
    infer_instance
  refine ⟨c, hι ?_⟩
  calc
    ι.hom.app (op V) (G.obj.map (homOfLE hVW).op c) =
        F.obj.map (homOfLE hVW).op (ι.hom.app (op W) c) :=
      ConcreteCategory.congr_hom (ι.hom.naturality (homOfLE hVW).op) c
    _ = F.obj.map (homOfLE hVW).op b := by rw [hc]
    _ = F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op
        (F.obj.map (homOfLE hsup).op t) := by
      dsimp [b]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      rfl
    _ = F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op
        (supportedOutsideGlueZero X U V F a) := by rw [ht]
    _ = ι.hom.app (op V) a :=
      ConcreteCategory.congr_hom (supportedOutsideGlueZero_restrict_left X U V F) a

/-- The actual sheaf-valued supported-sections functor preserves flasque sheaves. -/
instance sheafSectionsSupportedOutside_isFlasque [F.IsFlasque] :
    ((sheafSectionsSupportedOutside X U).obj F).IsFlasque where
  epi {V W} i := by
    exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (sheafSectionsSupportedOutside_restriction_surjective X U F (leOfHom i.unop))

/-- Equivalently, sections supported in any actual closed subset preserve flasqueness. -/
instance sheafSectionsWithClosedSupport_isFlasque (Z : Closeds X) [F.IsFlasque] :
    ((sheafSectionsWithClosedSupport X Z).obj F).IsFlasque :=
  sheafSectionsSupportedOutside_isFlasque X Z.compl F

end TopCat.Sheaf
