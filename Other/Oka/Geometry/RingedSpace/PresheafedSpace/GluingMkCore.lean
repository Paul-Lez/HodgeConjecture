/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.PresheafedSpace.Gluing
public import Other.Oka.Geometry.RingedSpace.OpenImmersion

/-!
# Glue data of locally ringed spaces from open subspaces

The analogue of `TopCat.GlueData.MkCore` for locally ringed spaces: the overlaps are open
subspaces `(U i)|(V i j)` of the members rather than objects with open immersions into them, and
the triple overlaps are the open subspaces `(U i)|(V i j ⊓ V i k)` rather than pullbacks.
`AlgebraicGeometry.LocallyRingedSpace.GlueData.MkCore.toGlueData` produces an
`AlgebraicGeometry.LocallyRingedSpace.GlueData` whose `V`, `f` and `t` are the given ones on the
nose.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

/-- The data of a gluing of locally ringed spaces along open subspaces. -/
structure GlueData.MkCore where
  /-- The index type. -/
  J : Type u
  /-- The spaces to be glued. -/
  U : J → LocallyRingedSpace.{u}
  /-- `V i j` is the open subset of `U i` glued to `U j`. -/
  V : ∀ i, J → Opens (U i)
  /-- The transition morphisms. -/
  t : ∀ i j, (U i).restrict (V i j).isOpenEmbedding ⟶ (U j).restrict (V j i).isOpenEmbedding
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, t i i = 𝟙 _
  /-- The transition morphisms on triple overlaps. -/
  t' : ∀ i j k, (U i).restrict (V i j ⊓ V i k).isOpenEmbedding ⟶
    (U j).restrict (V j k ⊓ V j i).isOpenEmbedding
  t'_fac : ∀ i j k, t' i j k ≫ (U j).restrictLE inf_le_right =
    (U i).restrictLE inf_le_left ≫ t i j
  t_inv : ∀ i j, t i j ≫ t j i = 𝟙 _
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

namespace GlueData.MkCore

variable (h : GlueData.MkCore.{u})

/-- The glue data of a `GlueData.MkCore`: the overlaps are the open subspaces `(U i)|(V i j)` with
their inclusions, and `t'` is `h.t'` conjugated by
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback`. -/
noncomputable def toGlueData : LocallyRingedSpace.GlueData.{u} where
  J := h.J
  U := h.U
  V ij := (h.U ij.1).restrict (h.V ij.1 ij.2).isOpenEmbedding
  f i j := (h.U i).ofRestrict (h.V i j).isOpenEmbedding
  f_id i := by
    haveI : Epi ((h.U i).ofRestrict (h.V i i).isOpenEmbedding).base := by
      rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ, range_ofRestrict, h.V_id]
      rfl
    exact IsOpenImmersion.to_iso _
  f_open i j := inferInstance
  t := h.t
  t_id := h.t_id
  t' i j k := ((h.U i).restrictInfIsoPullback (h.V i j) (h.V i k)).inv ≫ h.t' i j k ≫
    ((h.U j).restrictInfIsoPullback (h.V j k) (h.V j i)).hom
  t_fac i j k := by
    rw [← Iso.inv_hom_id_assoc ((h.U i).restrictInfIsoPullback (h.V i j) (h.V i k))
      (pullback.fst _ _ ≫ h.t i j)]
    simp only [Category.assoc, restrictInfIsoPullback_hom_snd, h.t'_fac,
      restrictInfIsoPullback_hom_fst_assoc]
  cocycle i j k := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% h.cocycle]
    simp

@[simp] lemma toGlueData_J : h.toGlueData.J = h.J := rfl
lemma toGlueData_U (i : h.J) : h.toGlueData.U i = h.U i := rfl
lemma toGlueData_V (i j : h.J) :
    h.toGlueData.V (i, j) = (h.U i).restrict (h.V i j).isOpenEmbedding := rfl
lemma toGlueData_f (i j : h.J) :
    h.toGlueData.f i j = (h.U i).ofRestrict (h.V i j).isOpenEmbedding := rfl
lemma toGlueData_t (i j : h.J) : h.toGlueData.t i j = h.t i j := rfl

/-- **Two points of the members are identified in the gluing iff the transition map sends one to
the other.** -/
theorem ι_eq_iff (i j : h.J) (x : h.U i) (y : h.U j) :
    (h.toGlueData.ι i).base x = (h.toGlueData.ι j).base y ↔
      ∃ hx : x ∈ h.V i j, ((h.t i j).base ⟨x, hx⟩).1 = y := by
  rw [GlueData.ι_eq_iff]
  constructor
  · rintro ⟨⟨z, hz'⟩, hz, hy⟩
    change z = x at hz
    change ((h.t i j).base ⟨z, hz'⟩).1 = y at hy
    refine ⟨hz ▸ hz', ?_⟩
    rw [← hy]
    congr 3
    exact hz.symm
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

/-- **The preimage in `U i` of the image of `U j` is `V i j`.** -/
theorem preimage_range (i j : h.J) :
    (h.toGlueData.ι i).base ⁻¹' Set.range (h.toGlueData.ι j).base =
      (h.V i j : Set (h.U i)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ((h.ι_eq_iff i j x y).mp hy.symm).1
  · intro hx
    exact ⟨_, ((h.ι_eq_iff i j x _).mpr ⟨hx, rfl⟩).symm⟩

/-- **Every point of the gluing comes from some member.** -/
theorem ι_jointly_surjective (x : h.toGlueData.glued) :
    ∃ (i : h.J) (y : h.U i), (h.toGlueData.ι i).base y = x :=
  GlueData.ι_jointly_surjective _ x

end GlueData.MkCore

end AlgebraicGeometry.LocallyRingedSpace

end
