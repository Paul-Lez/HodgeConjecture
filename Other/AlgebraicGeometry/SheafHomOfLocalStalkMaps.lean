/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SheafMapOfLocallyRepresentableStalks

/-!
# Assembling a morphism of sheaves from locally represented stalk maps

`Other/AlgebraicTopology/SheafMapOfLocallyRepresentableStalks.lean` glues a *global* section
out of a locally representable family of stalk elements. Here we do the same over an arbitrary
open set, and use it to assemble an actual morphism of sheaves of abelian groups out of a family
of maps on stalks which is locally represented by sections: for every section `s` of the source
over `V` and every point of `V` there must be a section of the target on a neighbourhood whose
germs are the prescribed images of the germs of `s`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {Y : TopCat.{u}} (F G : TopCat.Sheaf AddCommGrpCat.{u} Y)

/-- Over an arbitrary open set, a locally representable family of stalk elements is the family
of germs of a unique section. -/
theorem existsUnique_section_of_stalk_family (V : Opens Y)
    (g : ∀ x : Y, x ∈ V → G.presheaf.stalk x)
    (hlocal : ∀ (x : Y) (_hx : x ∈ V), ∃ (U : Opens Y) (_ : x ∈ U) (hUV : U ≤ V)
        (t : G.presheaf.obj (op U)), ∀ (y : Y) (hy : y ∈ U),
          G.presheaf.germ U y hy t = g y (hUV hy)) :
    ∃! s : G.presheaf.obj (op V), ∀ (x : Y) (hx : x ∈ V),
      G.presheaf.germ V x hx s = g x hx := by
  classical
  choose U hxU hUV t ht using hlocal
  let W : V → Opens Y := fun x => U x.1 x.2
  have hcover : V ≤ iSup W := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU x hx⟩
  have hcompat : TopCat.Presheaf.IsCompatible G.presheaf W (fun x => t x.1 x.2) := by
    intro a b
    apply TopCat.Presheaf.section_ext G
    intro z hz
    rw [G.presheaf.germ_res_apply, G.presheaf.germ_res_apply]
    exact (ht a.1 a.2 z hz.1).trans (ht b.1 b.2 z hz.2).symm
  obtain ⟨s, hs, hsuniq⟩ :=
    G.existsUnique_gluing' W V (fun x => homOfLE (hUV x.1 x.2)) hcover _ hcompat
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    have := congrArg (G.presheaf.germ (W ⟨x, hx⟩) x (hxU x hx)) (hs ⟨x, hx⟩)
    rw [G.presheaf.germ_res_apply] at this
    exact this.trans (ht x hx x (hxU x hx))
  · intro s' hs'
    apply hsuniq
    intro x
    apply TopCat.Presheaf.section_ext G
    intro z hz
    rw [G.presheaf.germ_res_apply, hs' z (hUV x.1 x.2 hz), ht x.1 x.2 z hz]

variable (φ : ∀ x : Y, F.presheaf.stalk x ⟶ G.presheaf.stalk x)
  (hrep : ∀ (V : Opens Y) (s : F.presheaf.obj (op V)) (x : Y) (_hx : x ∈ V),
    ∃ (U : Opens Y) (_ : x ∈ U) (hUV : U ≤ V) (t : G.presheaf.obj (op U)),
      ∀ (y : Y) (hy : y ∈ U),
        G.presheaf.germ U y hy t = φ y (F.presheaf.germ V y (hUV hy) s))

/-- The section of the target prescribed by the stalk maps. -/
def sectionMapOfStalkMaps (V : Opens Y) (s : F.presheaf.obj (op V)) : G.presheaf.obj (op V) :=
  (existsUnique_section_of_stalk_family G V
    (fun x hx => φ x (F.presheaf.germ V x hx s)) (hrep V s)).exists.choose

@[simp]
theorem germ_sectionMapOfStalkMaps (V : Opens Y) (s : F.presheaf.obj (op V))
    (x : Y) (hx : x ∈ V) :
    G.presheaf.germ V x hx (sectionMapOfStalkMaps F G φ hrep V s) =
      φ x (F.presheaf.germ V x hx s) :=
  (existsUnique_section_of_stalk_family G V
    (fun x hx => φ x (F.presheaf.germ V x hx s)) (hrep V s)).exists.choose_spec x hx

/-- The morphism of sheaves assembled from the given stalk maps. -/
def homOfStalkMaps : F ⟶ G :=
  ⟨{ app V := AddCommGrpCat.ofHom
        { toFun := sectionMapOfStalkMaps F G φ hrep (unop V)
          map_zero' := by
            apply TopCat.Presheaf.section_ext G
            intro x hx
            rw [germ_sectionMapOfStalkMaps, map_zero, map_zero, map_zero]
          map_add' := by
            intro a b
            apply TopCat.Presheaf.section_ext G
            intro x hx
            rw [germ_sectionMapOfStalkMaps, map_add, map_add, map_add,
              germ_sectionMapOfStalkMaps, germ_sectionMapOfStalkMaps] }
     naturality := by
       intro V W i
       apply AddCommGrpCat.hom_ext
       apply AddMonoidHom.ext
       intro s
       apply TopCat.Presheaf.section_ext G
       intro x hx
       change G.presheaf.germ (unop W) x hx
           (sectionMapOfStalkMaps F G φ hrep (unop W) (F.presheaf.map i s)) =
         G.presheaf.germ (unop W) x hx
           (G.presheaf.map i (sectionMapOfStalkMaps F G φ hrep (unop V) s))
       rw [germ_sectionMapOfStalkMaps, G.presheaf.germ_res_apply' i,
         germ_sectionMapOfStalkMaps, F.presheaf.germ_res_apply' i] }⟩

@[simp]
theorem germ_homOfStalkMaps_app (V : Opens Y) (s : F.presheaf.obj (op V)) (x : Y) (hx : x ∈ V) :
    G.presheaf.germ V x hx ((homOfStalkMaps F G φ hrep).hom.app (op V) s) =
      φ x (F.presheaf.germ V x hx s) :=
  germ_sectionMapOfStalkMaps F G φ hrep V s x hx

end TopCat.Sheaf
