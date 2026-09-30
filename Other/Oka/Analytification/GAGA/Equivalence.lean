/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveGAGA3
public import Other.Oka.Analytification.GAGA.SheafAnalytificationIsCoherent

/-!
# GAGA as an equivalence of categories

For a scheme `X` locally of finite type over `ℂ`, analytification of sheaves of modules sends
coherent sheaves to coherent sheaves (`ComplexAnalytic.isCoherent_analytificationModules`), so it
restricts to a functor `ComplexAnalytic.coherentAnalytification X` from the full subcategory of
coherent sheaves on `X` to the full subcategory of coherent sheaves on `X^an`.

For `X` projective, this functor is an equivalence of categories
(`ComplexAnalytic.isEquivalence_coherentAnalytification`): it is fully faithful by GAGA-2
(`ComplexAnalytic.gaga₂`) and essentially surjective by GAGA-3 (`ComplexAnalytic.gaga₃`).
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace ComplexAnalytic

variable (X : SchemeLFTℂ.{u})

/-- The analytification functor `F ↦ F^an` from coherent sheaves on `X` to coherent sheaves
on `X^an`. -/
def coherentAnalytification :
    (SheafOfModules.isCoherent X.obj.left.toLocallyRingedSpace.ringSheaf).FullSubcategory ⥤
      (SheafOfModules.isCoherent
        (analytification.obj X).toLocallyRingedSpace.ringSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ analytificationModules X) fun F ↦
    haveI := F.property
    isCoherent_analytificationModules X F.obj

/-- The analytification of coherent sheaves, followed by the inclusion into all sheaves of
modules on `X^an`, is the analytification of sheaves of modules restricted to coherent ones. -/
def coherentAnalytificationCompιIso :
    coherentAnalytification X ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ analytificationModules X :=
  Iso.refl _

variable {X}

/-- **GAGA-2 as full faithfulness**: for `X` projective over `ℂ`, analytification of coherent
sheaves is fully faithful. -/
def IsProjectiveℂ.fullyFaithfulCoherentAnalytification (hX : IsProjectiveℂ X) :
    (coherentAnalytification X).FullyFaithful where
  preimage {F G} f :=
    haveI := F.property
    haveI := G.property
    ObjectProperty.homMk (((gaga₂ X hX F.obj G.obj).surjective f.hom).choose)
  map_preimage {F G} f := by
    haveI := F.property
    haveI := G.property
    ext1
    exact ((gaga₂ X hX F.obj G.obj).surjective f.hom).choose_spec
  preimage_map {F G} f := by
    haveI := F.property
    haveI := G.property
    ext1
    exact (gaga₂ X hX F.obj G.obj).injective
      ((gaga₂ X hX F.obj G.obj).surjective _).choose_spec

/-- **GAGA-3 as essential surjectivity**: for `X` projective over `ℂ`, every coherent analytic
sheaf on `X^an` is isomorphic to the analytification of a coherent sheaf on `X`. -/
theorem essSurj_coherentAnalytification (hX : IsProjectiveℂ X) :
    (coherentAnalytification X).EssSurj where
  mem_essImage M := by
    obtain ⟨F, hF, ⟨e⟩⟩ := gaga₃ X hX M.obj M.property
    exact ⟨⟨F, hF⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Serre's GAGA as an equivalence of categories**: for a projective scheme `X` over `ℂ`,
analytification `F ↦ F^an` is an equivalence between the category of coherent sheaves on `X`
and the category of coherent analytic sheaves on `X^an`. -/
theorem isEquivalence_coherentAnalytification (hX : IsProjectiveℂ X) :
    (coherentAnalytification X).IsEquivalence :=
  haveI := hX.fullyFaithfulCoherentAnalytification.full
  haveI := hX.fullyFaithfulCoherentAnalytification.faithful
  haveI := essSurj_coherentAnalytification hX
  { }

/-- **Serre's GAGA**, bundled: for a projective scheme `X` over `ℂ`, the equivalence between
coherent sheaves on `X` and coherent analytic sheaves on `X^an` given by analytification. -/
def gagaEquivalence (hX : IsProjectiveℂ X) :
    (SheafOfModules.isCoherent X.obj.left.toLocallyRingedSpace.ringSheaf).FullSubcategory ≌
      (SheafOfModules.isCoherent
        (analytification.obj X).toLocallyRingedSpace.ringSheaf).FullSubcategory :=
  haveI := isEquivalence_coherentAnalytification hX
  (coherentAnalytification X).asEquivalence

/-- The functor of `ComplexAnalytic.gagaEquivalence` is analytification. -/
@[simp]
lemma gagaEquivalence_functor (hX : IsProjectiveℂ X) :
    (gagaEquivalence hX).functor = coherentAnalytification X :=
  rfl

end ComplexAnalytic

end
