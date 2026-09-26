/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Equivalence
public import Other.Oka.Analytification.GAGA.Proper.RelativeAnalyticSerre
public import Other.Oka.Analytification.GAGA.Proper.GAGA3

/-!
# GAGA for proper schemes as an equivalence of categories

For a proper scheme `X` over `ℂ`, analytification `F ↦ F^an` is an equivalence between the
category of coherent sheaves on `X` and the category of coherent analytic sheaves on `X^an`
(`ComplexAnalytic.isEquivalence_coherentAnalytification_of_isProperℂ`, bundled as
`ComplexAnalytic.gagaEquivalenceOfIsProperℂ`). Full faithfulness is GAGA-2
(`ComplexAnalytic.gaga₂_proper`), essential surjectivity is GAGA-3
(`ComplexAnalytic.gaga₃_proper`). `ComplexAnalytic.gagaFull_proper` collects the three GAGA
theorems.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace ComplexAnalytic

variable {X : SchemeLFTℂ.{u}}

/-- Analytification of coherent sheaves is fully faithful as soon as it is bijective on morphisms
between coherent sheaves. -/
def fullyFaithfulCoherentAnalytificationOfBijective
    (h : ∀ (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf),
      F.IsCoherent → G.IsCoherent →
        Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _)) :
    (coherentAnalytification X).FullyFaithful where
  preimage {F G} f := ObjectProperty.homMk
    ((h F.obj G.obj F.property G.property).surjective f.hom).choose
  map_preimage {F G} f := by
    ext1
    exact ((h F.obj G.obj F.property G.property).surjective f.hom).choose_spec
  preimage_map {F G} f := by
    ext1
    exact (h F.obj G.obj F.property G.property).injective
      ((h F.obj G.obj F.property G.property).surjective _).choose_spec

/-- Analytification of coherent sheaves is essentially surjective as soon as every coherent
analytic sheaf is the analytification of a coherent sheaf. -/
theorem essSurj_coherentAnalytification_of_exists
    (h : ∀ (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf),
      M.IsCoherent → ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
        F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M)) :
    (coherentAnalytification X).EssSurj where
  mem_essImage M := by
    obtain ⟨F, hF, ⟨e⟩⟩ := h M.obj M.property
    exact ⟨⟨F, hF⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **GAGA-3 for proper schemes**: for `X` proper over `ℂ`, every coherent analytic sheaf on
`X^an` is isomorphic to the analytification of a coherent sheaf on `X`. -/
theorem gaga₃_proper (hX : IsProperℂ X)
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    [M.IsCoherent] :
    ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M) :=
  gaga₃_proper' X hX relativeAnalyticSerre M

/-- **GAGA for proper schemes as an equivalence of categories**: for `X` proper over `ℂ`,
analytification is an equivalence between coherent sheaves on `X` and coherent analytic sheaves
on `X^an`. -/
theorem isEquivalence_coherentAnalytification_of_isProperℂ (hX : IsProperℂ X) :
    (coherentAnalytification X).IsEquivalence :=
  let hff := fullyFaithfulCoherentAnalytificationOfBijective (X := X)
    (fun F G _ _ ↦ gaga₂_proper hX F G)
  haveI := hff.full
  haveI := hff.faithful
  haveI := essSurj_coherentAnalytification_of_exists (X := X)
    (fun M _ ↦ gaga₃_proper hX M)
  { }

/-- **Serre's GAGA for proper schemes**, bundled: the equivalence between coherent sheaves on a
proper scheme `X` over `ℂ` and coherent analytic sheaves on `X^an` given by analytification. -/
def gagaEquivalenceOfIsProperℂ (hX : IsProperℂ X) :
    (SheafOfModules.isCoherent X.obj.left.toLocallyRingedSpace.ringSheaf).FullSubcategory ≌
      (SheafOfModules.isCoherent
        (analytification.obj X).toLocallyRingedSpace.ringSheaf).FullSubcategory :=
  haveI := isEquivalence_coherentAnalytification_of_isProperℂ hX
  (coherentAnalytification X).asEquivalence

/-- The functor of `ComplexAnalytic.gagaEquivalenceOfIsProperℂ` is analytification. -/
@[simp]
lemma gagaEquivalenceOfIsProperℂ_functor (hX : IsProperℂ X) :
    (gagaEquivalenceOfIsProperℂ hX).functor = coherentAnalytification X :=
  rfl

/-- **Serre's GAGA theorem for proper schemes**: for `X` proper over `ℂ`,
1. `Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective for coherent `F` and all `q` (GAGA-1);
2. `Hom(F, G) → Hom(F^an, G^an)` is bijective for coherent `F`, `G` (GAGA-2);
3. every coherent analytic sheaf on `X^an` is isomorphic to `F^an` for a coherent `F` (GAGA-3). -/
theorem gagaFull_proper (hX : IsProperℂ X) :
    (∀ (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ),
      Function.Bijective (gagaMap X F q)) ∧
    (∀ (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
      [F.IsCoherent] [G.IsCoherent],
      Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _)) ∧
    (∀ (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf),
      M.IsCoherent → ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
        F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M)) :=
  ⟨fun F _ q ↦ gaga₁_proper hX F q, fun F G _ _ ↦ gaga₂_proper hX F G,
    fun M hM ↦ haveI := hM; gaga₃_proper hX M⟩

end ComplexAnalytic

end
