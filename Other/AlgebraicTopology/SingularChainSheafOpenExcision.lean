/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularChainSheafOpenRestriction

/-!
# The open-inclusion comparison is a quasi-isomorphism

The actual chain-sheaf comparison is a quasi-isomorphism over `ℚ` on Hausdorff spaces.
The proof uses its normalized stalk formula and the proved rational neighborhood-excision
theorem, rather than assuming an open-restriction comparison or a chain-stalk isomorphism.
The universe and coefficient restriction on excision match the current subdivision API.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite HomologicalComplex

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat} (U : Opens X)

/-- The two presentations of the intrinsic punctured pair differ only by subtype equality.
Both directions are the identity on actual underlying points. -/
def openSubsetPointExcisionPairIso (y : (Opens.toTopCat X).obj U) :
    TopPair.ofSubset (X := (Opens.toTopCat X).obj U)
        ({y} : Set ((Opens.toTopCat X).obj U))ᶜ ≅
      neighborhoodPointComplementPair (U : Set X) y.val where
  hom := TopPair.ofHom (𝟙 _) (TopCat.ofHom
    ⟨fun z => ⟨z.val, fun h => z.property (Subtype.ext h)⟩,
      continuous_subtype_val.subtype_mk _⟩) rfl
  inv := TopPair.ofHom (𝟙 _) (TopCat.ofHom
    ⟨fun z => ⟨z.val, fun h => z.property (congrArg Subtype.val h)⟩,
      continuous_subtype_val.subtype_mk _⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z; rfl
    · rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z; rfl
    · rfl

/-- The normalized map of punctured pairs is exactly the previously proved excision map. -/
lemma openSubsetPointExcisionPairIso_hom_comp (y : (Opens.toTopCat X).obj U) :
    (openSubsetPointExcisionPairIso U y).hom ≫
      neighborhoodPointComplementPairMap (U : Set X) y.val = openSubsetPointPairMap U y := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z; rfl
  · rfl

/-- Rational point excision applies to the actual normalized point-pair map. -/
theorem openSubsetPointPairMap_quasiIso [T2Space X] (y : (Opens.toTopCat X).obj U) :
    QuasiIso ((relativeChainFunctor ℚ).map (openSubsetPointPairMap U y)) := by
  rw [← openSubsetPointExcisionPairIso_hom_comp, Functor.map_comp]
  have h := neighborhoodPointComplement_relativeChainMap_quasiIso
    (U : Set X) y.val U.isOpen y.property
  infer_instance

/-- The actual chain map on each stalk is a quasi-isomorphism, by neighborhood excision.
There is deliberately no assertion that this map is a chain-complex isomorphism. -/
theorem singularChainSheafOpenRestriction_stalk_quasiIso [T2Space X]
    (y : (Opens.toTopCat X).obj U) :
    QuasiIso (((TopCat.Sheaf.forget AddCommGrpCat ((Opens.toTopCat X).obj U) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat y).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (singularChainSheafOpenRestriction U ℚ)) := by
  have h := openSubsetPointPairMap_quasiIso U y
  have hcomp : QuasiIso
      ((singularChainSheafStalkIso ℚ ((Opens.toTopCat X).obj U) y).hom ≫
        ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            ((relativeChainFunctor ℚ).map (openSubsetPointPairMap U y))) := by infer_instance
  rw [← singularChainSheafOpenRestriction_stalk] at hcomp
  exact (quasiIso_iff_comp_right _ _).mp hcomp

/-- Stalkwise quasi-isomorphisms of additive-group sheaf complexes are quasi-isomorphisms.
This follows from exactness of stalks and detection of sheaf isomorphisms on stalks. -/
theorem sheafChainMap_quasiIso_of_stalk {Y : TopCat}
    {K L : ChainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ} (f : K ⟶ L)
    (h : ∀ y : Y, QuasiIso (((TopCat.Sheaf.forget AddCommGrpCat Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat y).mapHomologicalComplex
        (ComplexShape.down ℕ)).map f)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso
    (HomologicalComplex.homologyMap f n)).mpr
  intro y
  let F := TopCat.Sheaf.forget AddCommGrpCat Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  have hf : QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) := h y
  have heq := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (TopCat.Sheaf AddCommGrpCat Y) (ComplexShape.down ℕ) n).map f) F
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
      ((L.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapHomologyIso F).hom ≫ F.map (HomologicalComplex.homologyMap f n) at heq
  have hcomp : IsIso (((K.sc n).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap f n)) := by
    rw [← heq]
    infer_instance
  exact IsIso.of_isIso_comp_left ((K.sc n).mapHomologyIso F).hom
    (F.map (HomologicalComplex.homologyMap f n))

/-- The intrinsic chain sheaf on an open subspace is canonically quasi-isomorphic to the
restriction of the ambient chain sheaf, with its actual pair-induced normalization. -/
theorem singularChainSheafOpenRestriction_quasiIso [T2Space X] :
    QuasiIso (singularChainSheafOpenRestriction U ℚ) :=
  sheafChainMap_quasiIso_of_stalk _ (singularChainSheafOpenRestriction_stalk_quasiIso U)

/-- The open comparison remains a quasi-isomorphism after the `n ↦ -n` regrading. -/
theorem singularChainSheafOpenRestrictionRegraded_quasiIso [T2Space X] :
    QuasiIso (singularChainSheafOpenRestrictionRegraded U ℚ) :=
  (quasiIso_extendMap_iff _ ComplexShape.embeddingDownNat).mpr
    (singularChainSheafOpenRestriction_quasiIso U)

end AlgebraicTopology.Singular
