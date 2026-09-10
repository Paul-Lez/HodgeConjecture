/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenRestrictionStalk
public import Other.AlgebraicTopology.SingularChainSheafStalk
public import Other.AlgebraicTopology.RelativePairExcision

/-!
# Excision and the open restriction of the actual singular-chain sheaf

For an open subspace `U` of `X`, inclusion of the actual relative pairs constructs a map
from the intrinsic chain sheaf of `U` to the restriction of the ambient chain sheaf.
On point stalks it is the inclusion of point-complement pairs. This is not generally an
isomorphism of chain stalks: ambient simplices need not remain in `U`. Rational singular
excision is the mechanism giving the homology comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

universe u

namespace AlgebraicTopology.Singular

variable {X : TopCat.{u}} (U : Opens X)

instance singularChainOpenSubspace_t2 [T2Space X] :
    T2Space ((Opens.toTopCat X).obj U) := inferInstanceAs (T2Space U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Inclusion of an open subspace gives an actual map of complement-support pairs. -/
def openSubsetSupportPairMap (V : Opens ((Opens.toTopCat X).obj U)) :
    TopPair.ofSubset (X := (Opens.toTopCat X).obj U)
        (V : Set ((Opens.toTopCat X).obj U))ᶜ ⟶
      TopPair.ofSubset (X := X) (U.isOpenEmbedding.functor.obj V : Set X)ᶜ := by
  refine TopPair.ofHom U.inclusion' ?_ ?_
  · have hmem : ∀ z : ((V : Set ((Opens.toTopCat X).obj U))ᶜ :
        Set ((Opens.toTopCat X).obj U)), z.val.val ∈
        (U.isOpenEmbedding.functor.obj V : Set X)ᶜ := by
      rintro z ⟨w, hw, heq⟩
      exact z.property ((Subtype.ext heq) ▸ hw)
    exact TopCat.ofHom ⟨fun z => ⟨z.val.val, hmem z⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hmem⟩
  · rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The point-complement version of the actual open inclusion. -/
def openSubsetPointPairMap (y : (Opens.toTopCat X).obj U) :
    TopPair.ofSubset (X := (Opens.toTopCat X).obj U)
        ({y} : Set ((Opens.toTopCat X).obj U))ᶜ ⟶
      TopPair.ofSubset (X := X) ({y.val} : Set X)ᶜ := by
  refine TopPair.ofHom U.inclusion' ?_ ?_
  · have hmem : ∀ z : (({y} : Set ((Opens.toTopCat X).obj U))ᶜ :
        Set ((Opens.toTopCat X).obj U)), z.val.val ∈ ({y.val} : Set X)ᶜ :=
      fun z hz => z.property (Subtype.ext hz)
    exact TopCat.ofHom ⟨fun z => ⟨z.val.val, hmem z⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hmem⟩
  · rfl

/-- Inclusion of relative pairs commutes with restriction from an open support to a point. -/
lemma openSubsetSupportPairMap_restrict (V : Opens ((Opens.toTopCat X).obj U))
    (y : (Opens.toTopCat X).obj U) (hy : y ∈ V) :
    openSubsetSupportPairMap U V ≫
        supportInclusionPairMap X (Set.singleton_subset_iff.mpr
          (Set.mem_image_of_mem U.inclusion' hy)) =
      supportInclusionPairMap ((Opens.toTopCat X).obj U)
          (Set.singleton_subset_iff.mpr hy) ≫ openSubsetPointPairMap U y := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z; rfl
  · rfl

variable (R : Type u) [Field R]

/-- The actual open-inclusion maps form a natural transformation of pair-valued presheaves. -/
def openComplementPairRestriction :
    openComplementPairFunctor ((Opens.toTopCat X).obj U) ⟶
      U.isOpenEmbedding.functor.op ⋙ openComplementPairFunctor X where
  app V := openSubsetSupportPairMap U V.unop
  naturality {V W} a := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z; rfl
    · rfl

/-- The corresponding relative singular-chain map on presheaves in degree `n`. -/
def singularChainPresheafOpenRestriction (n : ℕ) :
    singularChainPresheaf R ((Opens.toTopCat X).obj U) n ⟶
      TopCat.Presheaf.openRestriction U (singularChainPresheaf R X n) :=
  Functor.whiskerRight
    (Functor.whiskerRight (openComplementPairRestriction U) (relativeChainFunctor R))
    (chainDegreeAdditiveFunctor R n)

@[simp]
lemma singularChainPresheafOpenRestriction_app (n : ℕ)
    (V : Opens ((Opens.toTopCat X).obj U)) :
    (singularChainPresheafOpenRestriction U R n).app (op V) =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map (openSubsetSupportPairMap U V)).f n) := rfl

/-- The sheaf map is obtained from the actual pair map and the sheafification unit. -/
def singularChainSheafOpenRestrictionDegree (n : ℕ) :
    singularChainSheaf R ((Opens.toTopCat X).obj U) n ⟶
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj (singularChainSheaf R X n) :=
  ⟨sheafifyLift (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    (singularChainPresheafOpenRestriction U R n ≫
      Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)))
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj
      (singularChainSheaf R X n)).property⟩

@[reassoc]
lemma singularChainSheafOpenRestrictionDegree_unit (n : ℕ) :
    toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        (singularChainPresheaf R ((Opens.toTopCat X).obj U) n) ≫
      (singularChainSheafOpenRestrictionDegree U R n).hom =
      singularChainPresheafOpenRestriction U R n ≫
        Functor.whiskerLeft U.isOpenEmbedding.functor.op
          (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)) :=
  toSheafify_sheafifyLift _ _ _

/-- Naturality of the singular boundary before sheafification. -/
@[reassoc]
lemma singularChainPresheafOpenRestriction_boundary (n : ℕ) :
    singularChainPresheafOpenRestriction U R (n + 1) ≫
        Functor.whiskerLeft U.isOpenEmbedding.functor.op (singularChainBoundary R X n) =
      singularChainBoundary R ((Opens.toTopCat X).obj U) n ≫
        singularChainPresheafOpenRestriction U R n :=
  NatTrans.ext (funext fun V ↦ congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
    (((relativeChainFunctor R).map (openSubsetSupportPairMap U V.unop)).comm (n + 1) n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual open-inclusion map commutes with the sheafified boundary. -/
@[reassoc]
lemma singularChainSheafOpenRestrictionDegree_boundary (n : ℕ) :
    singularChainSheafOpenRestrictionDegree U R (n + 1) ≫
        (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map
          (singularChainSheafBoundary R X n) =
      singularChainSheafBoundary R ((Opens.toTopCat X).obj U) n ≫
        singularChainSheafOpenRestrictionDegree U R n := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext _ _ _
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj
      (singularChainSheaf R X n)).property
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ← Category.assoc, singularChainSheafOpenRestrictionDegree_unit]
  change _ = _ ≫ sheafifyMap _ (singularChainBoundary R ((Opens.toTopCat X).obj U) n) ≫ _
  rw [← toSheafify_naturality_assoc, singularChainSheafOpenRestrictionDegree_unit]
  change (singularChainPresheafOpenRestriction U R (n + 1) ≫
    Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X (n + 1)))) ≫
    Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (sheafifyMap (Opens.grothendieckTopology X) (singularChainBoundary R X n)) = _
  rw [Category.assoc, ← Functor.whiskerLeft_comp, ← toSheafify_naturality,
    Functor.whiskerLeft_comp, ← Category.assoc]
  exact singularChainPresheafOpenRestriction_boundary_assoc U R n
    (Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)))

/-- The actual intrinsic-to-ambient open comparison of chain sheaf complexes. -/
def singularChainSheafOpenRestriction :
    singularChainSheafComplex R ((Opens.toTopCat X).obj U) ⟶
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X) where
  f n := singularChainSheafOpenRestrictionDegree U R n
  comm' j k hjk := by
    obtain rfl := hjk
    simp only [Functor.mapHomologicalComplex_obj_d, singularChainSheafComplex_d]
    exact singularChainSheafOpenRestrictionDegree_boundary U R k

/-- On complexes, taking a stalk of actual open restriction gives the ambient stalk. -/
def openRestrictionSheafComplexStalkIso
    (K : ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (y : (Opens.toTopCat X).obj U) :
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K) ≅
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y.val).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => TopCat.Presheaf.openRestrictionStalkIso U (K.X n).obj y)
    (fun n m _ => (TopCat.Presheaf.openRestrictionStalkHom_naturality U y (K.d n m).hom).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The local relative-chain identification retains its exact normalization after the
sheafification unit. -/
@[reassoc]
lemma singularChainSheafStalkIso_unit {Y : TopCat.{u}} [T2Space Y] (y : Y) (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (toSheafify (Opens.grothendieckTopology Y) (singularChainPresheaf R Y n)) ≫
      (singularChainSheafStalkIso R Y y).hom.f n =
      (singularChainPresheafStalkIso R Y y n).hom := by
  have h : (singularChainSheafificationStalkIso R Y y).hom ≫
      (singularChainSheafStalkIso R Y y).hom =
      (singularChainPresheafComplexStalkIso R Y y).hom := by
    dsimp only [singularChainSheafStalkIso, Iso.trans_hom, Iso.symm_hom]
    exact Iso.hom_inv_id_assoc _ _
  exact congrArg (fun f => f.f n) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Germ normalization for the actual sheaf-chain open comparison. -/
@[reassoc]
lemma singularChainSheafOpenRestriction_unit_germ
    (n : ℕ) (V : Opens ((Opens.toTopCat X).obj U))
    (y : (Opens.toTopCat X).obj U) (hy : y ∈ V) :
    (toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        (singularChainPresheaf R ((Opens.toTopCat X).obj U) n)).app (op V) ≫
      (singularChainSheafOpenRestrictionDegree U R n).hom.app (op V) ≫
      TopCat.Presheaf.germ
        (TopCat.Presheaf.openRestriction U (singularChainSheaf R X n).obj) V y hy ≫
      TopCat.Presheaf.openRestrictionStalkHom U (singularChainSheaf R X n).obj y =
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map (openSubsetSupportPairMap U V)).f n) ≫
      (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)).app
        (op (U.isOpenEmbedding.functor.obj V)) ≫
      TopCat.Presheaf.germ (singularChainSheaf R X n).obj
        (U.isOpenEmbedding.functor.obj V) y.val (Set.mem_image_of_mem U.inclusion' hy) := by
  rw [TopCat.Presheaf.germ_openRestrictionStalkHom, ← Category.assoc,
    ← NatTrans.comp_app, singularChainSheafOpenRestrictionDegree_unit]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The stalk map of open comparison, under the constructed local-chain identifications,
is exactly inclusion of point-complement pairs. No chain-stalk isomorphism is claimed. -/
lemma singularChainSheafOpenRestriction_stalk [T2Space X]
    (y : (Opens.toTopCat X).obj U) :
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (singularChainSheafOpenRestriction U R) ≫
      (openRestrictionSheafComplexStalkIso U (singularChainSheafComplex R X) y).hom ≫
      (singularChainSheafStalkIso R X y.val).hom =
    (singularChainSheafStalkIso R ((Opens.toTopCat X).obj U) y).hom ≫
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).map ((relativeChainFunctor R).map (openSubsetPointPairMap U y)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
    ((singularChainSheafificationUnit R ((Opens.toTopCat X).obj U)).f n))).mp
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      (toSheafify _ (singularChainPresheaf R ((Opens.toTopCat X).obj U) n)) ≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (singularChainSheafOpenRestrictionDegree U R n).hom ≫
        TopCat.Presheaf.openRestrictionStalkHom U (singularChainSheaf R X n).obj y ≫
        (singularChainSheafStalkIso R X y.val).hom.f n) =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      (toSheafify _ (singularChainPresheaf R ((Opens.toTopCat X).obj U) n)) ≫
      ((singularChainSheafStalkIso R ((Opens.toTopCat X).obj U) y).hom.f n ≫
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map (openSubsetPointPairMap U y)).f n))
  rw [singularChainSheafStalkIso_unit_assoc]
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hy
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    singularChainPresheafStalkIso_germ_assoc]
  erw [singularChainSheafOpenRestriction_unit_germ_assoc U R n V y hy]
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    singularChainSheafStalkIso_unit, singularChainPresheafStalkIso_germ]
  have h := congrArg ((relativeChainFunctor R).map)
    (openSubsetSupportPairMap_restrict U V y hy)
  simp only [Functor.map_comp] at h
  exact congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
    (congrArg (fun f => f.f n) h)

/-- The same constructed open comparison after placing homological degree `n` in degree
`-n`. The target is explicitly the regraded restricted chain complex. -/
def singularChainSheafOpenRestrictionRegraded :
    singularChainSheafCochainComplex R ((Opens.toTopCat X).obj U) ⟶
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X)).extend
          ComplexShape.embeddingDownNat :=
  HomologicalComplex.extendMap (singularChainSheafOpenRestriction U R)
    ComplexShape.embeddingDownNat

end AlgebraicTopology.Singular
