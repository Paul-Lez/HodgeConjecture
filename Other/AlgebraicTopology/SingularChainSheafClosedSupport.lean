/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularChainSheafPushforward
public import HodgeConjecture.Definitions.AlgebraicTopology.DerivedSheafSupport

/-!
# Genuine closed support for pushed relative-chain sheaves

The direct image of a sheaf along a map with closed image restricts to zero on the
complement of that image. Consequently every map out of that direct image factors
canonically through the actual kernel defining sections with closed support.

Applying this to the constructed closed-embedding singular-chain pushforward gives
a factorization through termwise `sheafSectionsWithClosedSupport`, compatible with
the singular boundary and with regrading `n ↦ -n`. The factorization is constructed
by the kernel universal property; no support lift is supplied as data.

No boundedness is imposed on the possibly singular source, and no identification
with derived sections with support is asserted. The further support
quasi-isomorphism requires a relative-chain excision/comparison theorem and an
appropriate derived support comparison; the present factorization alone does not
prove either one.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe u

namespace AlgebraicTopology.Singular

variable {Z X : TopCat.{u}} (i : Z ⟶ X)

/-- The actual image of a closed embedding, as a closed support. -/
def closedEmbeddingSupport (hi : IsClosedEmbedding i) : Closeds X :=
  ⟨Set.range i, hi.isClosed_range⟩

/-- Direct-image sheaves restrict to zero on the complement of the actual closed image.
The proof evaluates on opens and uses the sheaf's zero empty-open value. -/
theorem pushforward_openRestriction_closedImage_isZero
    (hi : IsClosedEmbedding i) (F : TopCat.Sheaf AddCommGrpCat.{u} Z) :
    IsZero ((TopCat.Sheaf.openRestrictionPushforward X (closedEmbeddingSupport i hi).compl).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F)) := by
  apply IsZero.of_full_of_faithful_of_isZero (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
  apply Functor.isZero
  intro V
  let U := (closedEmbeddingSupport i hi).compl
  have hpre : (Opens.map i).obj
      (U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj V.unop)) = ⊥ := by
    ext z
    change (∃ y : U, y.1 ∈ V.unop ∧ y.1 = i z) ↔ False
    refine ⟨?_, False.elim⟩
    rintro ⟨y, _, hy⟩
    exact y.2 ⟨z, hy.symm⟩
  change IsZero (F.obj.obj (.op ((Opens.map i).obj
    (U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj V.unop)))))
  rw [hpre]
  exact F.isTerminalOfEmpty.isZero

/-- Any morphism out of a closed-embedding direct image vanishes after restriction off
the image. This is proved from the actual restriction natural transformation. -/
@[reassoc] lemma mapFromPushforward_restrict_closedImage_zero
    (hi : IsClosedEmbedding i)
    {F : TopCat.Sheaf AddCommGrpCat.{u} Z} {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F ⟶ G) :
    f ≫ (TopCat.Sheaf.toOpenRestrictionPushforward X
      (closedEmbeddingSupport i hi).compl).app G = 0 := by
  calc
    _ = (TopCat.Sheaf.toOpenRestrictionPushforward X
        (closedEmbeddingSupport i hi).compl).app _ ≫
        (TopCat.Sheaf.openRestrictionPushforward X
          (closedEmbeddingSupport i hi).compl).map f :=
      (TopCat.Sheaf.toOpenRestrictionPushforward X
        (closedEmbeddingSupport i hi).compl).naturality f
    _ = 0 := by
      rw [(pushforward_openRestriction_closedImage_isZero i hi F).eq_zero_of_tgt
        ((TopCat.Sheaf.toOpenRestrictionPushforward X
          (closedEmbeddingSupport i hi).compl).app _), zero_comp]

/-- The canonical closed-support lift of a morphism out of a closed-embedding direct image. -/
def mapFromPushforwardWithClosedSupport (hi : IsClosedEmbedding i)
    {F : TopCat.Sheaf AddCommGrpCat.{u} Z} {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F ⟶ G) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F ⟶
      (TopCat.Sheaf.sheafSectionsWithClosedSupport X (closedEmbeddingSupport i hi)).obj G :=
  TopCat.Sheaf.liftSheafSectionsSupportedOutside X (closedEmbeddingSupport i hi).compl f
    (mapFromPushforward_restrict_closedImage_zero i hi f)

/-- Forgetting the constructed support gives back the original sheaf morphism. -/
@[reassoc (attr := simp)] lemma mapFromPushforwardWithClosedSupport_inclusion
    (hi : IsClosedEmbedding i)
    {F : TopCat.Sheaf AddCommGrpCat.{u} Z} {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F ⟶ G) :
    mapFromPushforwardWithClosedSupport i hi f ≫
      (TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X
        (closedEmbeddingSupport i hi).compl).app G = f :=
  TopCat.Sheaf.liftSheafSectionsSupportedOutside_inclusion _ _ _ _

/-- The supported coefficient complex includes termwise into the original chain complex. -/
def singularChainClosedSupportInclusion (R : Type u) [Field R]
    (S : Closeds X) :
    ((TopCat.Sheaf.sheafSectionsWithClosedSupport X S).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X) ⟶
      singularChainSheafComplex R X where
  f n := (TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X S.compl).app
    ((singularChainSheafComplex R X).X n)
  comm' j k _ :=
    (TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X S.compl).naturality
      ((singularChainSheafComplex R X).d j k) |>.symm

variable (R : Type u) [Field R]

/-- The actual singular-chain sheaf pushforward restricts to zero outside the closed image. -/
@[reassoc] lemma singularChainSheafPushforward_restrict_zero
    (hi : IsClosedEmbedding i) (n : ℕ) :
    (singularChainSheafPushforward R i hi).f n ≫
      (TopCat.Sheaf.toOpenRestrictionPushforward X (closedEmbeddingSupport i hi).compl).app
        ((singularChainSheafComplex R X).X n) = 0 :=
  mapFromPushforward_restrict_closedImage_zero i hi ((singularChainSheafPushforward R i hi).f n)

set_option backward.isDefEq.respectTransparency false in
/-- Pushed singular-chain sheaves land canonically in sections with the actual closed image
as support. This definition imposes no smoothness or boundedness on `Z`. -/
def singularChainSheafPushforwardWithClosedSupport (hi : IsClosedEmbedding i) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z) ⟶
      ((TopCat.Sheaf.sheafSectionsWithClosedSupport X
        (closedEmbeddingSupport i hi)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (singularChainSheafComplex R X) where
  f n := mapFromPushforwardWithClosedSupport i hi ((singularChainSheafPushforward R i hi).f n)
  comm' j k _ := by
    let a := TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X
      (closedEmbeddingSupport i hi).compl
    have hm : Mono (a.app ((singularChainSheafComplex R X).X k)) :=
      inferInstanceAs (Mono (kernel.ι _))
    apply (cancel_mono (a.app ((singularChainSheafComplex R X).X k))).mp
    have hn : (TopCat.Sheaf.sheafSectionsWithClosedSupport X (closedEmbeddingSupport i hi)).map
        ((singularChainSheafComplex R X).d j k) ≫ a.app _ =
        a.app _ ≫ (singularChainSheafComplex R X).d j k :=
      a.naturality ((singularChainSheafComplex R X).d j k)
    have hj := mapFromPushforwardWithClosedSupport_inclusion i hi
      ((singularChainSheafPushforward R i hi).f j)
    have hk := mapFromPushforwardWithClosedSupport_inclusion i hi
      ((singularChainSheafPushforward R i hi).f k)
    calc
      _ = mapFromPushforwardWithClosedSupport i hi ((singularChainSheafPushforward R i hi).f j) ≫
          (a.app _ ≫ (singularChainSheafComplex R X).d j k) :=
        (Category.assoc _ _ _).trans (congrArg (fun f =>
          mapFromPushforwardWithClosedSupport i hi ((singularChainSheafPushforward R i hi).f j) ≫ f) hn)
      _ = (singularChainSheafPushforward R i hi).f j ≫
          (singularChainSheafComplex R X).d j k :=
        (Category.assoc _ _ _).symm.trans (congrArg
          (fun f => f ≫ (singularChainSheafComplex R X).d j k) hj)
      _ = _ := (singularChainSheafPushforward R i hi).comm j k
      _ = _ := ((Category.assoc _ _ _).trans (congrArg (fun f =>
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z)).d j k ≫ f) hk)).symm

/-- Degreewise support-forgetting is the original, chain-normalized pushforward. -/
@[reassoc (attr := simp)] lemma singularChainSheafPushforwardWithClosedSupport_f_inclusion
    (hi : IsClosedEmbedding i) (n : ℕ) :
    (singularChainSheafPushforwardWithClosedSupport i R hi).f n ≫
      (singularChainClosedSupportInclusion R (closedEmbeddingSupport i hi)).f n =
        (singularChainSheafPushforward R i hi).f n :=
  mapFromPushforwardWithClosedSupport_inclusion _ _ _

/-- The factorization holds as an equality of chain maps. -/
@[reassoc (attr := simp)] lemma singularChainSheafPushforwardWithClosedSupport_inclusion
    (hi : IsClosedEmbedding i) :
    singularChainSheafPushforwardWithClosedSupport i R hi ≫
      singularChainClosedSupportInclusion R (closedEmbeddingSupport i hi) =
        singularChainSheafPushforward R i hi := by
  ext n
  exact singularChainSheafPushforwardWithClosedSupport_f_inclusion i R hi n

/-- The kernel universal property makes the support lift unique, as a chain map. -/
theorem singularChainSheafPushforwardWithClosedSupport_unique
    (hi : IsClosedEmbedding i)
    (g : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z) ⟶
      ((TopCat.Sheaf.sheafSectionsWithClosedSupport X
        (closedEmbeddingSupport i hi)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (singularChainSheafComplex R X))
    (hg : g ≫ singularChainClosedSupportInclusion R (closedEmbeddingSupport i hi) =
      singularChainSheafPushforward R i hi) :
    g = singularChainSheafPushforwardWithClosedSupport i R hi := by
  ext n
  exact TopCat.Sheaf.liftSheafSectionsSupportedOutside_unique X
    (closedEmbeddingSupport i hi).compl ((singularChainSheafPushforward R i hi).f n)
    (singularChainSheafPushforward_restrict_zero i R hi n) (g.f n)
    (congrArg (fun f => f.f n) hg)

/-- The chain-level support factorization also preserves the induced homology morphisms. -/
@[reassoc (attr := simp)] theorem singularChainSheafPushforwardWithClosedSupport_homology
    (hi : IsClosedEmbedding i) (n : ℕ) :
    HomologicalComplex.homologyMap (singularChainSheafPushforwardWithClosedSupport i R hi) n ≫
      HomologicalComplex.homologyMap
        (singularChainClosedSupportInclusion R (closedEmbeddingSupport i hi)) n =
      HomologicalComplex.homologyMap (singularChainSheafPushforward R i hi) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    singularChainSheafPushforwardWithClosedSupport_inclusion]

set_option backward.isDefEq.respectTransparency false in
/-- Even after adding genuine closed support, forgetting that support sends each original
relative chain through the same pair-induced, exactly normalized sheafification map. -/
@[reassoc] lemma singularChainSheafPushforwardWithClosedSupport_unit
    (hi : IsClosedEmbedding i) (n : ℕ) :
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map
        (toSheafify (Opens.grothendieckTopology Z) (singularChainPresheaf R Z n)) ≫
      ((singularChainSheafPushforwardWithClosedSupport i R hi).f n).hom ≫
        ((singularChainClosedSupportInclusion R (closedEmbeddingSupport i hi)).f n).hom =
      singularChainPresheafPushforward R i n ≫
        toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n) := by
  have h := congrArg (fun f => f.hom)
    (singularChainSheafPushforwardWithClosedSupport_f_inclusion i R hi n)
  change ((singularChainSheafPushforwardWithClosedSupport i R hi).f n).hom ≫
      ((singularChainClosedSupportInclusion R (closedEmbeddingSupport i hi)).f n).hom =
      ((singularChainSheafPushforward R i hi).f n).hom at h
  rw [h]
  exact singularChainSheafPushforward_unit R i hi n

/-- The constructed support factorization, regraded by homological `n ↦ -n`. -/
def singularChainSheafPushforwardWithClosedSupportRegraded (hi : IsClosedEmbedding i) :
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainSheafComplex R Z)).extend
        ComplexShape.embeddingDownNat ⟶
      (((TopCat.Sheaf.sheafSectionsWithClosedSupport X
        (closedEmbeddingSupport i hi)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (singularChainSheafComplex R X)).extend ComplexShape.embeddingDownNat :=
  HomologicalComplex.extendMap (singularChainSheafPushforwardWithClosedSupport i R hi)
    ComplexShape.embeddingDownNat

/-- Forgetting the regraded closed support recovers the actual regraded pushforward. -/
@[reassoc (attr := simp)] lemma singularChainSheafPushforwardWithClosedSupportRegraded_inclusion
    (hi : IsClosedEmbedding i) :
    singularChainSheafPushforwardWithClosedSupportRegraded i R hi ≫
      HomologicalComplex.extendMap
        (singularChainClosedSupportInclusion R (closedEmbeddingSupport i hi))
        ComplexShape.embeddingDownNat = singularChainSheafPushforwardRegraded R i hi := by
  rw [singularChainSheafPushforwardWithClosedSupportRegraded,
    ← HomologicalComplex.extendMap_comp,
    singularChainSheafPushforwardWithClosedSupport_inclusion]
  rfl

end AlgebraicTopology.Singular
