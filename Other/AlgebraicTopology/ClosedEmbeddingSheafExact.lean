/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularChainSheafPushforward
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exactness of actual closed-embedding sheaf pushforward

The direct image here is the ordinary sheaf direct image defined by preimages of opens.
Its stalk at `i z` is the source stalk at `z`, through the actual germ comparison; its
stalk off the closed image is zero. These facts prove exactness and preservation of
quasi-isomorphisms, with no proper-direct-image or exceptional-pullback hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe u

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Z X : TopCat.{u}} (i : Z ⟶ X) (hi : IsClosedEmbedding i)

include hi

/-- The canonical direct-image stalk identification on the image of a closed embedding. -/
def closedEmbeddingPushforwardStalkIso (F : Sheaf AddCommGrpCat.{u} Z) (z : Z) :
    (forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} (i z)).obj
        ((pushforward AddCommGrpCat.{u} i).obj F) ≅
      (forget AddCommGrpCat.{u} Z ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} z).obj F := by
  have h := Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    AddCommGrpCat.{u} hi.isEmbedding.isInducing F.obj z
  exact asIso (Presheaf.stalkPushforward AddCommGrpCat.{u} i F.obj z)

/-- The image-stalk isomorphism preserves the actual representative germ. -/
@[reassoc]
lemma closedEmbeddingPushforwardStalkIso_germ (F : Sheaf AddCommGrpCat.{u} Z)
    (V : Opens X) (z : Z) (hz : i z ∈ V) :
    Presheaf.germ ((pushforward AddCommGrpCat.{u} i).obj F).obj V (i z) hz ≫
      (closedEmbeddingPushforwardStalkIso i hi F z).hom =
      Presheaf.germ F.obj ((Opens.map i).obj V) z hz :=
  Presheaf.stalkPushforward_germ AddCommGrpCat.{u} i F.obj V z hz

/-- The image-stalk identification is natural in the coefficient sheaf. -/
def closedEmbeddingPushforwardStalkFunctorIso (z : Z) :
    pushforward AddCommGrpCat.{u} i ⋙ forget AddCommGrpCat.{u} X ⋙
        Presheaf.stalkFunctor AddCommGrpCat.{u} (i z) ≅
      forget AddCommGrpCat.{u} Z ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} z :=
  NatIso.ofComponents (fun F => closedEmbeddingPushforwardStalkIso i hi F z)
    (fun f => AlgebraicTopology.Singular.stalkPushforward_naturality_additive i f.hom z)

/-- Off the closed image, every actual direct-image sheaf stalk is zero. -/
theorem closedEmbeddingPushforwardStalk_isZero (F : Sheaf AddCommGrpCat.{u} Z)
    (x : X) (hx : x ∉ Set.range i) :
    IsZero ((forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((pushforward AddCommGrpCat.{u} i).obj F)) :=
  AlgebraicTopology.Singular.pushforward_stalk_isZero_of_not_mem_range
    i hi.isClosed_range F.obj (isTerminalOfEmpty F).isZero x hx

/-- Closed-embedding direct image preserves exact short complexes, proved on actual stalks. -/
theorem closedEmbeddingPushforward_map_exact
    (S : ShortComplex (Sheaf AddCommGrpCat.{u} Z)) (hS : S.Exact) :
    (S.map (pushforward AddCommGrpCat.{u} i)).Exact := by
  rw [exact_iff_stalkFunctor_map_exact]
  intro x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hx
    exact ShortComplex.exact_of_iso
      (S.mapNatIso (closedEmbeddingPushforwardStalkFunctorIso i hi z)).symm
      (hS.map (forget AddCommGrpCat.{u} Z ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} z))
  · exact ShortComplex.exact_of_isZero_X₂ _
      (closedEmbeddingPushforwardStalk_isZero i hi S.X₂ x hx)

/-- Preservation of homology is a theorem of the concrete closed-embedding direct image. -/
theorem closedEmbeddingPushforward_preservesHomology :
    (pushforward AddCommGrpCat.{u} i).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (closedEmbeddingPushforward_map_exact i hi)

/-- Closed-embedding direct image preserves finite colimits as well as the limits already
provided by its sheaf pullback/direct-image adjunction. -/
theorem closedEmbeddingPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (pushforward AddCommGrpCat.{u} i) := by
  have h := closedEmbeddingPushforward_preservesHomology i hi
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Applying actual closed-embedding pushforward termwise preserves quasi-isomorphisms. -/
theorem closedEmbeddingPushforward_map_quasiIso {I : Type*} {c : ComplexShape I}
    {K L : HomologicalComplex (Sheaf AddCommGrpCat.{u} Z) c}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso
      (((pushforward AddCommGrpCat.{u} i).mapHomologicalComplex c).map f) := by
  have h := closedEmbeddingPushforward_preservesHomology i hi
  infer_instance

end TopCat.Sheaf
