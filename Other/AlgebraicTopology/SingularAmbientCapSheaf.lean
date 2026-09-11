/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCapNaturality
public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularChainSheafStalk

/-!
# The ambient-cochain cap action on the relative-chain sheaf

A fixed singular cochain on the ambient space acts on relative chains `(X,A)` by the
Alexander–Whitney cap product followed by the relative projection, and naturality makes
the action descend through the quotient by chains in `A`. It commutes with restriction of
the open support, so it sheafifies on the relative-chain sheaves.

The cochain is defined on the whole ambient space, since large relative-chain simplices can
leave the domain of a merely local cochain. Upgrading this to an action of the sheaf of
local singular cochains needs the small-chain/excision comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

/-- The ambient cap product followed by the actual relative projection. -/
def ambientCapRelativeLift (P : TopPair.{u}) (p q : ℕ)
    (φ : Simplicial.Cochain R (TopCat.toSSet.obj P.fst) p) :
    Simplicial.ChainGroup R (TopCat.toSSet.obj P.fst) (p + q) ⟶
      RelativeChainGroup R P q :=
  Simplicial.capHom R p q φ ≫ (relativeChainProjection R P).f q

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The cap lift kills every chain in the relative subspace, by actual cap naturality. -/
lemma subspaceChain_ambientCapRelativeLift (P : TopPair.{u}) (p q : ℕ)
    (φ : Simplicial.Cochain R (TopCat.toSSet.obj P.fst) p) :
    ((chainPairFunctor R).obj P).hom.f (p + q) ≫ ambientCapRelativeLift R P p q φ = 0 := by
  have hcap : ((chainPairFunctor R).obj P).hom.f (p + q) ≫ Simplicial.capHom R p q φ =
      Simplicial.capHom R p q
        (Simplicial.cochainMap R (TopCat.toSSet.map P.map) p φ) ≫
          ((chainPairFunctor R).obj P).hom.f q := by
    apply ModuleCat.hom_ext
    ext c
    exact (Simplicial.cap_naturality R (TopCat.toSSet.map P.map) p q φ c).symm
  have hz := congrArg (fun f => f.f q) (subspaceChainMap_relativeChainProjection R P)
  change ((chainPairFunctor R).obj P).hom.f q ≫ (relativeChainProjection R P).f q = 0 at hz
  rw [ambientCapRelativeLift, ← Category.assoc, hcap, Category.assoc, hz, comp_zero]

/-- Cap by an ambient cochain on the actual quotient relative-chain group. -/
def relativeAmbientCapHom (P : TopPair.{u}) (p q : ℕ)
    (φ : Simplicial.Cochain R (TopCat.toSSet.obj P.fst) p) :
    RelativeChainGroup R P (p + q) ⟶ RelativeChainGroup R P q :=
  (relativeChainProjectionComponentIsCokernelForCap R P (p + q)).desc
    (CokernelCofork.ofπ (ambientCapRelativeLift R P p q φ)
      (subspaceChain_ambientCapRelativeLift R P p q φ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The quotient cap retains the exact Alexander–Whitney formula on every representative. -/
@[reassoc (attr := simp)]
lemma relativeChainProjection_relativeAmbientCapHom (P : TopPair.{u}) (p q : ℕ)
    (φ : Simplicial.Cochain R (TopCat.toSSet.obj P.fst) p) :
    (relativeChainProjection R P).f (p + q) ≫ relativeAmbientCapHom R P p q φ =
      Simplicial.capHom R p q φ ≫ (relativeChainProjection R P).f q :=
  (Cofork.IsColimit.π_desc (relativeChainProjectionComponentIsCokernelForCap R P (p + q))
    (t := CokernelCofork.ofπ (ambientCapRelativeLift R P p q φ)
      (subspaceChain_ambientCapRelativeLift R P p q φ))).trans (CokernelCofork.π_ofπ _ _ _)

variable (X : TopCat.{u}) (p q : ℕ)
  (φ : Simplicial.Cochain R (TopCat.toSSet.obj X) p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction of the relative support commutes with the actual ambient-cochain cap. -/
@[reassoc]
lemma relativeAmbientCapHom_supportInclusion {Z W : Set X} (h : Z ⊆ W) :
    ((relativeChainFunctor R).map (supportInclusionPairMap X h)).f (p + q) ≫
        relativeAmbientCapHom R (TopPair.ofSubset Zᶜ) p q φ =
      relativeAmbientCapHom R (TopPair.ofSubset Wᶜ) p q φ ≫
        ((relativeChainFunctor R).map (supportInclusionPairMap X h)).f q := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap R (TopPair.ofSubset Wᶜ) (p + q))
  change (relativeChainProjection R (TopPair.ofSubset Wᶜ)).f (p + q) ≫ _ =
    (relativeChainProjection R (TopPair.ofSubset Wᶜ)).f (p + q) ≫ _
  have hn (k : ℕ) := congrArg (fun f => f.f k) (relativeChainProjection_supportInclusion R X h)
  change ∀ k, (relativeChainProjection R (TopPair.ofSubset Wᶜ)).f k ≫
    ((relativeChainFunctor R).map (supportInclusionPairMap X h)).f k =
      (relativeChainProjection R (TopPair.ofSubset Zᶜ)).f k at hn
  rw [← Category.assoc, hn, relativeChainProjection_relativeAmbientCapHom,
    relativeChainProjection_relativeAmbientCapHom_assoc, hn]

/-- The degreewise cap action is an actual morphism of the relative-chain presheaves. -/
def singularChainPresheafAmbientCap :
    singularChainPresheaf R X (p + q) ⟶ singularChainPresheaf R X q where
  app U := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    (relativeAmbientCapHom R (TopPair.ofSubset (U.unop : Set X)ᶜ) p q φ)
  naturality U V f := by
    exact congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
      (relativeAmbientCapHom_supportInclusion R X p q φ (leOfHom f.unop))

/-- Sheafification of the actual presheaf cap action. -/
def singularChainSheafAmbientCap :
    singularChainSheaf R X (p + q) ⟶ singularChainSheaf R X q :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (singularChainPresheafAmbientCap R X p q φ)

/-- Sheafification preserves the literal cap action on the original relative-chain sections. -/
@[reassoc]
lemma singularChainSheafAmbientCap_unit :
    toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X (p + q)) ≫
      (singularChainSheafAmbientCap R X p q φ).hom =
    singularChainPresheafAmbientCap R X p q φ ≫
      toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X q) :=
  (toSheafify_naturality (Opens.grothendieckTopology X)
    (singularChainPresheafAmbientCap R X p q φ)).symm

/-- The cap boundary identity on actual relative-chain classes, with its exact sign. -/
lemma relativeAmbientCapHom_boundary_apply
    (P : TopPair.{u}) (p q : ℕ)
    (φ : Simplicial.Cochain R (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary R p φ = 0)
    (c : RelativeChainGroup R P (p + q + 1)) :
    relativeBoundary R P q ((relativeAmbientCapHom R P p (q + 1) φ).hom c) =
      (-1 : R) ^ p • (relativeAmbientCapHom R P p q φ).hom
        (relativeBoundary R P (p + q) c) := by
  let π := (relativeChainProjection R P).f (p + q + 1)
  let : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap R P (p + q + 1))
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance c
  dsimp only [π]
  have hproj (k : ℕ) (a : Simplicial.ChainGroup R (TopCat.toSSet.obj P.fst) (p + k)) :=
    ConcreteCategory.congr_hom (relativeChainProjection_relativeAmbientCapHom R P p k φ) a
  change ∀ k a,
    (relativeAmbientCapHom R P p k φ).hom (((relativeChainProjection R P).f (p + k)).hom a) =
      ((relativeChainProjection R P).f k).hom (Simplicial.cap R p k φ a) at hproj
  erw [hproj, relativeBoundary_projection, relativeBoundary_projection, hproj,
    Simplicial.boundary_cap_eq_of_cocycle R p q φ hφ, map_smul]

/-- The relative cap maps satisfy the signed differential identity as actual morphisms. -/
lemma relativeAmbientCapHom_boundary (P : TopPair.{u}) (p q : ℕ)
    (φ : Simplicial.Cochain R (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary R p φ = 0) :
    relativeAmbientCapHom R P p (q + 1) φ ≫ ((relativeChainFunctor R).obj P).d (q + 1) q =
      (-1 : ℤ) ^ p •
        (((relativeChainFunctor R).obj P).d (p + q + 1) (p + q) ≫
          relativeAmbientCapHom R P p q φ) := by
  apply ModuleCat.hom_ext
  ext c
  change relativeBoundary R P q ((relativeAmbientCapHom R P p (q + 1) φ).hom c) =
    (-1 : ℤ) ^ p • (relativeAmbientCapHom R P p q φ).hom (relativeBoundary R P (p + q) c)
  rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact relativeAmbientCapHom_boundary_apply R P p q φ hφ c

/-- The actual presheaf action retains the signed cap-boundary identity. -/
lemma singularChainPresheafAmbientCap_boundary
    (hφ : Simplicial.coboundary R p φ = 0) :
    singularChainPresheafAmbientCap R X p (q + 1) φ ≫ singularChainBoundary R X q =
      (-1 : ℤ) ^ p •
        (singularChainBoundary R X (p + q) ≫ singularChainPresheafAmbientCap R X p q φ) := by
  apply NatTrans.ext
  funext U
  exact congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
    (relativeAmbientCapHom_boundary R (TopPair.ofSubset (U.unop : Set X)ᶜ) p q φ hφ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Sheafification preserves the exact signed differential compatibility. -/
lemma singularChainSheafAmbientCap_boundary
    (hφ : Simplicial.coboundary R p φ = 0) :
    singularChainSheafAmbientCap R X p (q + 1) φ ≫ singularChainSheafBoundary R X q =
      (-1 : ℤ) ^ p •
        (singularChainSheafBoundary R X (p + q) ≫ singularChainSheafAmbientCap R X p q φ) := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have h := congrArg F.map (singularChainPresheafAmbientCap_boundary R X p q φ hφ)
  simpa only [F, Functor.map_comp, Functor.map_zsmul,
    singularChainSheafAmbientCap, singularChainSheafBoundary] using h

end AlgebraicTopology.Singular
