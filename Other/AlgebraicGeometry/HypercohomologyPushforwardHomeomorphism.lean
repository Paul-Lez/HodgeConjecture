/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DerivedGlobalHypercohomologyComparison
public import Other.AlgebraicGeometry.HypercohomologyFlasqueNaturality
public import Other.AlgebraicTopology.SheafPushforwardHomeomorphism
public import Other.AlgebraicTopology.ClosedEmbeddingSheafExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Hypercohomology and direct image by a homeomorphism

Whole-space sections of a direct-image sheaf are definitionally the sections of the
original sheaf.  For a homeomorphism, direct image also preserves injectives and
quasi-isomorphisms.  We use the repository's fixed functorial injective models to
package the resulting canonical equivalence on hypercohomology and prove its
naturality in the coefficient complex.
-/

@[expose] public noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory Limits TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance hypercohomologyPushforwardHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- The pushed fixed injective model remains K-injective. -/
def pushforwardInjectiveModelData
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsStrictlyGE 0] :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
    (.up ℤ)).obj (globalHypercohomologyInjectiveComplex X K)

/-- Hypercohomology of a pushed complex, computed on the direct image of the
fixed injective model of the original complex.  Its target is definitionally the
same global-section homology used for the original complex. -/
def pushforwardHypercohomologyAddEquivInjectiveHomology
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsStrictlyGE 0] (n : ℤ) :
    Hypercohomology X
        (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
          (.up ℤ)).obj K) n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
          (globalHypercohomologyInjectiveComplex X K)).homology n := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat H.hom
  let I := globalHypercohomologyInjectiveComplex X K
  let i := globalHypercohomologyInjectiveMap X K
  let PI := pushforwardInjectiveModelData X H K
  let Pi := (P.mapHomologicalComplex (.up ℤ)).map i
  letI : P.IsEquivalence :=
    TopCat.Sheaf.pushforward_isEquivalence_of_iso AddCommGrpCat H
  letI : QuasiIso Pi := by
    exact @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso
      _ _ H.hom (TopCat.homeoOfIso H).isClosedEmbedding
      ℤ (.up ℤ) _ _ i inferInstance
  letI : ∀ q : ℤ, Injective (PI.X q) := by
    intro q
    change Injective (P.obj (I.X q))
    infer_instance
  letI : CochainComplex.IsStrictlyGE PI (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    change IsZero (P.obj (I.X q))
    exact Functor.map_isZero P (I.isZero_of_isStrictlyGE (-1) q hq)
  letI : CochainComplex.IsKInjective PI :=
    CochainComplex.isKInjective_of_injective PI (-1)
  let hPi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (.up ℤ) Pi := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let e : Hypercohomology X
        ((P.mapHomologicalComplex (.up ℤ)).obj K) n ≃+
      Hypercohomology X PI n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv Pi hPi
      map_add' := (hypercohomologyMap X Pi n).map_add }
  exact e.trans (hypercohomologyAddEquivGlobalSectionsKInjective X PI n)

/-- Canonical whole-space hypercohomology identification
`RΓ(f_*K) ≃ RΓ(K)` for a homeomorphism. -/
def hypercohomologyPushforwardAddEquivOfIso
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsStrictlyGE 0] (n : ℤ) :
    Hypercohomology X
        (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
          (.up ℤ)).obj K) n ≃+
      Hypercohomology X K n :=
  (pushforwardHypercohomologyAddEquivInjectiveHomology X H K n).trans
    (hypercohomologyAddEquivInjectiveHomology X K n).symm

private lemma pushforwardInjectiveMapMap_comp
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] (f : K ⟶ L) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).map (globalHypercohomologyInjectiveMap X K) ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).map (globalHypercohomologyInjectiveMapMap X f) =
    ((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).map f ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).map (globalHypercohomologyInjectiveMap X L) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    globalHypercohomologyInjectiveMap_comp_map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The pushed-injective computation is natural in the coefficient complex. -/
theorem pushforwardHypercohomologyAddEquivInjectiveHomology_naturality
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (f : K ⟶ L) (n : ℤ)
    (a : Hypercohomology X
      (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).obj K) n) :
    pushforwardHypercohomologyAddEquivInjectiveHomology X H L n
        (hypercohomologyMap X
          (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
            (.up ℤ)).map f) n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) n
        (pushforwardHypercohomologyAddEquivInjectiveHomology X H K n a) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat H.hom
  let iK := globalHypercohomologyInjectiveMap X K
  let iL := globalHypercohomologyInjectiveMap X L
  let g := globalHypercohomologyInjectiveMapMap X f
  let PI_K := pushforwardInjectiveModelData X H K
  let PI_L := pushforwardInjectiveModelData X H L
  let PiK := (P.mapHomologicalComplex (.up ℤ)).map iK
  let PiL := (P.mapHomologicalComplex (.up ℤ)).map iL
  let Pg := (P.mapHomologicalComplex (.up ℤ)).map g
  letI : P.IsEquivalence :=
    TopCat.Sheaf.pushforward_isEquivalence_of_iso AddCommGrpCat H
  letI : QuasiIso PiK := by
    exact @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso
      _ _ H.hom (TopCat.homeoOfIso H).isClosedEmbedding
      ℤ (.up ℤ) _ _ iK inferInstance
  letI : QuasiIso PiL := by
    exact @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso
      _ _ H.hom (TopCat.homeoOfIso H).isClosedEmbedding
      ℤ (.up ℤ) _ _ iL inferInstance
  letI : ∀ q : ℤ, Injective (PI_K.X q) := by
    intro q
    change Injective (P.obj ((globalHypercohomologyInjectiveComplex X K).X q))
    infer_instance
  letI : ∀ q : ℤ, Injective (PI_L.X q) := by
    intro q
    change Injective (P.obj ((globalHypercohomologyInjectiveComplex X L).X q))
    infer_instance
  letI : CochainComplex.IsStrictlyGE PI_K (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    change IsZero (P.obj ((globalHypercohomologyInjectiveComplex X K).X q))
    exact Functor.map_isZero P
      ((globalHypercohomologyInjectiveComplex X K).isZero_of_isStrictlyGE (-1) q hq)
  letI : CochainComplex.IsStrictlyGE PI_L (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    change IsZero (P.obj ((globalHypercohomologyInjectiveComplex X L).X q))
    exact Functor.map_isZero P
      ((globalHypercohomologyInjectiveComplex X L).isZero_of_isStrictlyGE (-1) q hq)
  letI : CochainComplex.IsKInjective PI_K :=
    CochainComplex.isKInjective_of_injective PI_K (-1)
  letI : CochainComplex.IsKInjective PI_L :=
    CochainComplex.isKInjective_of_injective PI_L (-1)
  change hypercohomologyAddEquivGlobalSectionsKInjective X PI_L n
      (hypercohomologyMap X PiL n
        (hypercohomologyMap X ((P.mapHomologicalComplex (.up ℤ)).map f) n a)) = _
  rw [← hypercohomologyMap_comp_apply,
    ← pushforwardInjectiveMapMap_comp X H f,
    hypercohomologyMap_comp_apply]
  exact hypercohomologyAddEquivGlobalSectionsKInjective_naturality
    X PI_K PI_L Pg n (hypercohomologyMap X PiK n a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical `RΓ(f_*-) ≃ RΓ(-)` identification is natural in maps of
nonnegative coefficient complexes. -/
theorem hypercohomologyPushforwardAddEquivOfIso_naturality
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (f : K ⟶ L) (n : ℤ)
    (a : Hypercohomology X
      (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).obj K) n) :
    hypercohomologyPushforwardAddEquivOfIso X H L n
        (hypercohomologyMap X
          (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
            (.up ℤ)).map f) n a) =
      hypercohomologyMap X f n
        (hypercohomologyPushforwardAddEquivOfIso X H K n a) := by
  apply (hypercohomologyAddEquivInjectiveHomology X L n).injective
  dsimp only [hypercohomologyPushforwardAddEquivOfIso, AddEquiv.trans_apply]
  rw [AddEquiv.apply_symm_apply]
  rw [pushforwardHypercohomologyAddEquivInjectiveHomology_naturality,
    hypercohomologyAddEquivInjectiveHomology_naturality,
    AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a bounded-below termwise-flasque complex, the canonical pushforward
identification is exactly the identity on the whole-space global-section
complex. -/
theorem hypercohomologyPushforwardAddEquivOfIso_globalSections
    (H : TopCat.of (ComplexPoint X) ≅ TopCat.of (ComplexPoint X))
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsStrictlyGE 0]
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℤ)
    (a : Hypercohomology X
      (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
        (.up ℤ)).obj K) n) :
    hypercohomologyAddEquivGlobalSections X K 0 hK n
        (hypercohomologyPushforwardAddEquivOfIso X H K n a) =
      hypercohomologyAddEquivGlobalSections X
        (((TopCat.Sheaf.pushforward AddCommGrpCat H.hom).mapHomologicalComplex
          (.up ℤ)).obj K) 0
        (fun q => TopCat.Sheaf.IsFlasque.pushforward_isFlasque
          (K.X q) H.hom) n a := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat H.hom
  let I := globalHypercohomologyInjectiveComplex X K
  let i := globalHypercohomologyInjectiveMap X K
  let PI := pushforwardInjectiveModelData X H K
  let Pi := (P.mapHomologicalComplex (.up ℤ)).map i
  let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  let Γi := (Γ.mapHomologicalComplex (.up ℤ)).map i
  let ΓPi := (Γ.mapHomologicalComplex (.up ℤ)).map Pi
  letI : P.IsEquivalence :=
    TopCat.Sheaf.pushforward_isEquivalence_of_iso AddCommGrpCat H
  letI : QuasiIso Pi := by
    exact @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso
      _ _ H.hom (TopCat.homeoOfIso H).isClosedEmbedding
      ℤ (.up ℤ) _ _ i inferInstance
  letI : ∀ q : ℤ, Injective (PI.X q) := by
    intro q
    change Injective (P.obj (I.X q))
    infer_instance
  letI : CochainComplex.IsStrictlyGE PI (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    change IsZero (P.obj (I.X q))
    exact Functor.map_isZero P (I.isZero_of_isStrictlyGE (-1) q hq)
  letI : CochainComplex.IsKInjective PI :=
    CochainComplex.isKInjective_of_injective PI (-1)
  letI : CochainComplex.IsStrictlyGE PK 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    change IsZero (P.obj (K.X q))
    exact Functor.map_isZero P (K.isZero_of_isStrictlyGE 0 q hq)
  let hPK : ∀ q, (PK.X q).IsFlasque := fun q =>
    TopCat.Sheaf.IsFlasque.pushforward_isFlasque (K.X q) H.hom
  have hI : ∀ q, (I.X q).IsFlasque := fun _ => inferInstance
  have hPI : ∀ q, (PI.X q).IsFlasque := fun _ => inferInstance
  letI : QuasiIso ΓPi :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      Pi 0 (-1) hPK hPI
  apply AddCommGrpCat.injective_of_mono
    (HomologicalComplex.homologyMap ΓPi n)
  have hs := hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    X K I 0 hK i n
      (hypercohomologyPushforwardAddEquivOfIso X H K n a)
  have ht := hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    X PK PI 0 hPK Pi n a
  have he :
      hypercohomologyAddEquivGlobalSectionsKInjective X PI n
          (hypercohomologyMap X Pi n a) =
        hypercohomologyAddEquivInjectiveHomology X K n
          (hypercohomologyPushforwardAddEquivOfIso X H K n a) := by
    dsimp only [hypercohomologyPushforwardAddEquivOfIso,
      pushforwardHypercohomologyAddEquivInjectiveHomology,
      AddEquiv.trans_apply]
    rw [AddEquiv.apply_symm_apply]
    rfl
  calc
    HomologicalComplex.homologyMap ΓPi n
        (hypercohomologyAddEquivGlobalSections X K 0 hK n
          (hypercohomologyPushforwardAddEquivOfIso X H K n a)) =
        hypercohomologyAddEquivGlobalSectionsKInjective X I n
          (hypercohomologyMap X i n
            (hypercohomologyPushforwardAddEquivOfIso X H K n a)) := by
      exact hs.symm
    _ = hypercohomologyAddEquivGlobalSectionsKInjective X PI n
          (hypercohomologyMap X Pi n a) := he.symm
    _ = HomologicalComplex.homologyMap ΓPi n
          (hypercohomologyAddEquivGlobalSections X PK 0 hPK n a) := ht

end AlgebraicGeometry.ComplexPoint
