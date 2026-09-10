/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiSupportSingularGlobalComparison
public import Other.AlgebraicGeometry.BettiSupportSingularComparison
public import Other.AlgebraicTopology.SingularCapNaturality
public import Other.AlgebraicTopology.SheafCohomologyWithSupport
public import Other.Algebra.Homology.MapExtend
public import Other.AlgebraicTopology.SingularChainSheafPushforward
public import Other.AlgebraicTopology.LinearDualHomologyNaturality

/-!
# Naturality of the singular-cochain comparison under continuous maps

Restriction of constant and singular-cochain sheaves commutes with their canonical
comparison.  On global raw cochains the resulting restriction is the ordinary
contravariant singular cochain map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular

universe u

variable (R : Type) [Field R] {U X : TopCat.{0}} (j : U ⟶ X)

set_option backward.isDefEq.respectTransparency false in
lemma constantsToSingularCochainZeroSheaf_naturality :
    constantsToSingularCochainZeroSheaf R X ≫
        singularRestrictionSheaf R j 0 =
      TopCat.Sheaf.constantRestriction j (AddCommGrpCat.of R) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat j).map
          (constantsToSingularCochainZeroSheaf R U) := by
  apply Sheaf.hom_ext
  change sheafifyMap (Opens.grothendieckTopology X)
        (constantsToSingularCochainZero R X) ≫
      (singularRestrictionSheaf R j 0).hom =
    (TopCat.Sheaf.constantRestriction j (AddCommGrpCat.of R)).hom ≫
      Functor.whiskerLeft (Opens.map j).op
        (sheafifyMap (Opens.grothendieckTopology U)
          (constantsToSingularCochainZero R U))
  apply sheafify_hom_ext
    (J := Opens.grothendieckTopology X)
    (P := constantCoefficientPresheaf R X) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
      (singularCochainSheaf R U 0)).property
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    toSheafify_comp_singularRestrictionSheaf]
  unfold singularRestrictionPresheaf
  rw [← Category.assoc,
    constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward]
  conv_rhs => rw [← Category.assoc]
  unfold constantCoefficientPresheaf
  rw [TopCat.Sheaf.toSheafify_constantRestriction]
  rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp]
  rw [toSheafify_naturality]

def constantCoefficientRestrictionComplex :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat X)).obj
        (constantCoefficientSheaf R X) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat U)).obj
          (constantCoefficientSheaf R U)) :=
  (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat X)).map
      (TopCat.Sheaf.constantRestriction j (AddCommGrpCat.of R)) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat j)
      (ComplexShape.up ℕ) 0).inv.app (constantCoefficientSheaf R U)

def constantCoefficientRestrictionComplexInt :
    ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat X)).obj
        (constantCoefficientSheaf R X)).extend ComplexShape.embeddingUpNat ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat U)).obj
          (constantCoefficientSheaf R U)).extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap
      (constantCoefficientRestrictionComplex R j)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat j)
      ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat U)).obj
        (constantCoefficientSheaf R U))
      ComplexShape.embeddingUpNat).inv

theorem constantsToSingularCochainSheafComplex_naturality :
    constantsToSingularCochainSheafComplex R X ≫
        singularRestrictionSheafComplex R j =
      constantCoefficientRestrictionComplex R j ≫
        (((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (constantsToSingularCochainSheafComplex R U)) := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · change constantsToSingularCochainZeroSheaf R X ≫
        singularRestrictionSheaf R j 0 =
      TopCat.Sheaf.constantRestriction j (AddCommGrpCat.of R) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat j).map
          (constantsToSingularCochainZeroSheaf R U)
    exact constantsToSingularCochainZeroSheaf_naturality R j
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (constantCoefficientSheaf R X) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

theorem constantsToSingularCochainSheafComplexInt_naturality :
    HomologicalComplex.extendMap
        (constantsToSingularCochainSheafComplex R X)
        ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.extendMap
        (singularRestrictionSheafComplex R j)
        ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapExtendCanonicalIso
          (TopCat.Sheaf.pushforward AddCommGrpCat j)
          (singularCochainSheafComplex R U)
          ComplexShape.embeddingUpNat).inv) =
      constantCoefficientRestrictionComplexInt R j ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap
              (constantsToSingularCochainSheafComplex R U)
              ComplexShape.embeddingUpNat) := by
  let F := TopCat.Sheaf.pushforward AddCommGrpCat j
  let L := singularCochainSheafComplex R U
  let E := ComplexShape.embeddingUpNat
  apply (cancel_mono
    (HomologicalComplex.mapExtendCanonicalIso F L E).hom).1
  dsimp only [constantCoefficientRestrictionComplexInt]
  simp only [F, L, E, Category.assoc]
  rw [HomologicalComplex.mapExtendCanonicalIso_naturality]
  simp only [Category.comp_id, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  rw [← HomologicalComplex.extendMap_comp,
    constantsToSingularCochainSheafComplex_naturality]
  rw [HomologicalComplex.extendMap_comp]

def globalRawPushforwardSingularCochainComplexIsoGlobal :
    globalRawPushforwardSingularCochainComplex R j ≅
      globalRawSingularCochainComplex R U :=
  Iso.refl _

def globalRawPushforwardSingularCochainComplexIsoMap :
    globalRawPushforwardSingularCochainComplex R j ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex R U).linearDualCochainComplex :=
  globalRawPushforwardSingularCochainComplexIsoGlobal R j ≪≫
    globalRawSingularCochainComplexIsoSingular R U

set_option backward.isDefEq.respectTransparency false in
lemma topOpenPreimageChainMap_transport_without_target :
    (topOpenSingularChainComplexIso R U).inv ≫
        preimageOpenChainMap R j (⊤ : Opens X) =
      ((singularChainComplexFunctor (ModuleCat R)).obj
          (ModuleCat.of R R)).map j ≫
        (topOpenSingularChainComplexIso R X).inv := by
  apply (cancel_mono (topOpenSingularChainComplexIso R X).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    topOpenPreimageChainMap_transport R X j

set_option backward.isDefEq.respectTransparency false in
lemma globalRawSingularRestriction_transport_map :
    globalRawSingularRestriction R j ≫
        (globalRawPushforwardSingularCochainComplexIsoMap R j).hom =
      (globalRawSingularCochainComplexIsoSingular R X).hom ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (HomologicalComplex.linearDualMap
              (((singularChainComplexFunctor (ModuleCat R)).obj
                (ModuleCat.of R R)).map j)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change OpenCochains R X (.op (⊤ : Opens X)) n at φ
  apply LinearMap.ext
  intro c
  let F := (singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)
  change φ
      (((((topOpenSingularChainComplexIso R U).inv ≫
        preimageOpenChainMap R j (⊤ : Opens X)).f n).hom) c) =
    φ (((((F.map j) ≫
      (topOpenSingularChainComplexIso R X).inv).f n).hom) c)
  exact congrArg φ (ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.f n)
      (topOpenPreimageChainMap_transport_without_target R j)) c)

set_option backward.isDefEq.respectTransparency false in
/-- The universal-coefficient comparison intertwines the map on the full
singular cochain complex with pullback in the repository's standard singular
cohomology. -/
lemma ordinarySingularCohomologyEquivCohomology_naturality
    (n : ℕ) (a : OrdinarySingularCohomology R X n) :
    ordinarySingularCohomologyEquivCohomology R U n
        (HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap
            (((singularChainComplexFunctor (ModuleCat R)).obj
              (ModuleCat.of R R)).map j)) n a) =
      cohomologyMap R n j
        (ordinarySingularCohomologyEquivCohomology R X n a) := by
  apply LinearMap.ext
  intro z
  exact HomologicalComplex.linearDualHomologyEquiv_naturality
    (((singularChainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)).map j) n a z

/-- Forgetting the scalar structure commutes with taking homology of the full
ordinary singular cochain complex. -/
def forgottenSingularCochainHomologyIso (Y : TopCat.{0}) (n : ℕ) :
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (SingularChainComplex R Y).linearDualCochainComplex).homology n ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((SingularChainComplex R Y).linearDualCochainComplex.homology n) :=
  ShortComplex.mapHomologyIso
    ((SingularChainComplex R Y).linearDualCochainComplex.sc n)
    (forget₂ (ModuleCat R) AddCommGrpCat)

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- After transport to the full ordinary singular cochain complex, the raw
global comparison is the canonical forgetful-functor homology comparison. -/
lemma ordinarySingularCohomologyEquivGlobalRaw_normalization
    (Y : TopCat.{0}) (n : ℕ) (a : OrdinarySingularCohomology R Y n) :
    HomologicalComplex.homologyMap
        (globalRawSingularCochainComplexIsoSingular R Y).hom n
        (ordinarySingularCohomologyEquivGlobalRaw R Y n a) =
      (forgottenSingularCochainHomologyIso R Y n).inv a := by
  simp [ordinarySingularCohomologyEquivGlobalRaw,
    globalRawSingularCochainComplexIsoSingular,
    forgottenSingularCochainHomologyIso,
    HomologicalComplex.homologyMap_comp]
  have hcancel (x : (topOpenForgottenSingularCochainComplex R Y).homology n) :
      HomologicalComplex.homologyMap
          (globalRawSingularCochainComplexIso R Y).hom n
          (HomologicalComplex.homologyMap
            (globalRawSingularCochainComplexIso R Y).inv n x) = x := by
    rw [← ConcreteCategory.comp_apply,
      ← HomologicalComplex.homologyMap_comp,
      Iso.inv_hom_id, HomologicalComplex.homologyMap_id]
    rfl
  rw [hcancel]
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    (F := forget₂ (ModuleCat R) AddCommGrpCat)
    (φ := ((HomologicalComplex.shortComplexFunctor
      (ModuleCat R) (ComplexShape.up ℕ) n).map
        (singularCochainComplexIsoTopOpen R Y).hom))
  have hna := ConcreteCategory.congr_hom hn a
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let K := (SingularChainComplex R Y).linearDualCochainComplex
  let T := (TopOpenSingularChainComplex R Y).linearDualCochainComplex
  let e := singularCochainComplexIsoTopOpen R Y
  have hna' :
      ((T.sc n).mapHomologyIso F).inv
          (F.map (HomologicalComplex.homologyMap e.hom n) a) =
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom) n
          (((K.sc n).mapHomologyIso F).inv a) := by
    exact hna
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.inv) n
      (((T.sc n).mapHomologyIso F).inv
        (F.map (HomologicalComplex.homologyMap e.hom n) a)) =
    ((K.sc n).mapHomologyIso F).inv a
  rw [hna']
  rw [← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp]
  simp

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison from ordinary singular cohomology to raw top-open cochains
is natural under every continuous map, with the inverse-image top open
transported explicitly to the source's raw global complex. -/
lemma ordinarySingularCohomologyEquivGlobalRaw_naturality
    (n : ℕ) (a : OrdinarySingularCohomology R X n) :
    ordinarySingularCohomologyEquivGlobalRaw R U n
        (HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap
            (((singularChainComplexFunctor (ModuleCat R)).obj
              (ModuleCat.of R R)).map j)) n a) =
      HomologicalComplex.homologyMap
        (globalRawSingularRestriction R j ≫
          (globalRawPushforwardSingularCochainComplexIsoGlobal R j).hom) n
        (ordinarySingularCohomologyEquivGlobalRaw R X n a) := by
  apply ((HomologicalComplex.homologyMapIso
    (globalRawSingularCochainComplexIsoSingular R U) n
    ).addCommGroupIsoToAddEquiv).injective
  change HomologicalComplex.homologyMap
      (globalRawSingularCochainComplexIsoSingular R U).hom n
        (ordinarySingularCohomologyEquivGlobalRaw R U n
          (HomologicalComplex.homologyMap
            (HomologicalComplex.linearDualMap
              (((singularChainComplexFunctor (ModuleCat R)).obj
                (ModuleCat.of R R)).map j)) n a)) =
    HomologicalComplex.homologyMap
      (globalRawSingularCochainComplexIsoSingular R U).hom n
        (HomologicalComplex.homologyMap
          (globalRawSingularRestriction R j ≫
            (globalRawPushforwardSingularCochainComplexIsoGlobal R j).hom) n
          (ordinarySingularCohomologyEquivGlobalRaw R X n a))
  rw [ordinarySingularCohomologyEquivGlobalRaw_normalization]
  rw [← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp]
  change _ = HomologicalComplex.homologyMap
    (globalRawSingularRestriction R j ≫
      (globalRawPushforwardSingularCochainComplexIsoMap R j).hom) n _
  rw [globalRawSingularRestriction_transport_map]
  rw [HomologicalComplex.homologyMap_comp]
  rw [ConcreteCategory.comp_apply]
  rw [ordinarySingularCohomologyEquivGlobalRaw_normalization]
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let K := (SingularChainComplex R X).linearDualCochainComplex
  let L := (SingularChainComplex R U).linearDualCochainComplex
  let g : K ⟶ L := HomologicalComplex.linearDualMap
    (((singularChainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)).map j)
  have hnat := ShortComplex.mapHomologyIso_inv_naturality
    (F := F)
    (φ := ((HomologicalComplex.shortComplexFunctor
      (ModuleCat R) (ComplexShape.up ℕ) n).map g))
  change (F.map (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor
          (ModuleCat R) (ComplexShape.up ℕ) n).map g)) ≫
      ((L.sc n).mapHomologyIso F).inv) a =
    (((K.sc n).mapHomologyIso F).inv ≫
      ShortComplex.homologyMap
        (F.mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor
            (ModuleCat R) (ComplexShape.up ℕ) n).map g))) a
  exact ConcreteCategory.congr_hom hnat a

/-- Global sections of the pushed singular-cochain sheaf complex are the
global sections on the source space.  This explicit identity is kept as an
isomorphism to avoid unfolding the colimit presentation of sheafification. -/
def globalPushforwardSingularCochainSheafComplexIsoGlobal :
    globalPushforwardSingularCochainSheafComplex R j ≅
      globalSingularCochainSheafComplex R U :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- The pushed sheafification unit becomes the ordinary top-open
sheafification unit after the explicit global-section transports. -/
lemma globalRawPushforwardToSingularSheaf_transport :
    (globalRawPushforwardSingularCochainComplexIsoGlobal R j).hom ≫
        topOpenToGlobalSingularCochainSheafComplex R U =
      globalRawPushforwardToSingularSheaf R j ≫
        (globalPushforwardSingularCochainSheafComplexIsoGlobal R j).hom := by
  apply HomologicalComplex.Hom.ext
  funext m
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

/-- Ordinary singular cohomology computed by global sections of the
singular-cochain sheaf, assuming that the global sheafification map is a
quasi-isomorphism. -/
def ordinarySingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) (n : ℕ)
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R Y)] :
    OrdinarySingularCohomology R Y n ≃+
      (globalSingularCochainSheafComplex R Y).homology n :=
  (ordinarySingularCohomologyEquivGlobalRaw R Y n).trans
    ((asIso (HomologicalComplex.homologyMap
      (topOpenToGlobalSingularCochainSheafComplex R Y) n)
      ).addCommGroupIsoToAddEquiv)

/-- The repository's singular cohomology, computed by global sections of the
singular-cochain sheaf resolution. -/
def singularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) (n : ℕ)
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R Y)] :
    Cohomology R Y n ≃+
      (globalSingularCochainSheafComplex R Y).homology n :=
  (ordinarySingularCohomologyEquivCohomology R Y n).symm.toAddEquiv.trans
    (ordinarySingularCohomologyEquivGlobalSections R Y n)

set_option backward.isDefEq.respectTransparency false in
/-- The global-section realization of ordinary singular cohomology is
natural under every continuous map. -/
lemma ordinarySingularCohomologyEquivGlobalSections_naturality
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R X)]
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R U)]
    (n : ℕ) (a : OrdinarySingularCohomology R X n) :
    ordinarySingularCohomologyEquivGlobalSections R U n
        (HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap
            (((singularChainComplexFunctor (ModuleCat R)).obj
              (ModuleCat.of R R)).map j)) n a) =
      HomologicalComplex.homologyMap
        (globalSingularSheafRestriction R j ≫
          (globalPushforwardSingularCochainSheafComplexIsoGlobal R j).hom) n
        (ordinarySingularCohomologyEquivGlobalSections R X n a) := by
  change HomologicalComplex.homologyMap
      (topOpenToGlobalSingularCochainSheafComplex R U) n
        (ordinarySingularCohomologyEquivGlobalRaw R U n
          (HomologicalComplex.homologyMap
            (HomologicalComplex.linearDualMap
              (((singularChainComplexFunctor (ModuleCat R)).obj
                (ModuleCat.of R R)).map j)) n a)) = _
  rw [ordinarySingularCohomologyEquivGlobalRaw_naturality]
  rw [← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp]
  rw [Category.assoc,
    globalRawPushforwardToSingularSheaf_transport]
  rw [← Category.assoc,
    ← globalSingularSheafRestriction_naturality]
  simp [ordinarySingularCohomologyEquivGlobalSections,
    HomologicalComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The global-section realization of the repository's singular cohomology is
natural under every continuous map. -/
lemma singularCohomologyEquivGlobalSections_naturality
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R X)]
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R U)]
    (n : ℕ) (a : Cohomology R X n) :
    singularCohomologyEquivGlobalSections R U n
        (cohomologyMap R n j a) =
      HomologicalComplex.homologyMap
        (globalSingularSheafRestriction R j ≫
          (globalPushforwardSingularCochainSheafComplexIsoGlobal R j).hom) n
        (singularCohomologyEquivGlobalSections R X n a) := by
  let a₀ := (ordinarySingularCohomologyEquivCohomology R X n).symm a
  have hpre :
      HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap
            (((singularChainComplexFunctor (ModuleCat R)).obj
              (ModuleCat.of R R)).map j)) n a₀ =
        (ordinarySingularCohomologyEquivCohomology R U n).symm
          (cohomologyMap R n j a) := by
    apply (ordinarySingularCohomologyEquivCohomology R U n).injective
    rw [ordinarySingularCohomologyEquivCohomology_naturality]
    simp [a₀]
  change ordinarySingularCohomologyEquivGlobalSections R U n
      ((ordinarySingularCohomologyEquivCohomology R U n).symm
        (cohomologyMap R n j a)) = _
  rw [← hpre]
  exact ordinarySingularCohomologyEquivGlobalSections_naturality R j n a₀

end AlgebraicTopology.Singular
