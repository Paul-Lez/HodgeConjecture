import Other.AlgebraicGeometry.BettiSupportSingularGlobalComparison
import Other.AlgebraicGeometry.BettiSupportSingularComparison
import Other.AlgebraicTopology.SingularCapNaturality
import Other.AlgebraicTopology.SheafCohomologyWithSupport
import Other.Algebra.Homology.MapExtend
import Other.AlgebraicTopology.SingularChainSheafPushforward
import Other.AlgebraicTopology.LinearDualHomologyNaturality

@[expose] noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular

universe u

variable (R : Type) [Field R] {U X : TopCat.{0}} (j : U ⟶ X)

set_option backward.isDefEq.respectTransparency false in
lemma checkConstantsToSingularCochainZeroSheaf_naturality :
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

def checkConstantCoefficientRestrictionComplex :
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

def checkConstantCoefficientRestrictionComplexInt :
    ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat X)).obj
        (constantCoefficientSheaf R X)).extend ComplexShape.embeddingUpNat ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat U)).obj
          (constantCoefficientSheaf R U)).extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap
      (checkConstantCoefficientRestrictionComplex R j)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat j)
      ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat U)).obj
        (constantCoefficientSheaf R U))
      ComplexShape.embeddingUpNat).inv

theorem checkConstantsToSingularCochainSheafComplex_naturality :
    constantsToSingularCochainSheafComplex R X ≫
        singularRestrictionSheafComplex R j =
      checkConstantCoefficientRestrictionComplex R j ≫
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
    exact checkConstantsToSingularCochainZeroSheaf_naturality R j
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (constantCoefficientSheaf R X) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

theorem checkConstantsToSingularCochainSheafComplexInt_naturality :
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
      checkConstantCoefficientRestrictionComplexInt R j ≫
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
  dsimp only [checkConstantCoefficientRestrictionComplexInt]
  simp only [F, L, E, Category.assoc]
  rw [HomologicalComplex.mapExtendCanonicalIso_naturality]
  simp only [Category.comp_id, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  rw [← HomologicalComplex.extendMap_comp,
    checkConstantsToSingularCochainSheafComplex_naturality]
  rw [HomologicalComplex.extendMap_comp]

def checkGlobalRawPushforwardSingularCochainComplexIsoGlobal :
    globalRawPushforwardSingularCochainComplex R j ≅
      globalRawSingularCochainComplex R U :=
  Iso.refl _

def checkGlobalRawPushforwardSingularCochainComplexIsoSingular :
    globalRawPushforwardSingularCochainComplex R j ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex R U).linearDualCochainComplex :=
  checkGlobalRawPushforwardSingularCochainComplexIsoGlobal R j ≪≫
    globalRawSingularCochainComplexIsoSingular R U

set_option backward.isDefEq.respectTransparency false in
lemma checkTopOpenChainMap_transport :
    (topOpenSingularChainComplexIso R U).inv ≫
        preimageOpenChainMap R j (⊤ : Opens X) =
      ((singularChainComplexFunctor (ModuleCat R)).obj
          (ModuleCat.of R R)).map j ≫
        (topOpenSingularChainComplexIso R X).inv := by
  apply (cancel_mono (topOpenSingularChainComplexIso R X).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    topOpenPreimageChainMap_transport R X j

set_option backward.isDefEq.respectTransparency false in
lemma checkGlobalRawSingularRestriction_transport :
    globalRawSingularRestriction R j ≫
        (checkGlobalRawPushforwardSingularCochainComplexIsoSingular R j).hom =
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
    (congrArg (fun f ↦ f.f n) (checkTopOpenChainMap_transport R j)) c)

set_option backward.isDefEq.respectTransparency false in
lemma checkOrdinarySingularCohomologyEquivCohomology_naturality
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

def checkForgottenSingularCochainHomologyIso (Y : TopCat.{0}) (n : ℕ) :
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
lemma checkOrdinarySingularCohomologyEquivGlobalRaw_normalization
    (Y : TopCat.{0}) (n : ℕ) (a : OrdinarySingularCohomology R Y n) :
    HomologicalComplex.homologyMap
        (globalRawSingularCochainComplexIsoSingular R Y).hom n
        (ordinarySingularCohomologyEquivGlobalRaw R Y n a) =
      (checkForgottenSingularCochainHomologyIso R Y n).inv a := by
  simp [ordinarySingularCohomologyEquivGlobalRaw,
    globalRawSingularCochainComplexIsoSingular,
    checkForgottenSingularCochainHomologyIso,
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
lemma checkOrdinarySingularCohomologyEquivGlobalRaw_naturality
    (n : ℕ) (a : OrdinarySingularCohomology R X n) :
    ordinarySingularCohomologyEquivGlobalRaw R U n
        (HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap
            (((singularChainComplexFunctor (ModuleCat R)).obj
              (ModuleCat.of R R)).map j)) n a) =
      HomologicalComplex.homologyMap
        (globalRawSingularRestriction R j ≫
          (checkGlobalRawPushforwardSingularCochainComplexIsoGlobal R j).hom) n
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
            (checkGlobalRawPushforwardSingularCochainComplexIsoGlobal R j).hom) n
          (ordinarySingularCohomologyEquivGlobalRaw R X n a))
  rw [checkOrdinarySingularCohomologyEquivGlobalRaw_normalization]
  rw [← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp]
  change _ = HomologicalComplex.homologyMap
    (globalRawSingularRestriction R j ≫
      (checkGlobalRawPushforwardSingularCochainComplexIsoSingular R j).hom) n _
  rw [checkGlobalRawSingularRestriction_transport]
  rw [HomologicalComplex.homologyMap_comp]
  rw [ConcreteCategory.comp_apply]
  rw [checkOrdinarySingularCohomologyEquivGlobalRaw_normalization]
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

def checkOrdinarySingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) (n : ℕ)
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R Y)] :
    OrdinarySingularCohomology R Y n ≃+
      (globalSingularCochainSheafComplex R Y).homology n :=
  (ordinarySingularCohomologyEquivGlobalRaw R Y n).trans
    ((asIso (HomologicalComplex.homologyMap
      (topOpenToGlobalSingularCochainSheafComplex R Y) n)
      ).addCommGroupIsoToAddEquiv)

set_option backward.isDefEq.respectTransparency false in
lemma checkGlobalRawPushforwardToSingularSheaf_eq_topOpen :
    globalRawPushforwardToSingularSheaf R j =
      topOpenToGlobalSingularCochainSheafComplex R U := by
  apply HomologicalComplex.Hom.ext
  funext m
  rw [topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma checkOrdinarySingularCohomologyEquivGlobalSections_naturality
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R X)]
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R U)]
    (n : ℕ) (a : OrdinarySingularCohomology R X n) :
    checkOrdinarySingularCohomologyEquivGlobalSections R U n
        (HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap
            (((singularChainComplexFunctor (ModuleCat R)).obj
              (ModuleCat.of R R)).map j)) n a) =
      HomologicalComplex.homologyMap
        (globalSingularSheafRestriction R j) n
        (checkOrdinarySingularCohomologyEquivGlobalSections R X n a) := by
  change HomologicalComplex.homologyMap
      (topOpenToGlobalSingularCochainSheafComplex R U) n
        (ordinarySingularCohomologyEquivGlobalRaw R U n
          (HomologicalComplex.homologyMap
            (HomologicalComplex.linearDualMap
              (((singularChainComplexFunctor (ModuleCat R)).obj
                (ModuleCat.of R R)).map j)) n a)) = _
  rw [checkOrdinarySingularCohomologyEquivGlobalRaw_naturality]
  rw [← checkGlobalRawPushforwardToSingularSheaf_eq_topOpen R j]
  rw [← HomologicalComplex.homologyMap_comp]
  rw [← globalSingularSheafRestriction_naturality]
  rw [HomologicalComplex.homologyMap_comp]

end AlgebraicTopology.Singular
