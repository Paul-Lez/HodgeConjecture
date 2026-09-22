/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Other.AlgebraicGeometry.ComplexSupportedOrdinaryComparison
public import Other.AlgebraicGeometry.ExplicitSingularToHypercohomology

/-!
# Positive supported-kernel target for a supported singular class

The explicit singular-to-hypercohomology construction uses the positive literal relative
cochain inclusion.  This file records the comparison with the positive supported-injective
kernel model, so later cycle-component comparisons do not accidentally use the legacy cone sign.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance explicitSupportedPositiveAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance explicitSupportedPositiveOpenParacompact :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

local instance explicitSupportedPositiveHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency false in
theorem explicitPositive_globalSectionsIso_hom :
    (globalSectionsSingularCochainComplexIntIsoExtend X).hom =
      (HomologicalComplex.mapExtendCanonicalIso
        (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X)))
        (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
        ComplexShape.embeddingUpNat).hom := by
  let Y := TopCat.of (ComplexPoint X)
  let K := singularCochainSheafComplex ℚ Y
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : E.Additive := by dsimp [E]; infer_instance
  let q := ((Functor.mapHomologicalComplexCompIso
    (Iso.refl (F ⋙ E)) (ComplexShape.up ℕ)).inv.app K)
  let L := (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    E.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have hq : q = 𝟙 L := by ext n; rfl
  have hq' := congrArg
    (fun f ↦ HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) hq
  have hid : HomologicalComplex.extendMap (𝟙 L)
      ComplexShape.embeddingUpNat = 𝟙 (L.extend ComplexShape.embeddingUpNat) := by
    exact HomologicalComplex.extendMap_id L ComplexShape.embeddingUpNat
  rw [hid] at hq'
  change (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y)
      K ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap q ComplexShape.embeddingUpNat = _
  apply HomologicalComplex.Hom.ext
  funext n
  have hn := congrArg (fun f ↦ f.f n) hq'
  change _ ≫ (HomologicalComplex.extendMap q ComplexShape.embeddingUpNat).f n = _
  rw [hn]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
theorem explicitPositive_globalRawToSheaf_chain :
    globalRawToSingularSheafInt X ≫
      (globalSectionsSingularCochainComplexIntIsoExtend X).hom =
    HomologicalComplex.extendMap
      (topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat := by
  rw [explicitPositive_globalSectionsIso_hom]
  unfold globalRawToSingularSheafInt
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem rationalSingularCochainHypercohomologyAddEquivGlobalSections_of_globalRawClass
    (n : ℕ)
    (r : (globalRawSingularCochainComplex ℚ
      (TopCat.of (ComplexPoint X))).homology n) :
    rationalSingularCochainHypercohomologyAddEquivGlobalSections X (n : ℤ)
      ((rationalSingularCochainHypercohomologyAddEquivCohomology X n).symm
        (ordinarySingularCohomologyEquivCohomology ℚ
          (TopCat.of (ComplexPoint X)) n
          ((ordinarySingularCohomologyEquivGlobalRaw ℚ
            (TopCat.of (ComplexPoint X)) n).symm r))) =
      HomologicalComplex.homologyMap (globalRawToSingularSheafInt X) (n : ℤ)
        (((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).inv r) := by
  let Y := TopCat.of (ComplexPoint X)
  let G := rationalSingularCochainHypercohomologyAddEquivGlobalSections X (n : ℤ)
  let e :=
      (HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtend X) (n : ℤ)).addCommGroupIsoToAddEquiv |>.trans
      ((globalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X))).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).addCommGroupIsoToAddEquiv
  let q := (HereditarilyParacompact.rationalSingularCohomologyEquivGlobalSections Y n).symm
  let B := rationalSingularCochainHypercohomologyAddEquivCohomology X n
  let a := ordinarySingularCohomologyEquivCohomology ℚ Y n
    ((ordinarySingularCohomologyEquivGlobalRaw ℚ Y n).symm r)
  have hb := B.apply_symm_apply a
  have hb' : q (e (G (B.symm a))) = a := by
    change B (B.symm a) = a
    exact hb
  have hleft : e (G (B.symm a)) = q.symm a := by
    apply q.injective
    rw [q.apply_symm_apply]
    exact hb'
  change G (B.symm a) = _
  apply e.injective
  rw [hleft]
  have hqa : q.symm a =
      HomologicalComplex.homologyMap
        (topOpenToGlobalSingularCochainSheafComplex ℚ Y) n r := by
    dsimp [q, a,
      AlgebraicTopology.Singular.HereditarilyParacompact.rationalSingularCohomologyEquivGlobalSections,
      AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections]
    simp
  rw [hqa]
  let R := globalRawSingularCochainComplex ℚ Y
  let K := globalSingularCochainSheafComplex ℚ Y
  let rE := R.extendHomologyIso ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  let kE := K.extendHomologyIso ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  let iE := HomologicalComplex.homologyMapIso
    (globalSectionsSingularCochainComplexIntIsoExtend X) (n : ℤ)
  have hc := congrArg (fun f ↦ HomologicalComplex.homologyMap f (n : ℤ))
    (explicitPositive_globalRawToSheaf_chain X)
  rw [HomologicalComplex.homologyMap_comp] at hc
  have hcapp := ConcreteCategory.congr_hom hc (rE.inv r)
  have hcapp' : iE.hom
      (HomologicalComplex.homologyMap (globalRawToSingularSheafInt X) (n : ℤ)
        (rE.inv r)) =
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (topOpenToGlobalSingularCochainSheafComplex ℚ Y)
          ComplexShape.embeddingUpNat) (n : ℤ) (rE.inv r) := by
    change _ = _ at hcapp
    exact hcapp
  symm
  change kE.hom (iE.hom
      (HomologicalComplex.homologyMap (globalRawToSingularSheafInt X) (n : ℤ)
        (rE.inv r))) = _
  rw [hcapp']
  have hn := HomologicalComplex.extendHomologyIso_hom_naturality
    (topOpenToGlobalSingularCochainSheafComplex ℚ Y)
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have hnapp := ConcreteCategory.congr_hom hn (rE.inv r)
  simpa only [ConcreteCategory.comp_apply, R, K, rE, kE,
    Iso.inv_hom_id_apply] using hnapp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma localizedEquiv_equivOfIsKInjective_kInjectiveDerived
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [L.IsKInjective] (n : ℤ)
    (x : ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n) :
    Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
          (kInjectiveDerivedHomAddEquivCohomologyClass K L n x)) = x := by
  let e := kInjectiveDerivedHomAddEquivCohomologyClass K L n
  obtain ⟨z, hz⟩ := (e x).mk_surjective
  have hx : e.symm (CochainComplex.HomComplex.CohomologyClass.mk z) = x := by
    rw [hz, e.symm_apply_apply]
  change Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective (e x)) = x
  rw [← hz]
  change Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom
        (CochainComplex.HomComplex.CohomologyClass.mk z)) = x
  rw [CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk]
  rw [← kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk K L n z]
  exact hx

set_option maxHeartbeats 2000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The specialized rational Betti comparison for a fixed resolution agrees with the direct
K-injective comparison after applying the resolution map. -/
theorem rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution_map
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i)]
    (n : ℤ) (a : RationalSingularCochainHypercohomology X n) :
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) n
      (rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
        X I i n a) =
      hypercohomologyAddEquivGlobalSectionsKInjective X I n
        (hypercohomologyMap X i n a) := by
  let b := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) n
  dsimp only [rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution,
    hypercohomologyAddEquivGlobalSectionsKInjective,
    derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
  rw [hypercohomologyAddEquivDerived_naturality]
  simp only [isoHomCongrAddEquiv_apply, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.mapIso_hom]
  change b ((inv b) _) = _
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
  simp only [ConcreteCategory.id_apply]
  let A' := TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))
  let e3' : CochainComplex.HomComplex.CohomologyClass A' I n ≃
      Localization.SmallShiftedHom (analyticQuasiIsomorphisms X) A' I n :=
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
  let e3 := e3'.symm
  let e4 := (CochainComplex.HomComplex.homologyAddEquiv A' I n).symm
  let e5 := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
      (TopCat.of (ComplexPoint X)) I) n).addCommGroupIsoToAddEquiv
  change e5 (e4 (e3 _)) = e5 (e4 _)
  congr 1
  congr 1
  apply e3'.injective
  rw [e3'.apply_symm_apply]
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [localizedEquiv_equivOfIsKInjective_kInjectiveDerived]
  change Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
      ((Localization.SmallShiftedHom.precompEquiv
        (constantIntegerSheafComplexIntIsoSingle X).inv _)
        ((Localization.SmallShiftedHom.postcompEquiv i _) a)) = _
  rw [Localization.SmallShiftedHom.precompEquiv_apply,
    Localization.SmallShiftedHom.postcompEquiv_apply,
    Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀,
    Localization.SmallShiftedHom.equiv_mk₀]
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  rfl

set_option maxHeartbeats 2000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the specialized rational Betti comparison from a fixed resolution into an
arbitrary actual K-injective target. -/
theorem rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution_naturality_to_kInjective
    (I L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective] [L.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i)]
    (f : singularCochainSheafComplexInt X ℚ ⟶ L) (n : ℤ)
    (a : RationalSingularCochainHypercohomology X n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X L n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map f) n
        (rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
          X I i n a) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  obtain ⟨g, ⟨h⟩⟩ := CochainComplex.exists_homotopyLift_of_quasiIso_to_isKInjective i f
  have he : DerivedCategory.Q.map i ≫ DerivedCategory.Q.map g = DerivedCategory.Q.map f := by
    rw [← Functor.map_comp]
    exact DerivedCategory.Qh.congr_map (HomotopyCategory.eq_of_homotopy _ _ h)
  have ha : hypercohomologyMap X f n a =
      hypercohomologyMap X g n (hypercohomologyMap X i n a) := by
    apply (hypercohomologyAddEquivDerived X L n).injective
    simp only [hypercohomologyAddEquivDerived_naturality, Category.assoc,
      ← Functor.map_comp]
    rw [show DerivedCategory.Q.map (i ≫ g) = DerivedCategory.Q.map f from
      (DerivedCategory.Q.map_comp i g).trans he]
  rw [ha, hypercohomologyAddEquivGlobalSectionsKInjective_naturality,
    ← rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution_map]
  have hh := (Γ.mapHomotopy h).homologyMap_eq n
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh
    (rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i n a)

set_option maxHeartbeats 2000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical specialized rational Betti comparison is natural into an actual
K-injective target. -/
theorem rationalSingularCochainHypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    (L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [L.IsKInjective]
    (f : singularCochainSheafComplexInt X ℚ ⟶ L) (n : ℤ)
    (a : RationalSingularCochainHypercohomology X n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X L n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map f) n
        (rationalSingularCochainHypercohomologyAddEquivGlobalSections X n a) := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℚ
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 0
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE 0 := Classical.choose_spec hresiHi
  let : QuasiIso i := hi
  let : ∀ q : ℤ, Injective (I.X q) := hI
  let : I.IsStrictlyGE 0 := hIge
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  have hSflasque : ∀ q, (S.X q).IsFlasque :=
    fun q ↦ singularCochainSheafComplexInt_isFlasque X q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  let : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex ℤᵘᵖ).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact
    rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution_naturality_to_kInjective
      X I L i f n a

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/- The proof is intentionally left in terms of the positive kernel inclusion theorem. -/
theorem hypercohomologyClassOfSupportedSingularClass_eq_positiveKernel
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (z : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) S.compl ⊤
      (ambientRationalInjectiveComplex X)).X₁.homology (n : ℤ)) :
    hypercohomologyClassOfSupportedSingularClass X S n
        (relativeCohomologyMap ℚ n
          (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).inv
          (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n z)) =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ)).symm
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) S.compl ⊤
            (ambientRationalInjectiveComplex X)).f (n : ℤ) z) := by
  let q := complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n z
  let a := relativeCohomologyMap ℚ n
    (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).inv
    q
  let α := hypercohomologyClassOfSupportedSingularClass X S n a
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ)).injective
  rw [AddEquiv.apply_symm_apply]
  change rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ) α = _
  let I := ambientRationalInjectiveComplex X
  let f : singularCochainSheafComplexInt X ℚ ⟶ I :=
    complexSingularToAmbientInjective X
  let b := hypercohomologyMap X (rationalToSingularCochainComplexInt X) (n : ℤ) α
  have hnat :=
    rationalSingularCochainHypercohomologyAddEquivGlobalSections_naturality_to_kInjective
      X I f (n : ℤ) b
  have hcomp : hypercohomologyMap X f (n : ℤ) b =
      hypercohomologyMap X (ambientRationalInjectiveAugmentation X) (n : ℤ) α := by
    change hypercohomologyMap X f (n : ℤ)
      (hypercohomologyMap X (rationalToSingularCochainComplexInt X) (n : ℤ) α) = _
    rw [← hypercohomologyMap_comp_apply X]
    rw [rationalToSingular_comp_complexSingularToAmbientInjective]
  have hnat' :
      hypercohomologyAddEquivGlobalSectionsKInjective X I (n : ℤ)
        (hypercohomologyMap X (ambientRationalInjectiveAugmentation X) (n : ℤ) α) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map f) (n : ℤ)
        (rationalSingularCochainHypercohomologyAddEquivGlobalSections X (n : ℤ) b) := by
    rw [← hcomp]
    exact hnat
  change rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ) α = _ at hnat'
  rw [hnat']
  let B := rationalSingularCochainHypercohomologyAddEquivCohomology X n
  let c := singularClassOfSupportedSingularClass X S n a
  have hb : b = B.symm c := by
    apply B.injective
    rw [B.apply_symm_apply]
    change rationalCohomologyAddEquivSingularCohomology X n α = c
    exact rationalCohomologyLinearEquivSingularCohomology_hypercohomologyClassOfSupportedSingularClass
      X S n a
  have hraw := rationalSingularCochainHypercohomologyAddEquivGlobalSections_of_globalRawClass X n
    (globalRawClassOfSupportedSingularClass X S n a)
  have hglobal :
      rationalSingularCochainHypercohomologyAddEquivGlobalSections X (n : ℤ) b =
        HomologicalComplex.homologyMap (globalRawToSingularSheafInt X) (n : ℤ)
          (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X))
            (S : Set (ComplexPoint X))ᶜ n a) := by
    rw [hb]
    simpa only [B, c, singularClassOfSupportedSingularClass,
      globalRawClassOfSupportedSingularClass, Iso.hom_inv_id_apply] using hraw
  rw [hglobal]
  let g : TopCat.Sheaf.globalSectionsComplexInt
      (TopCat.of (ComplexPoint X)) (singularCochainSheafComplexInt X ℚ) ⟶
      TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveComplex X) :=
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map f)
  let u := globalRawToSingularSheafInt X
  let r := globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X))
    (S : Set (ComplexPoint X))ᶜ n a
  have hmap := HomologicalComplex.homologyMap_comp u g (n : ℤ)
  have hmapapp := ConcreteCategory.congr_hom hmap r
  rw [ConcreteCategory.comp_apply] at hmapapp
  have hleft :
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map f) (n : ℤ)
        (HomologicalComplex.homologyMap (globalRawToSingularSheafInt X) (n : ℤ)
          (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X))
            (S : Set (ComplexPoint X))ᶜ n a)) =
      HomologicalComplex.homologyMap (u ≫ g) (n : ℤ) r := by
    exact hmapapp.symm
  rw [hleft]
  have hpos := complexSupportInjectiveSectionCohomologyEquiv_inclusion_positive
    X S n a
  have hz :
      (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).symm
        (relativeCohomologyMap ℚ n
          (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).hom a) = z := by
    apply (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).injective
    simp only [AddEquiv.apply_symm_apply]
    dsimp only [a]
    change ((relativeCohomologyMap ℚ n
      (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).hom) ∘ₗ
      (relativeCohomologyMap ℚ n
        (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).inv)) _ = _
    rw [← relativeCohomologyMap_comp]
    simp [q]
  change HomologicalComplex.homologyMap (u ≫ g) (n : ℤ) r =
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) S.compl ⊤
        (ambientRationalInjectiveComplex X)).f (n : ℤ) z
  calc
    HomologicalComplex.homologyMap (u ≫ g) (n : ℤ) r =
        HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) S.compl ⊤
            (ambientRationalInjectiveComplex X)).f (n : ℤ)
          ((complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).symm
            (relativeCohomologyMap ℚ n
              (topOpenNeighborhoodSupportPairIso
                (TopCat.of (ComplexPoint X)) S).hom a)) := by
          symm
          dsimp only [u, g, r, f]
          exact hpos
    _ = _ := by rw [hz]

end AlgebraicGeometry.ComplexPoint
