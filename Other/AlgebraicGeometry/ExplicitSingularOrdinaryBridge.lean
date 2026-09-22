import Other.AlgebraicGeometry.ExplicitSingularToHypercohomology
import Other.AlgebraicTopology.RelativeCochainConeForgetComparison

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {S : ShortComplex C} (F : C ⥤ D) [F.Additive]
  [S.HasHomology] [(S.map F).HasHomology]
  [F.PreservesLeftHomologyOf S]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma mapHomologyπ_mapHomologyIso_hom
    (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
    [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq F,
    S.leftHomologyData.mapCyclesIso_eq F]
  dsimp only [Iso.trans_hom]
  rw [← Category.assoc]
  rw [S.leftHomologyData.map F |>.homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc]
  dsimp only [Functor.mapIso, Iso.symm_hom]
  rw [S.leftHomologyData.map_π]
  simp only [← F.map_comp]
  rw [S.leftHomologyData.π_comp_homologyIso_inv]

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom]
  [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
lemma ordinarySingularCohomologyEquivGlobalRaw_normalized
    (R : Type) [Field R] (Y : TopCat.{0}) (n : ℕ)
    (q : AlgebraicTopology.Singular.OrdinarySingularCohomology R Y n) :
    AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw R Y n q =
      ((HomologicalComplex.homologyMapIso
        (AlgebraicTopology.Singular.globalRawSingularCochainComplexIsoSingular R Y) n).inv)
        ((((AlgebraicTopology.Singular.SingularChainComplex R Y).linearDualCochainComplex.sc n).mapHomologyIso
          (forget₂ (ModuleCat R) AddCommGrpCat)).inv.hom q) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let K := AlgebraicTopology.Singular.SingularChainComplex R Y
  let qF : F.obj ((K.linearDualCochainComplex.sc n).homology) := q
  let φsc := (HomologicalComplex.shortComplexFunctor (ModuleCat R)
    (ComplexShape.up ℕ) n).map
      (AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen R Y).hom
  have hn := ShortComplex.mapHomologyIso_inv_naturality φsc F
  have hnq := ConcreteCategory.congr_hom hn qF
  simp only [ConcreteCategory.comp_apply] at hnq
  let g := AlgebraicTopology.Singular.globalRawSingularCochainComplexIso R Y
  have hmap := congrArg
    (fun z => (HomologicalComplex.homologyMap g.inv n).hom z) hnq
  dsimp [AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw]
  let eTop := AlgebraicTopology.Singular.topOpenForgottenSingularCochainHomologyIso R Y n
  let hTop := HomologicalComplex.homologyMapIso
    (AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen R Y) n
  let eTopShort :=
    ((AlgebraicTopology.Singular.TopOpenSingularChainComplex R Y).linearDualCochainComplex.sc n).mapHomologyIso F
  have hleft :
      eTop.symm.addCommGroupIsoToAddEquiv
          ((F.mapIso hTop).addCommGroupIsoToAddEquiv q) =
        eTopShort.inv.hom
          ((F.map (ShortComplex.homologyMap φsc)).hom qF) := by
    rfl
  let eK := (K.linearDualCochainComplex.sc n).mapHomologyIso F
  have hright :
      (HomologicalComplex.homologyMapIso
        (AlgebraicTopology.Singular.globalRawSingularCochainComplexIsoSingular R Y) n).inv
          (eK.inv.hom q) =
        (HomologicalComplex.homologyMap g.inv n).hom
          ((ShortComplex.homologyMap (F.mapShortComplex.map φsc)).hom
            (eK.inv.hom qF)) := by
    dsimp [AlgebraicTopology.Singular.globalRawSingularCochainComplexIsoSingular,
      eK, g]
    change
      (HomologicalComplex.homologyMap
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen R Y).hom) ≫
          (AlgebraicTopology.Singular.globalRawSingularCochainComplexIso R Y).inv) n).hom
          (eK.inv.hom q) = _
    rw [HomologicalComplex.homologyMap_comp]
    rfl
  change
    (HomologicalComplex.homologyMapIso g n).symm.addCommGroupIsoToAddEquiv
        (eTop.symm.addCommGroupIsoToAddEquiv
          ((F.mapIso hTop).addCommGroupIsoToAddEquiv q)) =
      (HomologicalComplex.homologyMapIso
        (AlgebraicTopology.Singular.globalRawSingularCochainComplexIsoSingular R Y) n).inv
        (eK.inv.hom qF)
  rw [hleft, hright]
  exact hmap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma singularClassOfSupportedSingularClass_eq_forgetSupport
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    singularClassOfSupportedSingularClass X Z n a =
      AlgebraicTopology.Singular.forgetSupport ℚ (TopCat.of (ComplexPoint X)) Z n a := by
  apply (ordinarySingularCohomologyEquivCohomology ℚ
    (TopCat.of (ComplexPoint X)) n).symm.injective
  dsimp [singularClassOfSupportedSingularClass]
  rw [LinearEquiv.symm_apply_apply]
  apply (ordinarySingularCohomologyEquivGlobalRaw ℚ
    (TopCat.of (ComplexPoint X)) n).injective
  rw [AddEquiv.apply_symm_apply]
  let P : TopPair := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) Zᶜ
  let b := (relativeDualCochainCohomologyEquiv ℚ P n).symm a
  let c := (relativeDualCochainHomologyIsoCone ℚ P n).hom b
  have hcanon :
      relativeCochainConeCohomologyEquivCanonical ℚ P n c = a := by
    dsimp [c, b, relativeCochainConeCohomologyEquivCanonical]
    simp
  have habs := relativeCochainConeCohomologyEquivCanonical_toAbsolute
    ℚ P n c
  rw [hcanon] at habs
  let u := (HomologicalComplex.extendHomologyIso
    (relativeDualCochainShortComplexNat ℚ P).X₂
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom.hom
  let f := (HomologicalComplex.homologyMap
    (relativeDualCochainShortComplexInt ℚ P).f (n : ℤ)).hom
  let v := (relativeDualCochainHomologyIsoCone ℚ P n).inv.hom c
  let eX2 := ((relativeDualCochainShortComplexInt ℚ P).X₂.sc (n : ℤ)).mapHomologyIso
    (forget₂ (ModuleCat ℚ) AddCommGrpCat)
  have habs' :
      (HomologicalComplex.linearDualHomologyEquiv
        (SingularChainComplex ℚ P.fst) n)
          (u (f v)) =
      relativeCohomologyToAbsolute ℚ P n a := by
    simpa [u, f, v] using habs
  change _ =
    (ordinarySingularCohomologyEquivGlobalRaw ℚ
      (TopCat.of (ComplexPoint X)) n)
      ((ordinarySingularCohomologyEquivCohomology ℚ
        (TopCat.of (ComplexPoint X)) n).symm
        (relativeCohomologyToAbsolute ℚ P n a))
  have hrawIso :
      (HomologicalComplex.homologyMap
        (globalRawSingularCochainComplexIntIsoRelative ℚ
          (TopCat.of (ComplexPoint X))).hom (n : ℤ)).hom
      (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X)) Zᶜ n a) =
      (((relativeDualCochainShortComplexInt ℚ P).X₂.sc (n : ℤ)).mapHomologyIso
          (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv
        (HomologicalComplex.homologyMap
          (relativeDualCochainShortComplexInt ℚ P).f (n : ℤ) v) := by
    let e := HomologicalComplex.homologyMapIso
      (globalRawSingularCochainComplexIntIsoRelative ℚ
        (TopCat.of (ComplexPoint X))) (n : ℤ)
    let q := (((relativeDualCochainShortComplexInt ℚ P).X₂.sc (n : ℤ)).mapHomologyIso
      (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv
        (HomologicalComplex.homologyMap
          (relativeDualCochainShortComplexInt ℚ P).f (n : ℤ) v)
    have hv : v = (relativeDualCochainCohomologyEquiv ℚ P n).symm a := by
      dsimp [v, c, b]
      simp
    have h := e.inv_hom_id_apply q
    simpa only [globalRawRelativeCochainClass, P, e, q, v,
      hv,
      HomologicalComplex.homologyMapIso_hom,
      HomologicalComplex.homologyMapIso_inv] using h
  let Y := TopCat.of (ComplexPoint X)
  let K := (SingularChainComplex ℚ Y).linearDualCochainComplex
  let qInt : (K.extend ComplexShape.embeddingUpNat).homology (n : ℤ) := by
    change (relativeDualCochainShortComplexInt ℚ P).X₂.homology (n : ℤ)
    exact f v
  let kE :
      ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).homology ≅
        (K.sc n).homology := by
    exact K.extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl
  let qNat : K.homology n := kE.hom qInt
  have hqInt : qInt = f v := by
    rfl
  have hqNat : qNat = u (f v) := by
    change (K.extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl).hom qInt = _
    rfl
  have habsY :
      (HomologicalComplex.linearDualHomologyEquiv
        (SingularChainComplex ℚ Y) n) (u (f v)) =
      relativeCohomologyToAbsolute ℚ P n a := by
    change (HomologicalComplex.linearDualHomologyEquiv
        (SingularChainComplex ℚ Y) n) (u (f v)) =
      relativeCohomologyToAbsolute ℚ P n a at habs'
    exact habs'
  rw [← habsY, show u (f v) = qNat from hqNat.symm]
  have huc :
      (ordinarySingularCohomologyEquivCohomology ℚ
        Y n).symm
        (HomologicalComplex.linearDualHomologyEquiv
          (SingularChainComplex ℚ Y) n qNat) =
      qNat := by
    change (ordinarySingularCohomologyEquivCohomology ℚ Y n).symm
      ((ordinarySingularCohomologyEquivCohomology ℚ Y n) qNat) = qNat
    exact (ordinarySingularCohomologyEquivCohomology ℚ Y n).symm_apply_apply qNat
  rw [huc]
  change AlgebraicTopology.Singular.OrdinarySingularCohomology ℚ
      (TopCat.of (ComplexPoint X)) n at qNat
  have hnorm := ordinarySingularCohomologyEquivGlobalRaw_normalized
    ℚ (TopCat.of (ComplexPoint X)) n qNat
  rw [hnorm]
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let scExt :
      ((F.mapHomologicalComplex ℤᵘᵖ).obj (K.extend ComplexShape.embeddingUpNat)).sc (n : ℤ) ≅
        ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).map F :=
    by
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · rfl
      · rfl
  let can := HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat
  let fkE :
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).sc (n : ℤ)).homology ≅
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).homology := by
    exact ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let eNat := (K.sc n).mapHomologyIso F
  let eInt := ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapHomologyIso F
  let scExtH := ShortComplex.homologyMapIso scExt
  let psi :
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
          ComplexShape.embeddingUpNat).sc (n : ℤ) ⟶
        ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).map F :=
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat
      ℤᵘᵖ (n : ℤ)).map
        (HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat).inv) ≫
      scExt.hom
  have hpsi :
      ShortComplex.homologyMap psi =
        HomologicalComplex.homologyMap can.inv (n : ℤ) ≫ scExtH.hom := by
    change ShortComplex.homologyMap
        (((HomologicalComplex.shortComplexFunctor AddCommGrpCat
          ℤᵘᵖ (n : ℤ)).map can.inv) ≫ scExt.hom) =
      ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor AddCommGrpCat
            ℤᵘᵖ (n : ℤ)).map can.inv) ≫
        ShortComplex.homologyMap scExt.hom
    rw [ShortComplex.homologyMap_comp]
  have hnj : ComplexShape.embeddingUpNat.f n = (n : ℤ) := by rfl
  have hcanX :
      can.inv.f (n : ℤ) ≫ F.map (K.extendXIso ComplexShape.embeddingUpNat hnj).hom =
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat hnj).hom := by
    apply (cancel_epi (can.hom.f (n : ℤ))).1
    have hcanId : can.hom.f (n : ℤ) ≫ can.inv.f (n : ℤ) = 𝟙 _ :=
      congrArg (fun z => z.f (n : ℤ)) can.hom_inv_id
    rw [← Category.assoc, hcanId, Category.id_comp]
    rw [HomologicalComplex.mapExtendCanonicalIso_hom_f F K ComplexShape.embeddingUpNat hnj]
    simp
  let qIntF : F.obj ((K.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) := qInt
  have hsq_mor :
      HomologicalComplex.homologyMap can.inv (n : ℤ) ≫ scExtH.hom ≫ eInt.hom ≫
          F.map kE.hom = fkE.hom ≫ eNat.hom := by
    rw [← Category.assoc, ← hpsi]
    apply (cancel_epi
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).homologyπ (n : ℤ))).1
    change
      ShortComplex.homologyπ
          ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
            ComplexShape.embeddingUpNat).sc (n : ℤ)) ≫
          ShortComplex.homologyMap psi ≫ eInt.hom ≫ F.map kE.hom =
        ShortComplex.homologyπ
            ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
              ComplexShape.embeddingUpNat).sc (n : ℤ)) ≫
          fkE.hom ≫ eNat.hom
    rw [ShortComplex.homologyπ_naturality_assoc]
    have hmapπ := CategoryTheory.ShortComplex.mapHomologyπ_mapHomologyIso_hom
      ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)) F
    dsimp only [eInt]
    have hmapπ' :
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).map F).homologyπ ≫
            (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapHomologyIso F).hom ≫
          F.map kE.hom =
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapCyclesIso F).hom ≫
            F.map ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).homologyπ ≫
            F.map kE.hom := by
      rw [← Category.assoc, hmapπ, Category.assoc]
    have hcycles :
        ShortComplex.cyclesMap psi ≫
          (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapCyclesIso F).hom ≫
          F.map (K.extendCyclesIso ComplexShape.embeddingUpNat hnj).hom =
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendCyclesIso
            ComplexShape.embeddingUpNat hnj).hom ≫
          ((K.sc n).mapCyclesIso F).hom := by
      apply (cancel_mono (F.map (K.iCycles n))).1
      simp only [Category.assoc, ← F.map_comp]
      rw [HomologicalComplex.extendCyclesIso_hom_iCycles]
      rw [F.map_comp]
      dsimp only [HomologicalComplex.iCycles]
      rw [ShortComplex.mapCyclesIso_hom_iCycles_assoc]
      rw [← Category.assoc, ShortComplex.cyclesMap_i]
      have hpsi₂ : psi.τ₂ = can.inv.f (n : ℤ) := by
        rfl
      rw [hpsi₂]
      rw [Category.assoc, hcanX]
      rw [ShortComplex.mapCyclesIso_hom_iCycles]
      have hExt :=
        HomologicalComplex.extendCyclesIso_hom_iCycles
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
          ComplexShape.embeddingUpNat hnj
      change _ = _ ≫ (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n)
      exact hExt.symm
    rw [hmapπ']
    rw [← F.map_comp]
    dsimp only [kE]
    have hKπ := K.homologyπ_extendHomologyIso_hom
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) hnj
    have hKπ' :
        ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).homologyπ ≫ kE.hom =
          (K.extendCyclesIso ComplexShape.embeddingUpNat hnj).hom ≫ K.homologyπ n := by
      change (K.extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ) ≫ kE.hom = _
      dsimp only [kE]
      exact hKπ
    rw [hKπ']
    rw [F.map_comp]
    have hcycles' :
        ShortComplex.cyclesMap psi ≫
            (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapCyclesIso F).hom ≫
          F.map (K.extendCyclesIso ComplexShape.embeddingUpNat hnj).hom =
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendCyclesIso
            ComplexShape.embeddingUpNat hnj).hom ≫
          ((K.sc n).mapCyclesIso F).hom := by
      simpa only [Category.assoc, HomologicalComplex.cycles] using hcycles
    have hcyclesLeft := hcycles'
    simp only [← Category.assoc] at hcyclesLeft ⊢
    rw [hcyclesLeft]
    have hFKπ := HomologicalComplex.homologyπ_extendHomologyIso_hom
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) hnj
    have hFKπ' :
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
          ComplexShape.embeddingUpNat).sc (n : ℤ)).homologyπ ≫ fkE.hom =
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendCyclesIso
            ComplexShape.embeddingUpNat hnj).hom ≫
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n := by
      change (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
          ComplexShape.embeddingUpNat).homologyπ (n : ℤ) ≫ fkE.hom = _
      dsimp only [fkE]
      exact hFKπ
    rw [hFKπ']
    have hmapπNat := CategoryTheory.ShortComplex.mapHomologyπ_mapHomologyIso_hom
      (K.sc n) F
    have hmapπNat' :
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n ≫ eNat.hom =
          ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) := by
      change ((K.sc n).map F).homologyπ ≫ eNat.hom = _
      exact hmapπNat
    conv_rhs => rw [Category.assoc]
    rw [hmapπNat']
    simp only [Category.assoc]
  have hsq :
      (HomologicalComplex.homologyMap can.inv (n : ℤ)).hom
          (fkE.inv.hom
            (eNat.inv.hom (F.map kE.hom qIntF))) =
        scExtH.inv.hom (eInt.inv.hom qIntF) := by
    apply scExtH.addCommGroupIsoToAddEquiv.injective
    apply eInt.addCommGroupIsoToAddEquiv.injective
    apply (F.mapIso kE).addCommGroupIsoToAddEquiv.injective
    have hsq_mor' := ConcreteCategory.congr_hom hsq_mor
      (fkE.inv.hom (eNat.inv.hom (F.map kE.hom qIntF)))
    change
      (ConcreteCategory.hom (F.map kE.hom))
          (eInt.hom (scExtH.hom
            ((HomologicalComplex.homologyMap can.inv (n : ℤ))
              (fkE.inv.hom (eNat.inv.hom (F.map kE.hom qIntF)))))) =
        (ConcreteCategory.hom (fkE.hom ≫ eNat.hom))
          (fkE.inv.hom (eNat.inv.hom (F.map kE.hom qIntF))) at hsq_mor'
    simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply,
      Iso.inv_hom_id_apply] at hsq_mor'
    change
      (ConcreteCategory.hom (F.map kE.hom))
          ((ConcreteCategory.hom eInt.hom)
            ((ConcreteCategory.hom scExtH.hom)
              ((ConcreteCategory.hom (HomologicalComplex.homologyMap can.inv (n : ℤ)))
                (fkE.inv.hom (eNat.inv.hom (F.map kE.hom qIntF)))))) =
        (ConcreteCategory.hom eNat.hom)
          ((ConcreteCategory.hom eNat.inv)
            ((ConcreteCategory.hom (F.map kE.hom)) qIntF)) at hsq_mor'
    rw [Iso.inv_hom_id_apply eNat
      (ConcreteCategory.hom (F.map kE.hom) qIntF)] at hsq_mor'
    simp only [Iso.addCommGroupIsoToAddEquiv_apply, Functor.mapIso_hom,
      Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]
    change
      (ConcreteCategory.hom (F.map kE.hom))
          ((ConcreteCategory.hom eInt.hom)
            ((ConcreteCategory.hom scExtH.hom)
              ((ConcreteCategory.hom (HomologicalComplex.homologyMap can.inv (n : ℤ)))
                (fkE.inv.hom (eNat.inv.hom (F.map kE.hom qIntF)))))) =
        (ConcreteCategory.hom (F.map kE.hom)) qIntF
    exact hsq_mor'
  rw [globalRawClassOfSupportedSingularClass]
  let qFNat : F.obj (K.sc n).homology := F.map kE.hom qIntF
  let qFMap : (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).homology :=
    eNat.inv.hom qFNat
  have hExtSing0 :
      (HomologicalComplex.homologyMap
          (globalRawSingularCochainComplexIntIsoSingular ℚ Y).hom (n : ℤ)).hom
          ((HomologicalComplex.extendHomologyIso
              (globalRawSingularCochainComplex ℚ Y)
              ComplexShape.embeddingUpNat hnj).inv.hom
            ((HomologicalComplex.homologyMapIso
              (globalRawSingularCochainComplexIsoSingular ℚ Y) n).inv.hom
              qFMap)) =
        fkE.inv.hom qFMap := by
    have hIso :
        (globalRawSingularCochainComplexIntIsoSingular ℚ Y).hom =
          HomologicalComplex.extendMap
            (globalRawSingularCochainComplexIsoSingular ℚ Y).hom
            ComplexShape.embeddingUpNat := by
      rfl
    rw [hIso]
    apply fkE.addCommGroupIsoToAddEquiv.injective
    have hn := HomologicalComplex.extendHomologyIso_hom_naturality
      (globalRawSingularCochainComplexIsoSingular ℚ Y).hom
      ComplexShape.embeddingUpNat hnj
    have hn' := ConcreteCategory.congr_hom hn
      ((HomologicalComplex.extendHomologyIso
          (globalRawSingularCochainComplex ℚ Y)
          ComplexShape.embeddingUpNat hnj).inv.hom
          ((HomologicalComplex.homologyMapIso
            (globalRawSingularCochainComplexIsoSingular ℚ Y) n).inv.hom
          qFMap))
    have hcancel :
        (ConcreteCategory.hom
          (HomologicalComplex.homologyMap
            (globalRawSingularCochainComplexIsoSingular ℚ Y).hom n))
          ((ConcreteCategory.hom
            (HomologicalComplex.homologyMap
              (globalRawSingularCochainComplexIsoSingular ℚ Y).inv n))
            qFMap) = qFMap := by
      rw [← ConcreteCategory.comp_apply]
      rw [← HomologicalComplex.homologyMap_comp]
      simp
    have hcancel' :
        (ConcreteCategory.hom
          (HomologicalComplex.homologyMap
            (globalRawSingularCochainComplexIsoSingular ℚ Y).hom n))
          ((ConcreteCategory.hom
            (HomologicalComplex.extendHomologyIso
              (globalRawSingularCochainComplex ℚ Y)
              ComplexShape.embeddingUpNat hnj).hom)
            ((ConcreteCategory.hom
              (HomologicalComplex.extendHomologyIso
                (globalRawSingularCochainComplex ℚ Y)
                ComplexShape.embeddingUpNat hnj).inv)
              ((ConcreteCategory.hom
                (HomologicalComplex.homologyMapIso
                  (globalRawSingularCochainComplexIsoSingular ℚ Y) n).inv)
      qFMap))) = qFMap := by
      rw [← ConcreteCategory.comp_apply]
      rw [← ConcreteCategory.comp_apply]
      rw [Iso.inv_hom_id_assoc]
      simpa only [HomologicalComplex.homologyMapIso_inv] using hcancel
    change (ConcreteCategory.hom
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso
          ComplexShape.embeddingUpNat hnj).hom)
        ((ConcreteCategory.hom
          (HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap
              (globalRawSingularCochainComplexIsoSingular ℚ Y).hom
              ComplexShape.embeddingUpNat) (n : ℤ)))
          ((ConcreteCategory.hom
            (HomologicalComplex.extendHomologyIso
              (globalRawSingularCochainComplex ℚ Y)
              ComplexShape.embeddingUpNat hnj).inv)
            ((ConcreteCategory.hom
              (HomologicalComplex.homologyMapIso
                (globalRawSingularCochainComplexIsoSingular ℚ Y) n).inv)
              qFMap))) =
      (ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (globalRawSingularCochainComplexIsoSingular ℚ Y).hom n))
        ((ConcreteCategory.hom
          (HomologicalComplex.extendHomologyIso
            (globalRawSingularCochainComplex ℚ Y)
            ComplexShape.embeddingUpNat hnj).hom)
          ((ConcreteCategory.hom
            (HomologicalComplex.extendHomologyIso
              (globalRawSingularCochainComplex ℚ Y)
              ComplexShape.embeddingUpNat hnj).inv)
            ((ConcreteCategory.hom
              (HomologicalComplex.homologyMapIso
                (globalRawSingularCochainComplexIsoSingular ℚ Y) n).inv)
              qFMap))) at hn'
    rw [hcancel'] at hn'
    dsimp [fkE, K, F] at hn' ⊢
    convert hn' using 1 <;> simp [HomologicalComplex.homology]
    all_goals
      change _ = _
      rfl
  have hExtSing :
      (HomologicalComplex.homologyMap
          (globalRawSingularCochainComplexIntIsoRelative ℚ Y).hom (n : ℤ)).hom
          ((HomologicalComplex.extendHomologyIso
              (globalRawSingularCochainComplex ℚ Y)
              ComplexShape.embeddingUpNat hnj).inv.hom
            ((HomologicalComplex.homologyMapIso
                (globalRawSingularCochainComplexIsoSingular ℚ Y) n).inv.hom
              (eNat.inv.hom qFNat))) =
        (HomologicalComplex.homologyMap can.inv (n : ℤ)).hom
          (fkE.inv.hom (eNat.inv.hom qFNat)) := by
    have hh := congrArg
      (fun z => (HomologicalComplex.homologyMap can.inv (n : ℤ)).hom z)
      hExtSing0
    have hIso :
        (globalRawSingularCochainComplexIntIsoSingular ℚ Y).hom =
          HomologicalComplex.extendMap
            (globalRawSingularCochainComplexIsoSingular ℚ Y).hom
            ComplexShape.embeddingUpNat := by
      rfl
    rw [hIso] at hh
    dsimp [can] at hh ⊢
    change (AddCommGrpCat.Hom.hom
      (HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (globalRawSingularCochainComplexIsoSingular ℚ Y).hom
          ComplexShape.embeddingUpNat ≫ can.inv)
        (n : ℤ)))
        ((AddCommGrpCat.Hom.hom
          (HomologicalComplex.extendHomologyIso
            (globalRawSingularCochainComplex ℚ Y)
            ComplexShape.embeddingUpNat hnj).inv)
          ((AddCommGrpCat.Hom.hom
            (HomologicalComplex.homologyMapIso
              (globalRawSingularCochainComplexIsoSingular ℚ Y) n).inv)
            qFMap)) =
      (AddCommGrpCat.Hom.hom (HomologicalComplex.homologyMap
        (HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat).inv
        (n : ℤ)))
        ((AddCommGrpCat.Hom.hom fkE.inv) qFMap)
    rw [HomologicalComplex.homologyMap_comp]
    exact hh
  unfold globalRawSingularCochainComplexInt at *
  let A : (HomologicalComplex.extend (globalRawSingularCochainComplex ℚ Y)
      ComplexShape.embeddingUpNat).homology (n : ℤ) :=
    globalRawRelativeCochainClass ℚ Y Zᶜ n a
  have hA : A = globalRawRelativeCochainClass ℚ Y Zᶜ n a := by
    rfl
  change (HomologicalComplex.extendHomologyIso
      (globalRawSingularCochainComplex ℚ Y)
      ComplexShape.embeddingUpNat hnj).addCommGroupIsoToAddEquiv
      A = _
  apply (HomologicalComplex.extendHomologyIso
    (globalRawSingularCochainComplex ℚ Y)
    ComplexShape.embeddingUpNat hnj).symm.addCommGroupIsoToAddEquiv.injective
  apply (HomologicalComplex.homologyMapIso
    (globalRawSingularCochainComplexIntIsoRelative ℚ Y) (n : ℤ)).addCommGroupIsoToAddEquiv.injective
  simp (config := { zetaDelta := false }) only [Iso.addCommGroupIsoToAddEquiv_apply,
    Iso.inv_hom_id_apply,
    HomologicalComplex.homologyMapIso_hom,
    ConcreteCategory.comp_apply]
  have hcancelA :
      (AddCommGrpCat.Hom.hom
        (HomologicalComplex.extendHomologyIso
          (globalRawSingularCochainComplex ℚ Y)
          ComplexShape.embeddingUpNat hnj).symm.hom)
        ((AddCommGrpCat.Hom.hom
          (HomologicalComplex.extendHomologyIso
            (globalRawSingularCochainComplex ℚ Y)
            ComplexShape.embeddingUpNat hnj).hom) A) = A := by
    rw [← ConcreteCategory.comp_apply]
    simp
  rw [hcancelA]
  rw [hA]
  have hscExt_hom : scExt.hom = 𝟙 _ := by
    ext <;> rfl
  have hscExtH_hom : scExtH.hom = 𝟙 _ := by
    dsimp [scExtH]
    rw [hscExt_hom]
    simp
  have hscExtH_inv : scExtH.inv = 𝟙 _ := by
    apply (cancel_mono scExtH.hom).1
    rw [Iso.inv_hom_id]
    rw [Category.id_comp]
    rw [hscExtH_hom]
    rfl
  have hsq' :
      (ConcreteCategory.hom eInt.inv) qIntF =
        (ConcreteCategory.hom (HomologicalComplex.homologyMap can.inv (n : ℤ)))
          ((ConcreteCategory.hom fkE.inv)
            ((ConcreteCategory.hom eNat.inv)
              ((ConcreteCategory.hom (F.map kE.hom)) qIntF))) := by
    have h := hsq.symm
    simp [hscExtH_inv] at h
    exact h
  have heX2 : eX2 = eInt := by
    dsimp [eX2, eInt, Y, K, F, P]
    rfl
  calc
    _ = (ConcreteCategory.hom
          ((HomologicalComplex.sc (relativeDualCochainShortComplexInt ℚ P).X₂
            (n : ℤ)).mapHomologyIso
              (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv)
          ((ConcreteCategory.hom
            (HomologicalComplex.homologyMap
              (relativeDualCochainShortComplexInt ℚ P).f (n : ℤ))) v) := by
      exact hrawIso
    _ = _ := by
      calc
        _ = (ConcreteCategory.hom eInt.inv) qIntF := by
          change (ConcreteCategory.hom eX2.inv) (f v) =
            (ConcreteCategory.hom eInt.inv) qIntF
          rw [heX2]
          dsimp [qIntF]
          rw [hqInt]
          rfl
        _ = (ConcreteCategory.hom (HomologicalComplex.homologyMap can.inv (n : ℤ)))
              ((ConcreteCategory.hom fkE.inv)
                ((ConcreteCategory.hom eNat.inv)
                  ((ConcreteCategory.hom (F.map kE.hom)) qIntF))) := hsq'
        _ = (ConcreteCategory.hom (HomologicalComplex.homologyMap can.inv (n : ℤ)))
              ((ConcreteCategory.hom fkE.inv) ((ConcreteCategory.hom eNat.inv) qFNat)) := by
          simpa only [qFNat]
        _ = _ := by
          exact hExtSing.symm

/-- The selected global raw singular cochain represents the ordinary class obtained by
forgetting support from the relative class.  This is a class-level statement: the cochain
representative itself is the noncomputably selected representative supplied by
`globalRawCochainOfSupportedSingularClass`. -/
lemma singularClassOfDisplayedGlobalRawCochain_eq_forgetSupport
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    singularClassOfDisplayedGlobalRawCochain X Z n a =
      AlgebraicTopology.Singular.forgetSupport ℚ (TopCat.of (ComplexPoint X)) Z n a := by
  exact (singularClassOfDisplayedGlobalRawCochain_eq_singularClassOfSupportedSingularClass
    X Z n a).trans (singularClassOfSupportedSingularClass_eq_forgetSupport X Z n a)

/-- The hypercohomology class obtained from a supported singular class maps under the Betti
comparison to the ordinary class obtained by forgetting support. -/
lemma rationalCohomologyLinearEquivSingularCohomology_hypercohomologyClassOfSupportedSingularClass_eq_forgetSupport
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    rationalCohomologyLinearEquivSingularCohomology X n
        (hypercohomologyClassOfSupportedSingularClass X Z n a) =
      AlgebraicTopology.Singular.forgetSupport ℚ (TopCat.of (ComplexPoint X)) Z n a := by
  rw [rationalCohomologyLinearEquivSingularCohomology_hypercohomologyClassOfSupportedSingularClass]
  exact singularClassOfSupportedSingularClass_eq_forgetSupport X Z n a

end AlgebraicGeometry.ComplexPoint
