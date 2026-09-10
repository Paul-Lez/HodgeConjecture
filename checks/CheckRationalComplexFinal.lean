import Other.AlgebraicGeometry.RationalComplexBettiCompatibility
import Other.Algebra.Homology.MapExtendNaturality
import Other.AlgebraicTopology.SingularProductCoefficientChange
import Other.AlgebraicTopology.LinearDualHomologyNaturality

@[expose] noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance checkHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
theorem test_hypercohomologyAddEquivGlobalSections_naturality
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (hKflasque : ∀ q, (K.X q).IsFlasque)
    (hLflasque : ∀ q, (L.X q).IsFlasque)
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSections X L 0 hLflasque n
        (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyAddEquivGlobalSections X K 0 hKflasque n a) := by
  let Y := TopCat.of (ComplexPoint X)
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L 0
  let I := Classical.choose hres
  let hresI := Classical.choose_spec hres
  let i := Classical.choose hresI
  let hresi := Classical.choose_spec hresI
  let hi : QuasiIso i := Classical.choose hresi
  let hresiHi := Classical.choose_spec hresi
  let hI : ∀ q : ℤ, Injective (I.X q) := Classical.choose hresiHi
  let hIge : I.IsStrictlyGE 0 := Classical.choose_spec hresiHi
  letI : QuasiIso i := hi
  letI : ∀ q : ℤ, Injective (I.X q) := hI
  letI : I.IsStrictlyGE 0 := hIge
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hLflasque hIflasque
  apply (AddCommGrpCat.mono_iff_injective
    (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) n)).mp inferInstance
  change
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) n
        (hypercohomologyAddEquivGlobalSectionsOfResolution
          X L I i n (hypercohomologyMap X f n a)) = _
  rw [hypercohomologyAddEquivGlobalSectionsOfResolution_map]
  rw [← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp]
  rw [← hypercohomologyMap_comp_apply]
  exact hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    X K I 0 hKflasque (f ≫ i) n a

end AlgebraicGeometry.ComplexPoint

namespace HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}

set_option backward.isDefEq.respectTransparency false in
theorem test_mapExtendIso_hom_naturality
    (F : Functor C D) [F.Additive] {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    (F.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫ extendMap ((F.mapHomologicalComplex c).map f) e := by
  rw [← cancel_epi (mapExtendIso F K e).inv]
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc,
    ← mapExtendIso_inv_naturality]
  simp

end HomologicalComplex

namespace HomologicalComplex

universe u v

variable {C D E : Type u}
  [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  {ι : Type v} {ι' : Type v} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem test_mapExtendCompIso_naturality
    (F : C ⥤ D) [F.Additive] (E₁ : D ⥤ E) [E₁.Additive]
    (G : C ⥤ E) [G.Additive] (eComp : F ⋙ E₁ ≅ G)
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    (G.mapHomologicalComplex c').map (extendMap f e) ≫
        (mapExtendIso (c' := c') G L e).hom ≫
        extendMap
          ((Functor.mapHomologicalComplexCompIso eComp c).inv.app L) e =
      (mapExtendIso (c' := c') G K e).hom ≫
        extendMap
          ((Functor.mapHomologicalComplexCompIso eComp c).inv.app K) e ≫
        extendMap
          ((E₁.mapHomologicalComplex c).map
            ((F.mapHomologicalComplex c).map f)) e := by
  rw [← Category.assoc, test_mapExtendIso_hom_naturality]
  simp only [Category.assoc]
  rw [← extendMap_comp, ← extendMap_comp]
  rw [(Functor.mapHomologicalComplexCompIso eComp c).inv.naturality]
  rfl

end HomologicalComplex

namespace HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D]
  [Abelian C] [Abelian D]
  {i : Type v} {c : ComplexShape i}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_map_homologyπ_comp_mapHomologyIso
    (F : C ⧤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (n : i)
    [F.PreservesLeftHomologyOf (K.sc n)] :
    (K.map F).homologyπ n ≫ ((K.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) := by
  let S := K.sc n
  let h := S.homologyData.left
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapCyclesIso_eq, h.mapHomologyIso_eq]
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc,
    (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc]
  rw [cancel_epi]
  change F.map (h.π ≫ h.homologyIso.inv) =
    F.map (h.cyclesIso.inv ≫ S.homologyπ)
  rw [h.π_comp_homologyIso_inv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_map_homologyπ_comp_mapHomologyIso_inv
    (F : C ⧤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (n : i)
    [F.PreservesLeftHomologyOf (K.sc n)] :
    F.map (K.homologyπ n) ≫ ((K.sc n).mapHomologyIso F).inv =
      ((K.sc n).mapCyclesIso F).inv ≫ (K.map F).homologyπ n := by
  rw [← cancel_epi ((K.sc n).mapCyclesIso F).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← test_map_homologyπ_comp_mapHomologyIso]
  simp

end HomologicalComplex

namespace AlgebraicTopology.Singular

variable (Y : TopCat.{0})

local instance testQToCModuleCochains (n : ℕ) :
    Module ℚ ((SingularChainComplex ℂ Y).linearDualCochainComplex.X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance testQToCScalarTowerCochains (n : ℕ) :
    IsScalarTower ℚ ℂ
      ((SingularChainComplex ℂ Y).linearDualCochainComplex.X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Complex singular cochains regarded as a cochain complex of rational modules. -/
abbrev testRestrictedCOrdinarySingularCochains :
    CochainComplex (ModuleCat ℚ) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      (SingularChainComplex ℂ Y).linearDualCochainComplex

/-- Coefficient extension on whole-space cochains before forgetting additive structure. -/
def testQToCOrdinarySingularCochainComplexRestricted :
    (SingularChainComplex ℚ Y).linearDualCochainComplex ⟶
      testRestrictedCOrdinarySingularCochains Y where
  f n := ModuleCat.ofHom (qToCSingularCochain Y n)
  comm' i j hij := by
    obtain rfl := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    simp only [Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.linearDualCochainComplex_d]
    change ((SingularChainComplex ℂ Y).d (i + 1) i).hom.dualMap
        (qToCSingularCochain Y i φ) =
      qToCSingularCochain Y (i + 1)
        (((SingularChainComplex ℚ Y).d (i + 1) i).hom.dualMap φ)
    exact (qToCSingularCochain_coboundary Y i φ).symm

/-- Restriction of scalars commutes with cohomology of the complex singular cochain complex. -/
def testRestrictedCOrdinarySingularCochainsHomologyIso (n : ℕ) :
    (testRestrictedCOrdinarySingularCochains Y).homology n ≅
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
        ((SingularChainComplex ℂ Y).linearDualCochainComplex.homology n) :=
  ShortComplex.mapHomologyIso
    ((SingularChainComplex ℂ Y).linearDualCochainComplex.sc n)
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))

/-- Coefficient extension on the ordinary whole-space singular cochain complexes,
with scalar structures forgotten. -/
def testQToCOrdinarySingularCochainComplex :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (SingularChainComplex ℚ Y).linearDualCochainComplex ⟶
      ((forget₂ (ModuleCat ℂ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex ℂ Y).linearDualCochainComplex where
  f n := AddCommGrpCat.ofHom (qToCSingularCochain Y n).toAddMonoidHom
  comm' i j hij := by
    obtain rfl := hij
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    simp only [ConcreteCategory.comp_apply,
      Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.linearDualCochainComplex_d]
    change ((SingularChainComplex ℂ Y).d (i + 1) i).hom.dualMap
        (qToCSingularCochain Y i φ) =
      qToCSingularCochain Y (i + 1)
        (((SingularChainComplex ℚ Y).d (i + 1) i).hom.dualMap φ)
    exact (qToCSingularCochain_coboundary Y i φ).symm

/-- Coefficient extension on the raw global singular-cochain complexes. -/
def testQToCGlobalRawSingularCochainComplex :
    globalRawSingularCochainComplex ℚ Y ⟶
      globalRawSingularCochainComplex ℂ Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (qToCSingularCochainPresheafComplex Y)

/-- Coefficient extension on global sections of singular-cochain sheaves. -/
def testQToCGlobalSingularCochainSheafComplex :
    globalSingularCochainSheafComplex ℚ Y ⟶
      globalSingularCochainSheafComplex ℂ Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (qToCSingularCochainSheafComplex Y))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem test_topOpenToGlobal_qToC_naturality :
    topOpenToGlobalSingularCochainSheafComplex ℚ Y ≫
        testQToCGlobalSingularCochainSheafComplex Y =
      testQToCGlobalRawSingularCochainComplex Y ≫
        topOpenToGlobalSingularCochainSheafComplex ℂ Y := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  change (toSheafify (Opens.grothendieckTopology Y)
      (singularCochainPresheaf ℚ Y n)).app (.op ⊤) ≫
      ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (qToCSingularCochainPresheaf Y n)).hom.app (.op ⊤) =
    (qToCSingularCochainPresheaf Y n).app (.op ⊤) ≫
      (toSheafify (Opens.grothendieckTopology Y)
        (singularCochainPresheaf ℂ Y n)).app (.op ⊤)
  simpa only [NatTrans.comp_app] using (congrArg (fun f => f.app (.op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology Y)
      (qToCSingularCochainPresheaf Y n))).symm

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (.of ℂ)))

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem test_globalSectionsSingularCochainComplexIntIsoExtend_naturality :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (rationalToComplexSingularCochainComplexInt X) ≫
        (globalSectionsComplexSingularCochainComplexIntIsoExtend X).hom =
      (globalSectionsSingularCochainComplexIntIsoExtend X).hom ≫
        HomologicalComplex.extendMap
          (AlgebraicTopology.Singular.testQToCGlobalSingularCochainSheafComplex
            (TopCat.of (ComplexPoint X)))
          ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let SQ := AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y
  let SC := AlgebraicTopology.Singular.singularCochainSheafComplex ℂ Y
  let q := AlgebraicTopology.Singular.qToCSingularCochainSheafComplex Y
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : E.Additive := by dsimp [E]; infer_instance
  letI : Γ.Additive := by dsimp [Γ]; infer_instance
  let eComp : F ⋙ E ≅ Γ := Iso.refl _
  change
    (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap q ComplexShape.embeddingUpNat) ≫
      (HomologicalComplex.mapExtendIso Γ SC ComplexShape.embeddingUpNat).hom ≫
        HomologicalComplex.extendMap
          ((Functor.mapHomologicalComplexCompIso eComp
            (ComplexShape.up ℕ)).inv.app SC) ComplexShape.embeddingUpNat =
    (HomologicalComplex.mapExtendIso Γ SQ ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap
        ((Functor.mapHomologicalComplexCompIso eComp
          (ComplexShape.up ℕ)).inv.app SQ) ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap
        ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map q))
        ComplexShape.embeddingUpNat
  exact HomologicalComplex.test_mapExtendCompIso_naturality
    F E Γ eComp q ComplexShape.embeddingUpNat

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

variable (Y : TopCat.{0})

local instance testQToCModuleCochains2 (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).linearDualCochainComplex.X n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerCochains2 (n : Nat) :
    IsScalarTower Rat Complex
      ((SingularChainComplex Complex Y).linearDualCochainComplex.X n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance testQToCModuleCohomology (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).linearDualCochainComplex.homology n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerCohomology (n : Nat) :
    IsScalarTower Rat Complex
      ((SingularChainComplex Complex Y).linearDualCochainComplex.homology n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance testQToCModuleCochainCycles (n : Nat) :
    Module Rat
      ((SingularChainComplex Complex Y).linearDualCochainComplex.cycles n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerCochainCycles (n : Nat) :
    IsScalarTower Rat Complex
      ((SingularChainComplex Complex Y).linearDualCochainComplex.cycles n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance testQToCModuleChainCycles (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).cycles n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerChainCycles (n : Nat) :
    IsScalarTower Rat Complex ((SingularChainComplex Complex Y).cycles n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance testQToCModuleHomology (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).homology n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerHomology (n : Nat) :
    IsScalarTower Rat Complex ((SingularChainComplex Complex Y).homology n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance testQToCModuleHomology' (n : Nat) :
    Module Rat ((CChains Y).homology n) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerHomology' (n : Nat) :
    IsScalarTower Rat Complex ((CChains Y).homology n) :=
  IsScalarTower.of_compHom Rat Complex _

local instance testQToCModuleRawChainCycles (n : Nat) :
    Module Rat
      (((SingularChainComplex Complex Y).sc n).homologyData.left.K) :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerRawChainCycles (n : Nat) :
    IsScalarTower Rat Complex
      (((SingularChainComplex Complex Y).sc n).homologyData.left.K) :=
  IsScalarTower.of_compHom Rat Complex _

local instance testQToCModuleShortChainCycles (n : Nat) :
    Module Rat ((SingularChainComplex Complex Y).sc n).cycles :=
  Module.compHom _ (algebraMap Rat Complex)

local instance testQToCScalarTowerShortChainCycles (n : Nat) :
    IsScalarTower Rat Complex ((SingularChainComplex Complex Y).sc n).cycles :=
  IsScalarTower.of_compHom Rat Complex _

def testRestrictedCOrdinarySingularCochainsCyclesIso (n : Nat) :
    (testRestrictedCOrdinarySingularCochains Y).cycles n ≅
      (ModuleCat.restrictScalars (algebraMap Rat Complex)).obj
        ((SingularChainComplex Complex Y).linearDualCochainComplex.cycles n) :=
  ((SingularChainComplex Complex Y).linearDualCochainComplex.sc n).mapCyclesIso
    (ModuleCat.restrictScalars (algebraMap Rat Complex))

def testQToCOrdinaryCochainCycles (n : Nat) :
    (SingularChainComplex Rat Y).linearDualCochainComplex.cycles n →ₗ[Rat]
      (SingularChainComplex Complex Y).linearDualCochainComplex.cycles n :=
  (testRestrictedCOrdinarySingularCochainsCyclesIso Y n).hom.hom.comp
    (HomologicalComplex.cyclesMap
      (testQToCOrdinarySingularCochainComplexRestricted Y) n).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_restrictedCOrdinarySingularCochains_homologyπ_iso (n : Nat) :
    (testRestrictedCOrdinarySingularCochains Y).homologyπ n ≫
        (testRestrictedCOrdinarySingularCochainsHomologyIso Y n).hom =
      (testRestrictedCOrdinarySingularCochainsCyclesIso Y n).hom ≫
        (ModuleCat.restrictScalars (algebraMap Rat Complex)).map
          ((SingularChainComplex Complex Y).linearDualCochainComplex.homologyπ n) := by
  let S := (SingularChainComplex Complex Y).linearDualCochainComplex.sc n
  let F := ModuleCat.restrictScalars (algebraMap Rat Complex)
  let h := S.homologyData.left
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapCyclesIso_eq, h.mapHomologyIso_eq]
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc,
    (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc]
  rw [cancel_epi]
  change F.map (h.π ≫ h.homologyIso.inv) =
    F.map (h.cyclesIso.inv ≫ S.homologyπ)
  rw [h.π_comp_homologyIso_inv]

lemma test_iCycles_comp_qToCOrdinaryCochainCycles (n : Nat) :
    (qToCSingularCochain Y n).comp
        ((SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n).hom =
      (((SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n).hom.restrictScalars Rat).comp
        (testQToCOrdinaryCochainCycles Y n) := by
  apply LinearMap.ext
  intro phi
  have h1 := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.cyclesMap_i
        (testQToCOrdinarySingularCochainComplexRestricted Y) n).symm) phi
  have h2 := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (ShortComplex.mapCyclesIso_hom_iCycles
        ((SingularChainComplex Complex Y).linearDualCochainComplex.sc n)
        (ModuleCat.restrictScalars (algebraMap Rat Complex))))
    ((HomologicalComplex.cyclesMap
      (testQToCOrdinarySingularCochainComplexRestricted Y) n).hom phi)
  change qToCSingularCochain Y n
      (((SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n).hom phi) =
    ((SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n).hom
      (testQToCOrdinaryCochainCycles Y n phi)
  exact h1.trans h2.symm

/-- The class-level map induced by literal coefficient extension on singular cochains. -/
def testQToCOrdinaryCochainCohomologyMap (n : Nat) :
    OrdinarySingularCohomology Rat Y n →ₗ[Rat]
      OrdinarySingularCohomology Complex Y n :=
  (testRestrictedCOrdinarySingularCochainsHomologyIso Y n).hom.hom.comp
    (HomologicalComplex.homologyMap
      (testQToCOrdinarySingularCochainComplexRestricted Y) n).hom

lemma test_qToCOrdinaryCochainCohomologyMap_homologyπ (n : Nat)
    (phi : (SingularChainComplex Rat Y).linearDualCochainComplex.cycles n) :
    testQToCOrdinaryCochainCohomologyMap Y n
        ((SingularChainComplex Rat Y).linearDualCochainComplex.homologyπ n phi) =
      (SingularChainComplex Complex Y).linearDualCochainComplex.homologyπ n
        (testQToCOrdinaryCochainCycles Y n phi) := by
  let KQ := (SingularChainComplex Rat Y).linearDualCochainComplex
  let KC := (SingularChainComplex Complex Y).linearDualCochainComplex
  let KR := testRestrictedCOrdinarySingularCochains Y
  let q := testQToCOrdinarySingularCochainComplexRestricted Y
  let eC := testRestrictedCOrdinarySingularCochainsCyclesIso Y n
  let eH := testRestrictedCOrdinarySingularCochainsHomologyIso Y n
  let F := ModuleCat.restrictScalars (algebraMap Rat Complex)
  have h : KQ.homologyπ n ≫ HomologicalComplex.homologyMap q n ≫ eH.hom =
      HomologicalComplex.cyclesMap q n ≫ eC.hom ≫ F.map (KC.homologyπ n) := by
    rw [HomologicalComplex.homologyπ_naturality_assoc,
      test_restrictedCOrdinarySingularCochains_homologyπ_iso]
  exact ConcreteCategory.congr_hom h phi

def testQToCOrdinaryChainCycles (n : Nat) :
    (SingularChainComplex Rat Y).cycles n →ₗ[Rat]
      (SingularChainComplex Complex Y).cycles n :=
  (((SingularChainComplex Complex Y).sc n).homologyData.left.cyclesIso.inv.hom
    |>.restrictScalars Rat).comp (qToCCycles Y n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_iCycles_qToCOrdinaryChainCycles (n : Nat)
    (z : (SingularChainComplex Rat Y).cycles n) :
    (SingularChainComplex Complex Y).iCycles n
        (testQToCOrdinaryChainCycles Y n z) =
      qToCChainGroup Y n ((SingularChainComplex Rat Y).iCycles n z) := by
  let h := ((SingularChainComplex Complex Y).sc n).homologyData.left
  have hq := DFunLike.congr_fun (iCycles_comp_qToCChainGroup Y n) z
  have hc := ConcreteCategory.congr_hom h.cyclesIso_inv_comp_iCycles
    (qToCCycles Y n z)
  change ((SingularChainComplex Complex Y).sc n).iCycles.hom
      (h.cyclesIso.inv.hom (qToCCycles Y n z)) =
    qToCChainGroup Y n
      (((SingularChainComplex Rat Y).sc n).iCycles.hom z)
  exact hc.trans hq.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_qToCHomology_homologyπ (n : Nat)
    (z : (SingularChainComplex Rat Y).cycles n) :
    qToCHomology Y n
        ((SingularChainComplex Rat Y).homologyπ n z) =
      (SingularChainComplex Complex Y).homologyπ n
        (testQToCOrdinaryChainCycles Y n z) := by
  let S := (SingularChainComplex Complex Y).sc n
  let h := S.homologyData.left
  have hq := ConcreteCategory.congr_hom
    (homologyπ_comp_qToCHomology Y n) z
  have hc := ConcreteCategory.congr_hom h.π_comp_homologyIso_inv
    (qToCCycles Y n z)
  have hi : h.homologyIso.inv = 𝟙 _ := by
    simp only [ShortComplex.LeftHomologyData.homologyIso, Iso.trans_inv,
      Iso.symm_inv]
    change S.leftHomologyIso.inv ≫ S.leftHomologyIso.hom = 𝟙 _
    simp
  change qToCHomology Y n
      ((SingularChainComplex Rat Y).homologyπ n z) =
    S.homologyπ.hom (h.cyclesIso.inv.hom (qToCCycles Y n z))
  change qToCHomology Y n
      ((SingularChainComplex Rat Y).homologyπ n z) =
    h.π.hom (qToCCycles Y n z) at hq
  rw [hi] at hc
  simp only [Category.comp_id, ConcreteCategory.comp_apply] at hc
  exact hq.trans hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_linearDualHomologyEquiv_homologyπ_apply
    {R : Type} [Field R] (K : ChainComplex (ModuleCat R) Nat) (n : Nat)
    (phi : K.linearDualCochainComplex.cycles n) (z : K.cycles n) :
    HomologicalComplex.linearDualHomologyEquiv K n
        (K.linearDualCochainComplex.homologyπ n phi)
        (K.homologyπ n z) =
      (show Module.Dual R (K.X n) from
        K.linearDualCochainComplex.iCycles n phi) (K.iCycles n z) := by
  change (K.sc n).linearDualHomologyEquiv
      ((ShortComplex.homologyMap
        (HomologicalComplex.linearDualCochainComplexScIso K n).hom).hom
        ((K.linearDualCochainComplex.sc n).homologyπ.hom phi))
      ((K.sc n).homologyπ z) = _
  rw [← ConcreteCategory.comp_apply,
    ShortComplex.homologyπ_naturality]
  change (K.sc n).linearDualHomologyEquiv
      ((K.sc n).linearDual.homologyπ.hom
        ((ShortComplex.cyclesMap
          (HomologicalComplex.linearDualCochainComplexScIso K n).hom).hom phi))
      ((K.sc n).homologyπ.hom z) = _
  rw [ShortComplex.linearDualHomologyEquiv_homologyπ_apply]
  have hi := ConcreteCategory.congr_hom
    (ShortComplex.cyclesMap_i
      (HomologicalComplex.linearDualCochainComplexScIso K n).hom) phi
  have he :
      (HomologicalComplex.linearDualCochainComplexScIso K n).hom.τ₂ = 𝟙 _ := by
    simp [HomologicalComplex.linearDualCochainComplexScIso,
      HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]
  rw [he] at hi
  simp only [Category.comp_id, ConcreteCategory.comp_apply] at hi
  have hi' :
      (show Module.Dual R (K.X n) from
        (K.sc n).linearDual.iCycles.hom
          ((ShortComplex.cyclesMap
            (HomologicalComplex.linearDualCochainComplexScIso K n).hom).hom phi)) =
      (show Module.Dual R (K.X n) from
        K.linearDualCochainComplex.iCycles n phi) := by
    exact hi
  exact congrArg (fun f : Module.Dual R (K.X n) ↦ f (K.iCycles n z)) hi'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_qToCOrdinaryCochain_uct_pairing (n : Nat)
    (a : OrdinarySingularCohomology Rat Y n)
    (z : (SingularChainComplex Rat Y).homology n) :
    HomologicalComplex.linearDualHomologyEquiv (SingularChainComplex Complex Y) n
        (testQToCOrdinaryCochainCohomologyMap Y n a)
        (qToCHomology Y n z) =
      algebraMap Rat Complex
        (HomologicalComplex.linearDualHomologyEquiv
          (SingularChainComplex Rat Y) n a z) := by
  let KQ := (SingularChainComplex Rat Y).linearDualCochainComplex
  let KC := (SingularChainComplex Complex Y).linearDualCochainComplex
  obtain ⟨phi, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (KQ.homologyπ n)).mp inferInstance a
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective
      ((SingularChainComplex Rat Y).homologyπ n)).mp inferInstance z
  rw [test_qToCOrdinaryCochainCohomologyMap_homologyπ,
    test_qToCHomology_homologyπ,
    test_linearDualHomologyEquiv_homologyπ_apply,
    test_linearDualHomologyEquiv_homologyπ_apply]
  have hphi := DFunLike.congr_fun
    (test_iCycles_comp_qToCOrdinaryCochainCycles Y n) phi
  have hc := test_iCycles_qToCOrdinaryChainCycles Y n c
  change (show Module.Dual Complex
      ((SingularChainComplex Complex Y).X n) from
      (SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n
        (testQToCOrdinaryCochainCycles Y n phi))
      ((SingularChainComplex Complex Y).iCycles n
        (testQToCOrdinaryChainCycles Y n c)) =
    algebraMap Rat Complex
      ((show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
        (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi)
        ((SingularChainComplex Rat Y).iCycles n c))
  have hphi' :
      (show Module.Dual Complex
        ((SingularChainComplex Complex Y).X n) from
        (SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n
          (testQToCOrdinaryCochainCycles Y n phi)) =
      qToCSingularCochain Y n
        (show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
          (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi) := by
    change qToCSingularCochain Y n
        (show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
          (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi) =
      (show Module.Dual Complex
        ((SingularChainComplex Complex Y).X n) from
        (SingularChainComplex Complex Y).linearDualCochainComplex.iCycles n
          (testQToCOrdinaryCochainCycles Y n phi)) at hphi
    exact hphi.symm
  calc
    _ = qToCSingularCochain Y n
        (show Module.Dual Rat ((SingularChainComplex Rat Y).X n) from
          (SingularChainComplex Rat Y).linearDualCochainComplex.iCycles n phi)
        (qToCChainGroup Y n
          ((SingularChainComplex Rat Y).iCycles n c)) := by
      rw [hphi', hc]
      rfl
    _ = _ := qToCSingularCochain_apply_qToCChain Y n _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_qToCOrdinaryCohomology_uct (n : Nat)
    (a : OrdinarySingularCohomology Rat Y n) :
    ordinarySingularCohomologyEquivCohomology Complex Y n
        (testQToCOrdinaryCochainCohomologyMap Y n a) =
      rationalToComplexCohomologyMap Y n
        (ordinarySingularCohomologyEquivCohomology Rat Y n a) := by
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange Y n).inductionOn w
    (fun w =>
      ordinarySingularCohomologyEquivCohomology Complex Y n
          (testQToCOrdinaryCochainCohomologyMap Y n a) w =
        rationalToComplexCohomologyMap Y n
          (ordinarySingularCohomologyEquivCohomology Rat Y n a) w)
  · simp
  · intro z
    exact (test_qToCOrdinaryCochain_uct_pairing Y n a z).trans
      ((qToCHomology_isBaseChange Y n).toDual_comp_apply
        (ordinarySingularCohomologyEquivCohomology Rat Y n a) z).symm
  · intro c z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_ordinarySingularCohomologyEquivGlobalRaw_qToC
    (n : Nat) (a : OrdinarySingularCohomology Rat Y n) :
    HomologicalComplex.homologyMap
        (testQToCGlobalRawSingularCochainComplex Y) n
        (ordinarySingularCohomologyEquivGlobalRaw Rat Y n a) =
      ordinarySingularCohomologyEquivGlobalRaw Complex Y n
        (testQToCOrdinaryCochainCohomologyMap Y n a) := by
  let KQ := (SingularChainComplex Rat Y).linearDualCochainComplex
  obtain ⟨phi, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (KQ.homologyπ n)).mp inferInstance a
  rw [test_qToCOrdinaryCochainCohomologyMap_homologyπ]
  dsimp only [ordinarySingularCohomologyEquivGlobalRaw,
    AddEquiv.trans_apply]
  simp only [← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality]

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular.HereditarilyParacompact

variable (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma test_ordinarySingularCohomologyEquivGlobalSections_qToC
    (n : Nat) (a : OrdinarySingularCohomology Rat Y n) :
    ordinaryComplexSingularCohomologyEquivGlobalSections Y n
        (testQToCOrdinaryCochainCohomologyMap Y n a) =
      HomologicalComplex.homologyMap
        (testQToCGlobalSingularCochainSheafComplex Y) n
        (ordinaryRationalSingularCohomologyEquivGlobalSections Y n a) := by
  dsimp only [ordinaryComplexSingularCohomologyEquivGlobalSections,
    ordinaryRationalSingularCohomologyEquivGlobalSections, AddEquiv.trans_apply]
  rw [← test_ordinarySingularCohomologyEquivGlobalRaw_qToC]
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  rw [test_topOpenToGlobal_qToC_naturality]

end AlgebraicTopology.Singular.HereditarilyParacompact
