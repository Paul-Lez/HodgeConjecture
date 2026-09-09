/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenRawRelativeConnecting
public import Other.AlgebraicTopology.SupportedSingularSectionCohomology

/-! # Literal top-open normalization of relative cochain classes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [Field R] (X : TopCat.{0})

/-- The actual pair of the top open and its intersection with U is the
ordinary ambient pair `(X,U)`, by removing only subtype witnesses. -/
def topOpenIntersectionPairIso (U : Opens X) :
    openInclusionPair X (Opens.infLELeft ⊤ U) ≅ TopPair.ofSubset (U : Set X) where
  hom := TopPair.ofHom (Opens.inclusionTopIso X).hom
    (TopCat.ofHom ⟨fun w => ⟨w.1, w.2.2⟩, continuous_subtype_val.subtype_mk _⟩) rfl
  inv := TopPair.ofHom (Opens.inclusionTopIso X).inv
    (TopCat.ofHom ⟨fun u => ⟨u.1, ⟨trivial, u.2⟩⟩, continuous_subtype_val.subtype_mk _⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- The whole-open support-complement pair is the literal ordinary ambient
support pair, with both subtype regroupings displayed. -/
def topOpenNeighborhoodSupportPairIso (S : Closeds X) :
    neighborhoodSupportComplementPair ((⊤ : Opens X) : Set X) (S : Set X) ≅
      TopPair.ofSubset ((S : Set X)ᶜ) :=
  (openIntersectionPairIsoSupportComplement X S S.isClosed ⊤).symm ≪≫
    topOpenIntersectionPairIso X S.compl

/-- The local support-complement comparison uses exactly pullback along the
displayed pair isomorphism. This isolates its evaluation from the resolutions. -/
theorem supportedSingularSupportComplementEquiv_apply
    [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : Set X) (hS : IsClosed S) (V : Opens X) (n : ℕ)
    (a : ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ)) :
    supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n a =
      relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement X S hS V).inv
        (supportedRationalSingularSectionCohomologyEquivRelative X
          ⟨Sᶜ, hS.isOpen_compl⟩ V n a) := rfl

/-- The ordinary and local top-open raw cochain identifications retain the
actual pullback along the top-open projection. -/
theorem globalRawCochainIso_comp_topOpenDual (U : Opens X) :
    (globalRawSingularCochainComplexIsoSingular R X).hom ≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (relativeDualCochainShortComplexNatMap R (topOpenIntersectionPairIso X U).hom).τ₂ =
      (openRawSingularCochainComplexIsoDual R X ⊤).hom := by
  change ((globalRawSingularCochainComplexIso R X).hom ≫
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
      (singularCochainComplexIsoTopOpen R X).inv) ≫
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
      (singularCochainComplexIsoTopOpen R X).hom = _
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The preceding exact cochain normalization survives extension to integer
degrees and the coefficient-forgetting grading comparison. -/
theorem globalRawCochainIntIso_comp_topOpenDual (U : Opens X) :
    (globalRawSingularCochainComplexIntIsoRelative R X).hom ≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
        (relativeDualCochainShortComplexIntMap R (topOpenIntersectionPairIso X U).hom).τ₂ =
      (openRawSingularCochainComplexIntIsoDual R X ⊤).hom := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let f := (relativeDualCochainShortComplexNatMap R (topOpenIntersectionPairIso X U).hom).τ₂
  change (HomologicalComplex.extendMap (globalRawSingularCochainComplexIsoSingular R X).hom
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendIso F (SingularChainComplex R X).linearDualCochainComplex
      ComplexShape.embeddingUpNat).inv) ≫
      (F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap f
        ComplexShape.embeddingUpNat) = _
  rw [Category.assoc, ← HomologicalComplex.mapExtendIso_inv_naturality,
    ← Category.assoc, ← HomologicalComplex.extendMap_comp]
  rw [globalRawCochainIso_comp_topOpenDual]
  rfl

set_option maxHeartbeats 1000000 in
/-- Removing the literal top-open subtype witnesses preserves the positive
ordinary class of a relative cochain, with the actual pair pullback displayed. -/
theorem openRawRelativeCochainClass_top (U : Opens X) (n : ℕ)
    (a : RelativeCohomology R (TopPair.ofSubset (U : Set X)) n) :
    openRawRelativeCochainClass R X (Opens.infLELeft ⊤ U) n
      (relativeCohomologyMap R n (topOpenIntersectionPairIso X U).hom a) =
        globalRawRelativeCochainClass R X U n a := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let q := (topOpenIntersectionPairIso X U).hom
  let f := relativeDualCochainShortComplexIntMap R q
  let SG := relativeDualCochainShortComplexInt R (TopPair.ofSubset (U : Set X))
  let SL := relativeDualCochainShortComplexInt R (openInclusionPair X (Opens.infLELeft ⊤ U))
  let eG := (SG.X₂.sc (n : ℤ)).mapHomologyIso F
  let eL := (SL.X₂.sc (n : ℤ)).mapHomologyIso F
  let g := HomologicalComplex.homologyMapIso (globalRawSingularCochainComplexIntIsoRelative R X) (n : ℤ)
  let l := HomologicalComplex.homologyMapIso (openRawSingularCochainComplexIntIsoDual R X ⊤) (n : ℤ)
  let b := (relativeDualCochainCohomologyEquiv R (TopPair.ofSubset (U : Set X)) n).symm a
  have ha : HomologicalComplex.homologyMap f.τ₁ (n : ℤ) b =
      (relativeDualCochainCohomologyEquiv R (openInclusionPair X (Opens.infLELeft ⊤ U)) n).symm
        (relativeCohomologyMap R n q a) := by
    apply (relativeDualCochainCohomologyEquiv R (openInclusionPair X (Opens.infLELeft ⊤ U)) n).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (relativeDualCochainCohomologyEquiv_naturality R q n b).trans
      (congrArg (relativeCohomologyMap R n q) (LinearEquiv.apply_symm_apply _ _))
  have hf : HomologicalComplex.homologyMap f.τ₁ (n : ℤ) ≫
      HomologicalComplex.homologyMap SL.f (n : ℤ) =
    HomologicalComplex.homologyMap SG.f (n : ℤ) ≫
      HomologicalComplex.homologyMap f.τ₂ (n : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun t => HomologicalComplex.homologyMap t (n : ℤ)) f.comm₁₂
  have hm : l.hom ≫ eL.hom = g.hom ≫ eG.hom ≫
      F.map (HomologicalComplex.homologyMap f.τ₂ (n : ℤ)) := by
    have hn := ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) (n : ℤ)).map f.τ₂) F
    change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map f.τ₂) (n : ℤ) ≫ eL.hom =
      eG.hom ≫ F.map (HomologicalComplex.homologyMap f.τ₂ (n : ℤ)) at hn
    change HomologicalComplex.homologyMap (openRawSingularCochainComplexIntIsoDual R X ⊤).hom
      (n : ℤ) ≫ eL.hom = _
    rw [← globalRawCochainIntIso_comp_topOpenDual R X U, HomologicalComplex.homologyMap_comp,
      Category.assoc, hn]
    rfl
  apply l.addCommGroupIsoToAddEquiv.injective
  apply eL.addCommGroupIsoToAddEquiv.injective
  change eL.hom (l.hom (l.inv (eL.inv (HomologicalComplex.homologyMap SL.f (n : ℤ)
    ((relativeDualCochainCohomologyEquiv R (openInclusionPair X (Opens.infLELeft ⊤ U)) n).symm
      (relativeCohomologyMap R n q a)))))) =
    eL.hom (l.hom (g.inv (eG.inv (HomologicalComplex.homologyMap SG.f (n : ℤ) b))))
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have hme := ConcreteCategory.congr_hom hm
    (g.inv (eG.inv (HomologicalComplex.homologyMap SG.f (n : ℤ) b)))
  change eL.hom (l.hom (g.inv (eG.inv (HomologicalComplex.homologyMap SG.f (n : ℤ) b)))) =
    HomologicalComplex.homologyMap f.τ₂ (n : ℤ)
      (eG.hom (g.hom (g.inv (eG.inv (HomologicalComplex.homologyMap SG.f (n : ℤ) b))))) at hme
  simp only [← ConcreteCategory.comp_apply,
    Iso.inv_hom_id, ConcreteCategory.id_apply] at hme
  rw [← ha]
  exact (ConcreteCategory.congr_hom hf b).trans hme.symm

end AlgebraicTopology.Singular
