/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialRawWindingClass
public import Other.AlgebraicGeometry.RawComplementResolutionComparison
public import Other.AlgebraicTopology.OpenRawComplementNormalization

/-!
# The actual exponential winding class in the intrinsic complement presentation

The comparison on the specified open Ω agrees with the original intrinsic
complement comparison used by the support-boundary theorem. We prove equality of
complex maps by cancelling raw restriction, which is epic on complexes. No
surjectivity on cycles or cohomology is inferred from that cancellation.

The class theorem transports the existing normalized winding class through the
actual raw maps, keeping the literal double complement and top-open intersection.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
  (Ω : Opens (TopCat.of (ComplexPoint X)))
/-- The open raw comparison preserves the literal restriction from the ambient space. -/
lemma openRawRestriction_comp_complementResolutionOnOpen :
    HomologicalComplex.extendMap
      (openRawSingularRestriction ℚ (TopCat.of (ComplexPoint X)) (homOfLE (le_top : Ω ≤ ⊤)))
      ComplexShape.embeddingUpNat ≫ openRawToComplementResolutionOnOpen X Ω =
    globalRawToSingularSheafInt X ≫
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl)) := by
  let Y := TopCat.of (ComplexPoint X)
  let K := singularCochainSheafComplex ℚ Y
  let Γ := (TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)
  let i : Ω ⟶ ⊤ := homOfLE le_top
  let e := (NatIso.mapHomologicalComplex (openRestrictionTopEval Ω) (.up ℤ)).app
    (singularCochainSheafComplexInt X ℚ)
  let eW := HomologicalComplex.mapExtendCanonicalIso
    (TopCat.Sheaf.supportEvaluation Y Ω) K ComplexShape.embeddingUpNat
  let eTop := HomologicalComplex.mapExtendCanonicalIso
    (TopCat.Sheaf.supportEvaluation Y ⊤) K ComplexShape.embeddingUpNat
  let ρ := HomologicalComplex.extendMap (openRawSingularRestriction ℚ Y i)
    ComplexShape.embeddingUpNat
  let a := HomologicalComplex.extendMap
    (openRawToSingularCochainSheafComplex ℚ Y ⊤) ComplexShape.embeddingUpNat
  let b := HomologicalComplex.extendMap
    (openRawToSingularCochainSheafComplex ℚ Y Ω) ComplexShape.embeddingUpNat
  let r := HomologicalComplex.extendMap
    (openSingularSheafRestriction ℚ Y i) ComplexShape.embeddingUpNat
  let r' := TopCat.Sheaf.sectionComplexRestriction Y (.up ℤ)
    (singularCochainSheafComplexInt X ℚ) i
  let g := Γ.map (TopCat.Sheaf.supportRestrictionComplexShortComplex Y Ω
    (singularCochainSheafComplexInt X ℚ)).g
  let f := Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)
  have hunit : ρ ≫ b = a ≫ r := openSingularSheafRestrictionInt_naturality ℚ Y i
  have hgrade : r ≫ eW.inv = eTop.inv ≫ r' := by
    have hext : r' ≫ eW.hom = eTop.hom ≫ r :=
      TopCat.Sheaf.sectionComplexRestriction_extend Y K i
    apply (cancel_mono eW.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hext, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hrestr : g ≫ e.hom = r' := by
    ext j : 1
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro t
    exact openRestrictionTopEval_restrictionUnit Ω
      ((singularCochainSheafComplexInt X ℚ).X j) t
  have htop : a ≫ eTop.inv = globalRawToSingularSheafInt X :=
    complexOpenRawToSheafTop_eq_global X
  have hrestr' : r' ≫ e.inv = g := by
    rw [← hrestr]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hgf : g ≫ f = Γ.map
      (naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl) := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg Γ.map
      (actualSingularRestriction_comp_naturalOutsideResolutionComparisonOnOpen X Ω)
  change ρ ≫ (b ≫ eW.inv ≫ e.inv ≫ f) = _
  calc
    _ = (a ≫ r) ≫ eW.inv ≫ e.inv ≫ f := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ eW.inv ≫ e.inv ≫ f) hunit
    _ = (a ≫ eTop.inv) ≫ r' ≫ e.inv ≫ f := by
      simpa only [Category.assoc] using congrArg (fun k => a ≫ k ≫ e.inv ≫ f) hgrade
    _ = (a ≫ eTop.inv) ≫ g ≫ f := by rw [← Category.assoc r', hrestr']
    _ = globalRawToSingularSheafInt X ≫ (g ≫ f) := by rw [htop]
    _ = _ := congrArg (fun k => globalRawToSingularSheafInt X ≫ k) hgf

/-- Raw cochains on Ω transported to the prescribed intrinsic double-complement
presentation, through literal raw restriction and the existing top-open iso. -/
def openRawToIntrinsicComplement :
    (openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) Ω).extend
        ComplexShape.embeddingUpNat ⟶
      globalRawPushforwardSingularCochainComplexInt ℚ (TopCat.of (ComplexPoint X))
        ((Ω : Set (ComplexPoint X))ᶜ)ᶜ := by
  let U : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨((Ω : Set (ComplexPoint X))ᶜ)ᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
  let j : ⊤ ⊓ U ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
  let t := globalRawComplementToTopOpenCochains ℚ (TopCat.of (ComplexPoint X)) U
  let := globalRawComplementToTopOpenCochains_isIso ℚ (TopCat.of (ComplexPoint X)) U
  exact HomologicalComplex.extendMap (openRawSingularRestriction ℚ (TopCat.of (ComplexPoint X)) j)
    ComplexShape.embeddingUpNat ≫ inv t

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Intrinsic raw transport preserves the actual restriction from ambient raw cochains. -/
lemma openRawRestriction_comp_intrinsicComplement :
    HomologicalComplex.extendMap
      (openRawSingularRestriction ℚ (TopCat.of (ComplexPoint X)) (homOfLE (le_top : Ω ≤ ⊤)))
      ComplexShape.embeddingUpNat ≫ openRawToIntrinsicComplement X Ω =
    globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X)) ((Ω : Set (ComplexPoint X))ᶜ)ᶜ := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨((Ω : Set (ComplexPoint X))ᶜ)ᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
  let j : ⊤ ⊓ U ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
  let i : Ω ⟶ ⊤ := homOfLE le_top
  let t := globalRawComplementToTopOpenCochains ℚ Y U
  let := globalRawComplementToTopOpenCochains_isIso ℚ Y U
  let ρ := HomologicalComplex.extendMap (openRawSingularRestriction ℚ Y i)
    ComplexShape.embeddingUpNat
  let s := HomologicalComplex.extendMap (openRawSingularRestriction ℚ Y j)
    ComplexShape.embeddingUpNat
  have h : ρ ≫ s = globalRawSingularRestrictionInt ℚ Y (U : Set Y) ≫ t := by
    rw [globalRawSingularRestrictionInt_comp_topOpen]
    change HomologicalComplex.extendMap (openRawSingularRestriction ℚ Y i)
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (openRawSingularRestriction ℚ Y j)
        ComplexShape.embeddingUpNat = _
    rw [← HomologicalComplex.extendMap_comp, ← openRawSingularRestriction_comp]
    congr 1
  change ρ ≫ (s ≫ inv t) = _
  rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The Ω-indexed exponential comparison is the exact original intrinsic raw
complement comparison, following the prescribed change of raw presentation. -/
lemma openRawToComplementResolutionOnOpen_eq_intrinsic :
    openRawToComplementResolutionOnOpen X Ω =
    openRawToIntrinsicComplement X Ω ≫
      globalRawComplementToDerivedPushforwardInt X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl := by
  let i : Ω ⟶ (⊤ : Opens (TopCat.of (ComplexPoint X))) := homOfLE le_top
  let := openRawSingularRestrictionInt_epi ℚ (TopCat.of (ComplexPoint X)) i
  apply (cancel_epi (HomologicalComplex.extendMap
    (openRawSingularRestriction ℚ (TopCat.of (ComplexPoint X)) i) ComplexShape.embeddingUpNat)).mp
  rw [openRawRestriction_comp_complementResolutionOnOpen, ← Category.assoc,
    openRawRestriction_comp_intrinsicComplement]
  exact globalNaturalSingularResolutionRestrictionInt_naturality X
    ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Returning from the intrinsic complement presentation is exactly raw
restriction to the literal top-open intersection. -/
lemma openRawToIntrinsicComplement_comp_topOpen :
    let U : Opens (TopCat.of (ComplexPoint X)) :=
      ⟨((Ω : Set (ComplexPoint X))ᶜ)ᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
    let j : ⊤ ⊓ U ⟶ Ω := homOfLE (fun _q hq => not_not.mp hq.2)
    openRawToIntrinsicComplement X Ω ≫
      globalRawComplementToTopOpenCochains ℚ (TopCat.of (ComplexPoint X)) U =
    HomologicalComplex.extendMap
      (openRawSingularRestriction ℚ (TopCat.of (ComplexPoint X)) j) ComplexShape.embeddingUpNat := by
  dsimp only
  let U : Opens (TopCat.of (ComplexPoint X)) :=
    ⟨((Ω : Set (ComplexPoint X))ᶜ)ᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
  let := globalRawComplementToTopOpenCochains_isIso ℚ (TopCat.of (ComplexPoint X)) U
  dsimp only [openRawToIntrinsicComplement]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (u : (holomorphicUnitSheaf X d).obj.obj (op Ω))

/-- The actual restricted singular class is the image of normalized raw winding
under the original intrinsic-complement map used in the support boundary theorem. -/
lemma complementRationalHypercohomology_restrictedSingularOneCocycle_eq_intrinsicWinding :
    let z := (restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))
        ((openRestrictionTopEval Ω).inv.app (holomorphicUnitSheaf X d) u)))
    complementRationalHypercohomologyAddEquivGlobalSections X ((Ω : Set (ComplexPoint X))ᶜ) 1
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
          CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)) =
    HomologicalComplex.homologyMap
      (globalRawComplementToDerivedPushforwardInt X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl) 1
      (HomologicalComplex.homologyMap (openRawToIntrinsicComplement X Ω) 1
        (ChernWinding.openRawRationalWindingClass (TopCat.of (ComplexPoint X)) Ω
          (holomorphicUnitFunction X d Ω u) (holomorphicUnitFunction_ne_zero X d Ω u))) := by
  dsimp only
  rw [complementRationalHypercohomology_restrictedSingularOneCocycle_eq_rawWinding,
    openRawToComplementResolutionOnOpen_eq_intrinsic, HomologicalComplex.homologyMap_comp]
  rfl
end AlgebraicGeometry.ComplexPoint
