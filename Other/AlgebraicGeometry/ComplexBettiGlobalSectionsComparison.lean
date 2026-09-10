/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiGlobalSectionsComparison
public import Other.AlgebraicGeometry.ExplicitEllipticCurveDeRhamClass
public import Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import Other.AlgebraicGeometry.ProjectiveAnalytificationParacompact
public import Other.AlgebraicTopology.SingularSubdivisionCochainSheafComplex

/-!
# Complex Betti cohomology and global sections

This is the complex-coefficient specialization of the singular-cochain resolution and
global-sections comparison.  It identifies complex constant-sheaf cohomology, analytic de Rham
cohomology, and ordinary singular cohomology with complex coefficients.  The final definitions
transport the explicit nonzero elliptic differential to a named nonzero singular cohomology
class.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The complex constant-sheaf comparison with the integer-indexed singular-cochain
resolution. -/
def complexToSingularCochainComplexInt :
    constantComplexSheafComplexInt X ⟶
      singularCochainSheafComplexInt X ℂ :=
  constantsToSingularCochainComplexInt X ℂ

/-- The complex constant-to-singular comparison is a quasi-isomorphism on a smooth
complex-point space. -/
lemma complexToSingularCochainComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (complexToSingularCochainComplexInt X) := by
  change QuasiIso (constantsToSingularCochainComplexInt X ℂ)
  exact constantsToSingularCochainComplexInt_quasiIso X ℂ

/-- Hypercohomology of the integer-indexed complex singular-cochain sheaf complex. -/
abbrev ComplexSingularCochainHypercohomology (n : ℤ) : Type 1 :=
  Hypercohomology X (singularCochainSheafComplexInt X ℂ) n

/-- Complex constant-sheaf cohomology is canonically equivalent to hypercohomology of the
singular-cochain resolution. -/
def complexCohomologySingularCochainEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ComplexConstantCohomology X n ≃
      ComplexSingularCochainHypercohomology X n :=
  Localization.SmallShiftedHom.postcompEquiv
    (complexToSingularCochainComplexInt X)
    (complexToSingularCochainComplexInt_quasiIso X)

/-- Every integer-indexed term of the complex singular-cochain resolution is flasque on a
hereditarily paracompact Hausdorff complex-point space. -/
theorem complexSingularCochainSheafComplexInt_isFlasque
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((singularCochainSheafComplexInt X ℂ).X n) := by
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    let e := (AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
      (TopCat.of (ComplexPoint X))).extendXIso
        ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
          (TopCat.of (ComplexPoint X))).X m).obj := by
      change TopCat.Sheaf.IsFlasque
        (AlgebraicTopology.Singular.singularCochainSheaf ℂ
          (TopCat.of (ComplexPoint X)) m)
      infer_instance
    change TopCat.Presheaf.IsFlasque
      ((singularCochainSheafComplexInt X ℂ).X (m : ℤ)).obj
    exact @AlgebraicTopology.Singular.presheaf_isFlasque_of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapIso e.symm) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact (AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
      (TopCat.of (ComplexPoint X))).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)

/-- Taking global sections commutes with extending the complex singular-cochain sheaf complex
from natural-number to integer degrees. -/
def globalSectionsComplexSingularCochainComplexIntIsoExtend :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℂ) ≅
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ
        (TopCat.of (ComplexPoint X))).extend
          ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let K := AlgebraicTopology.Singular.singularCochainSheafComplex ℂ Y
  let : F.Additive := by dsimp [F]; infer_instance
  let : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  exact HomologicalComplex.mapExtendIso G K ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
      ((Functor.mapHomologicalComplexCompIso eComp (ComplexShape.up ℕ)).app K).symm

/-- Under the precise K-injective resolution hypotheses, complex singular-cochain
hypercohomology is the homology of its global-section complex. -/
def complexSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℂ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    ComplexSingularCochainHypercohomology X n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℂ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let S := singularCochainSheafComplexInt X ℂ
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle X
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) e.inv := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let e₁ := Localization.SmallShiftedHom.postcompEquiv
    (X := A) (Y := S) (Z := I) (a := n) i hi
  let e₂ := Localization.SmallShiftedHom.precompEquiv
    (X := A') (Y := A) (Z := I) (a := n) e.inv he
  let e₃ := (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
    (K := A') (L := I) (n := n)).symm
  let e₄ := (CochainComplex.HomComplex.homologyAddEquiv A' I n).symm.toEquiv
  let e₅ := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I) n)
      |>.addCommGroupIsoToAddEquiv.toEquiv
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := inferInstance
  let e₆ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n)).symm
      |>.addCommGroupIsoToAddEquiv.toEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

/-- On a hereditarily paracompact Hausdorff complex-point space, complex singular-cochain
hypercohomology is computed by global sections. -/
def complexSingularCochainHypercohomologyEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    ComplexSingularCochainHypercohomology X n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℂ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℂ
  let : S.IsStrictlyGE 0 := by
    dsimp [S, singularCochainSheafComplexInt]
    infer_instance
  let hres := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 0
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
  have hSflasque : ∀ q, (S.X q).IsFlasque :=
    fun q ↦ complexSingularCochainSheafComplexInt_isFlasque X q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact complexSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    X I i n

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular.HereditarilyParacompact

/-- On a paracompact Hausdorff space, ordinary complex singular cohomology is the cohomology
of the global-section complex of the singular-cochain sheaf resolution. -/
def ordinaryComplexSingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    AlgebraicTopology.Singular.OrdinarySingularCohomology ℂ Y n ≃+
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y).homology n := by
  let := AlgebraicTopology.Singular.HereditarilyParacompact.topOpenToGlobalSingularCochainSheafComplex_quasiIso_complex
    (Y := Y)
  exact
    AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℂ Y n |>.trans <|
      (asIso (HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ Y) n))
          |>.addCommGroupIsoToAddEquiv

/-- The repository's complex singular cohomology is the cohomology of the global-section
complex of the complex singular-cochain sheaf resolution. -/
def complexSingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℂ Y n ≃+
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y).homology n :=
  (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivCohomology ℂ Y n).symm.toAddEquiv
    |>.trans (ordinaryComplexSingularCohomologyEquivGlobalSections Y n)

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- Hypercohomology of the complex singular-cochain resolution is ordinary complex singular
cohomology. -/
def complexSingularCochainHypercohomologyEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ComplexSingularCochainHypercohomology X (n : ℤ) ≃
      AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  exact (complexSingularCochainHypercohomologyEquivGlobalSections
      X (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsComplexSingularCochainComplexIntIsoExtend X)
        (n : ℤ)).addCommGroupIsoToAddEquiv.toEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv.toEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.complexSingularCohomologyEquivGlobalSections
          Y n).symm.toEquiv

/-- Complex constant-sheaf cohomology agrees with ordinary complex singular cohomology. -/
def complexCohomologyEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ComplexConstantCohomology X (n : ℤ) ≃
      AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint X)) n :=
  (complexCohomologySingularCochainEquiv X (n : ℤ)).trans
    (complexSingularCochainHypercohomologyEquivCohomology X n)

/-- Analytic de Rham cohomology agrees with ordinary complex singular cohomology. -/
def deRhamCohomologyEquivComplexSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    DeRhamHypercohomology X (n : ℤ) ≃
      AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint X)) n :=
  (complexConstantCohomologyDeRhamEquiv X inferInstance (n : ℤ)).symm.trans
    (complexCohomologyEquivSingularCohomology X n)

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance curveVariety_smoothForComplexBetti : Smooth curveVariety.hom :=
  SmoothOfRelativeDimension.smooth 1 curveVariety.hom

/-- The ordinary complex singular cohomology class represented by the explicit invariant
elliptic differential. -/
def curveComplexSingularClass :
    AlgebraicTopology.Singular.Cohomology ℂ
      (TopCat.of (ComplexPoint curveVariety)) 1 :=
  let : ∀ U : Opens (ComplexPoint curveVariety), ParacompactSpace U :=
    ComplexPoint.openParacompactSpace curveVariety
  deRhamCohomologyEquivComplexSingularCohomology curveVariety 1
      (filteredToDeRhamCohomology curveVariety 1 1 curveTopFilteredClass) -
    deRhamCohomologyEquivComplexSingularCohomology curveVariety 1 0

/-- The explicit invariant elliptic differential gives a nonzero class in ordinary singular
cohomology with complex coefficients. -/
theorem curveComplexSingularClass_ne_zero : curveComplexSingularClass ≠ 0 := by
  let : ∀ U : Opens (ComplexPoint curveVariety), ParacompactSpace U :=
    ComplexPoint.openParacompactSpace curveVariety
  intro h
  apply curveTopFilteredClass_toDeRham_ne_zero
  apply (deRhamCohomologyEquivComplexSingularCohomology curveVariety 1).injective
  exact sub_eq_zero.mp h

end AlgebraicGeometry.ExplicitEllipticCandidate
