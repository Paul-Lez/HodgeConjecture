/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiGlobalSectionsComparison
public import Other.AlgebraicGeometry.HolomorphicIntegralHodgeClass

/-!
# Constant-sheaf cohomology with arbitrary coefficients and singular cohomology

The rational comparison of `BettiSheafComparison` and `BettiGlobalSectionsComparison` uses no
property of `ℚ` beyond its ring structure once the singular-cochain machinery is stated over a
commutative ring. This file records the comparison for an arbitrary coefficient ring `R`:
hypercohomology of the constant sheaf `R` on the analytic space of a smooth complex scheme
is the homology of the algebraic-dual singular cochain complex with coefficients in `R`.

The case `R = ℤ` identifies `IntegralCohomology` with integral singular cohomology. The target
is `OrdinarySingularCohomology`, the homology of the dual cochain complex; the further
identification with the dual of homology is a universal-coefficient statement valid only over a
field and is not used here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (R : Type) [CommRing R]

/-- Hypercohomology of the constant sheaf with coefficients in `R`, presented through the
integer-indexed constant coefficient complex. -/
abbrev ScalarCohomology (n : ℤ) : Type 1 :=
  Hypercohomology X (constantCoefficientSheafComplexInt X R) n

/-- Hypercohomology of the integer-indexed singular-cochain sheaf complex with coefficients
in `R`. -/
abbrev ScalarSingularCochainHypercohomology (n : ℤ) : Type 1 :=
  Hypercohomology X (singularCochainSheafComplexInt X R) n

/-- Constant-sheaf cohomology is canonically equivalent to the hypercohomology of its
singular-cochain resolution. -/
def scalarCohomologySingularCochainEquiv [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ScalarCohomology X R n ≃ ScalarSingularCochainHypercohomology X R n :=
  Localization.SmallShiftedHom.postcompEquiv
    (constantsToSingularCochainComplexInt X R)
    (constantsToSingularCochainComplexInt_quasiIso X R)

lemma scalarCohomologySingularCochainEquiv_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ScalarCohomology X R n) :
    scalarCohomologySingularCochainEquiv X R n α =
      hypercohomologyMap X (constantsToSingularCochainComplexInt X R) n α :=
  rfl

/-- Every integer-indexed term of the singular-cochain resolution with coefficients in `R` is
flasque on a hereditarily paracompact Hausdorff complex-point space. -/
theorem singularCochainSheafComplexInt_isFlasque_scalar
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((singularCochainSheafComplexInt X R).X n) := by
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    let e := (AlgebraicTopology.Singular.singularCochainSheafComplex R
      (TopCat.of (ComplexPoint X))).extendXIso
        ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque
        ((AlgebraicTopology.Singular.singularCochainSheafComplex R
          (TopCat.of (ComplexPoint X))).X m).obj := by
      change TopCat.Sheaf.IsFlasque
        (AlgebraicTopology.Singular.singularCochainSheaf R
          (TopCat.of (ComplexPoint X)) m)
      infer_instance
    change TopCat.Presheaf.IsFlasque
      ((singularCochainSheafComplexInt X R).X (m : ℤ)).obj
    exact @AlgebraicTopology.Singular.presheaf_isFlasque_of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapIso e.symm) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact (AlgebraicTopology.Singular.singularCochainSheafComplex R
      (TopCat.of (ComplexPoint X))).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections commutes with extending the natural-number-indexed singular-cochain
sheaf complex by zero to integer degrees. -/
def globalSectionsSingularCochainComplexIntIsoExtend_scalar :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X R) ≅
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex R
        (TopCat.of (ComplexPoint X))).extend
          ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let K := AlgebraicTopology.Singular.singularCochainSheafComplex R Y
  let : F.Additive := by dsimp [F]; infer_instance
  let : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  exact HomologicalComplex.mapExtendIso G K ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
      ((Functor.mapHomologicalComplexCompIso eComp (ComplexShape.up ℕ)).app K).symm

/-- Hypercohomology of the singular-cochain resolution is the homology of its own
global-section complex, given a K-injective resolution that remains a quasi-isomorphism after
taking global sections. -/
def scalarSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : singularCochainSheafComplexInt X R ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    ScalarSingularCochainHypercohomology X R n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X R)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let S := singularCochainSheafComplexInt X R
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

/-- On a hereditarily paracompact Hausdorff complex-point space, hypercohomology of the
singular-cochain resolution with coefficients in `R` is computed by its global-section
complex. -/
def scalarSingularCochainHypercohomologyEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    ScalarSingularCochainHypercohomology X R n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X R)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X R
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
    fun q ↦ singularCochainSheafComplexInt_isFlasque_scalar X R q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact scalarSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    X R I i n

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular.HereditarilyParacompact

/-- On a paracompact Hausdorff space, ordinary singular cohomology with coefficients in `R` is
the cohomology of the global-section complex of the singular-cochain sheaf resolution. -/
def ordinaryScalarSingularCohomologyEquivGlobalSections
    (R : Type) [CommRing R] (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    AlgebraicTopology.Singular.OrdinarySingularCohomology R Y n ≃+
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex R Y).homology n := by
  let := AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso R
    (Y := Y)
  exact
    AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw R Y n |>.trans <|
      (asIso (HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex R Y) n))
          |>.addCommGroupIsoToAddEquiv

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (R : Type) [CommRing R]

/-- On a hereditarily paracompact Hausdorff complex-point space, hypercohomology of the
singular-cochain resolution with coefficients in `R` is ordinary singular cohomology with
coefficients in `R`. -/
def scalarSingularCochainHypercohomologyEquivOrdinaryCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ScalarSingularCochainHypercohomology X R (n : ℤ) ≃
      AlgebraicTopology.Singular.OrdinarySingularCohomology R
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex R Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  exact (scalarSingularCochainHypercohomologyEquivGlobalSections
      X R (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtend_scalar X R)
        (n : ℤ)).addCommGroupIsoToAddEquiv.toEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv.toEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryScalarSingularCohomologyEquivGlobalSections
          R Y n).symm.toEquiv

/-- On a smooth complex scheme whose analytification is hereditarily paracompact Hausdorff,
constant-sheaf cohomology with coefficients in `R` agrees with ordinary singular cohomology
with coefficients in `R`. -/
def scalarCohomologyEquivOrdinarySingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ScalarCohomology X R (n : ℤ) ≃
      AlgebraicTopology.Singular.OrdinarySingularCohomology R
        (TopCat.of (ComplexPoint X)) n :=
  (scalarCohomologySingularCochainEquiv X R (n : ℤ)).trans
    (scalarSingularCochainHypercohomologyEquivOrdinaryCohomology X R n)

/-- Integral constant-sheaf cohomology is integral singular cohomology, presented as the
homology of the integral dual singular cochain complex. -/
def integralCohomologyEquivOrdinarySingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    IntegralCohomology X (n : ℤ) ≃
      AlgebraicTopology.Singular.OrdinarySingularCohomology ℤ
        (TopCat.of (ComplexPoint X)) n :=
  scalarCohomologyEquivOrdinarySingularCohomology X ℤ n

end AlgebraicGeometry.ComplexPoint
