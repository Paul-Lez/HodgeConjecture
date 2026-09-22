/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Other.AlgebraicGeometry.BettiGlobalSectionsAdditivity
public import Other.AlgebraicGeometry.ProjectiveSpaceSmooth
public import Other.AlgebraicTopology.ExplicitCochainClass
public import HodgeConjecture.Definitions.AlgebraicGeometry.ReducedSmoothStratification
public import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersionComplexPoint
public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The explicit hyperplane in complex projective two-space

This file records the scheme-theoretic zero locus of the first homogeneous coordinate.  The
cohomological part starts with the elementary three-cell calculation for projective two-space in
singular cohomology.  The repository's Betti comparison then transports that class to its
constant-sheaf hypercohomology model.  No general cycle-class/Chern-class theorem is used here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MvPolynomial AlgebraicGeometry HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane

open AlgebraicGeometry.ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard grading on the homogeneous coordinate ring of `ℙ²_ℂ`. -/
abbrev Grading : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ) :=
  homogeneousSubmodule (Fin 3) ℂ

/-- The first homogeneous coordinate. -/
def coordinateZero : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0

lemma coordinateZero_homogeneous : coordinateZero.IsHomogeneous 1 := by
  exact MvPolynomial.isHomogeneous_X ℂ 0

/-- The projective plane as `Proj` of the standard graded complex polynomial ring. -/
def plane : Scheme := Proj Grading

/-- The degree-zero part of the grading is identified with `ℂ`. -/
def degreeZeroIso : CommRingCat.of (Grading 0) ≅ CommRingCat.of ℂ :=
  RingEquiv.toCommRingCatIso (ProjectiveSpace.degreeZeroEquiv (Fin 3) ℂ)

/-- The structure morphism of the projective plane over `Spec ℂ`. -/
def structureMap : plane ⟶ Spec ↧ℂ :=
  Proj.toSpecZero Grading ≫ Scheme.Spec.map degreeZeroIso.symm.hom.op

/-- The projective plane regarded as an object over `Spec ℂ`, as required by the cohomology API. -/
def planeOver : Over (Spec ↧ℂ) := Over.mk structureMap

/-- The direct `Proj` model of the projective plane is proper over `Spec ℂ`.

This is recorded separately from the repository's stronger `IsProjective` class: the latter
also asks for a chosen presentation as a closed immersion into the pullback-model projective
space. -/
noncomputable instance plane_proper : IsProper structureMap := by
  change IsProper (Proj.toSpecZero Grading ≫ Scheme.Spec.map degreeZeroIso.symm.hom.op)
  letI : MorphismProperty.RespectsIso (@IsProper) := inferInstance
  apply (MorphismProperty.cancel_right_of_respectsIso
    (@IsProper) (Proj.toSpecZero Grading)
    (Scheme.Spec.map degreeZeroIso.symm.hom.op)).mpr
  letI : Algebra.FiniteType (Grading 0) (MvPolynomial (Fin 3) ℂ) :=
    ProjectiveSpace.degreeZeroFiniteType (Fin 3) ℂ
  infer_instance

noncomputable instance planeOver_proper : IsProper planeOver.hom := plane_proper

/-- The direct `Proj` presentation of `ℙ²_ℂ` is smooth of relative dimension two. -/
noncomputable instance plane_smoothOfRelativeDimension : SmoothOfRelativeDimension 2 structureMap := by
  change SmoothOfRelativeDimension 2
    (Proj.toSpecZero Grading ≫ Scheme.Spec.map degreeZeroIso.symm.hom.op)
  letI : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 2) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 2).respectsIso
  apply (MorphismProperty.cancel_right_of_respectsIso
    (@SmoothOfRelativeDimension 2)
    (Proj.toSpecZero Grading)
    (Scheme.Spec.map degreeZeroIso.symm.hom.op)).mpr
  exact Other.ProjectiveChart.smoothOfRelativeDimension_toSpecZero (N := 2) ℂ

noncomputable instance planeOver_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 2 planeOver.hom := plane_smoothOfRelativeDimension

noncomputable instance plane_smooth : Smooth structureMap :=
  SmoothOfRelativeDimension.smooth 2 structureMap

noncomputable instance planeOver_smooth : Smooth planeOver.hom :=
  SmoothOfRelativeDimension.smooth 2 planeOver.hom

/-! The direct Proj model is integral.  The reducedness proof is chartwise: each standard affine
chart is the degree-zero homogeneous localization of the polynomial domain, embedded in the usual
localization.  Irreducibility is witnessed by the relevant homogeneous prime `(0)`, which is a
generic point because specialization is inclusion of homogeneous ideals. -/

lemma away_isReduced {f : MvPolynomial (Fin 3) ℂ} :
    _root_.IsReduced (Away Grading f) := by
  by_cases hf : f = 0
  · subst f
    letI : Subsingleton (Away Grading 0) :=
      HomogeneousLocalization.subsingleton Grading (by simp)
    exact isReduced_of_subsingleton
  · letI : IsDomain (Localization.Away f) :=
      Localization.Away.isDomain hf
    letI : Nontrivial (Away Grading f) := by
      constructor
      refine ⟨0, 1, ?_⟩
      intro h
      have hv := congrArg HomogeneousLocalization.val h
      rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.val_one] at hv
      exact zero_ne_one hv
    letI : NoZeroDivisors (Away Grading f) := by
      constructor
      intro a b hab
      have hv := congrArg HomogeneousLocalization.val hab
      rw [HomogeneousLocalization.val_mul] at hv
      letI : NoZeroDivisors (Localization.Away f) := inferInstance
      have hv' : HomogeneousLocalization.val a * HomogeneousLocalization.val b = 0 := by
        simpa only [HomogeneousLocalization.val_zero] using hv
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hv' with ha | hb
      · left
        apply HomogeneousLocalization.val_injective (Submonoid.powers f)
        simpa [HomogeneousLocalization.val_zero] using ha
      · right
        apply HomogeneousLocalization.val_injective (Submonoid.powers f)
        simpa [HomogeneousLocalization.val_zero] using hb
    exact inferInstance

noncomputable instance plane_isReduced : IsReduced plane := by
  let 𝒰 := (Proj.affineOpenCover Grading).openCover
  letI : ∀ i : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X i) := by
    intro i
    change AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (Away Grading (i.2 : MvPolynomial (Fin 3) ℂ))))
    rw [affine_isReduced_iff]
    exact away_isReduced
  exact AlgebraicGeometry.IsReduced.of_openCover plane 𝒰

noncomputable instance plane_irreducible : IrreducibleSpace plane := by
  change IrreducibleSpace (ProjectiveSpectrum Grading)
  let x₀ : ProjectiveSpectrum Grading :=
    { asHomogeneousIdeal := ⊥
      isPrime := Ideal.isPrime_bot
      not_irrelevant_le := by
        intro h
        have hX := h (show coordinateZero ∈ HomogeneousIdeal.irrelevant Grading by
          rw [HomogeneousIdeal.mem_irrelevant_iff]
          rw [GradedRing.proj_apply]
          exact DirectSum.decompose_of_mem_ne Grading (i := 1) (j := 0)
            ((MvPolynomial.mem_homogeneousSubmodule 1 coordinateZero).2
              coordinateZero_homogeneous) (by decide))
        exact MvPolynomial.X_ne_zero 0 (show coordinateZero = 0 from hX) }
  letI : PreirreducibleSpace (ProjectiveSpectrum Grading) :=
    (preirreducibleSpace_iff_open_dense (ProjectiveSpectrum Grading)).2 (by
      intro U hU hUn
      have hxU : x₀ ∈ U := by
        by_contra hx
        have hclosed : closure ({x₀} : Set (ProjectiveSpectrum Grading)) ⊆ Uᶜ :=
          closure_minimal (Set.singleton_subset_iff.mpr hx) hU.isClosed_compl
        have hall : (Set.univ : Set (ProjectiveSpectrum Grading)) ⊆ Uᶜ := by
          intro y _
          have hxy : x₀ ≤ y := by
            change (⊥ : HomogeneousIdeal Grading) ≤ y.asHomogeneousIdeal
            exact bot_le
          exact hclosed ((ProjectiveSpectrum.le_iff_mem_closure Grading x₀ y).mp hxy)
        obtain ⟨y, hy⟩ := hUn
        exact (hall trivial) hy
      rw [dense_iff_closure_eq]
      apply Set.Subset.antisymm (Set.subset_univ _)
      intro y _
      have hxy : x₀ ≤ y := by
        change (⊥ : HomogeneousIdeal Grading) ≤ y.asHomogeneousIdeal
        exact bot_le
      exact closure_mono (Set.singleton_subset_iff.mpr hxU)
        ((ProjectiveSpectrum.le_iff_mem_closure Grading x₀ y).mp hxy))
  exact IrreducibleSpace.mk ⟨x₀⟩

noncomputable instance plane_integral : IsIntegral plane :=
  isIntegral_of_irreducibleSpace_of_isReduced plane

noncomputable instance planeOver_integral : IsIntegral planeOver.left := by
  change IsIntegral plane
  infer_instance

/-- The explicit homogeneous zero locus `{X₀ = 0}` in the projective spectrum. -/
def hyperplaneLocus : Set (ProjectiveSpectrum Grading) :=
  ProjectiveSpectrum.zeroLocus Grading {coordinateZero}

/-- The standard open complement of the displayed zero locus. -/
def hyperplaneComplementOpen : plane.Opens :=
  Proj.basicOpen Grading coordinateZero

/-- The complement of `{X₀ = 0}` is literally the standard principal open `D₊(X₀)`.

This is a statement about the actual projective-spectrum zero locus, prior to any use of
cohomology or a cycle-class comparison. -/
lemma hyperplaneComplementOpen_eq_compl :
    (hyperplaneComplementOpen : Set plane) = hyperplaneLocusᶜ := by
  exact ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl Grading coordinateZero

@[simp]
lemma mem_hyperplaneLocus_iff (x : ProjectiveSpectrum Grading) :
    x ∈ hyperplaneLocus ↔ coordinateZero ∈ x.asHomogeneousIdeal := by
  simp [hyperplaneLocus]

/-- The closed subset underlying the scheme-theoretic hyperplane. -/
def hyperplaneClosed : TopologicalSpace.Closeds plane where
  carrier := hyperplaneLocus
  isClosed' := ProjectiveSpectrum.isClosed_zeroLocus Grading {coordinateZero}

/-- The reduced closed subscheme cut out by the equation `X₀`. -/
def hyperplane : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subscheme

/- The zero-locus construction is the reduced closed subscheme attached to the displayed
   closed set. -/
noncomputable instance hyperplane_isReduced : IsReduced hyperplane := by
  change IsReduced
    (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subscheme
  exact reducedClosedSubscheme_isReduced hyperplaneClosed

/-! The homogeneous prime `(X₀)` is the generic point of the ambient zero locus.  We keep this
    point in the ambient `ProjectiveSpectrum` for now; identifying it with the generic point of
    the subscheme `hyperplane` still requires the scheme-theoretic comparison below. -/

noncomputable def hyperplaneAmbientGenericPoint : ProjectiveSpectrum Grading :=
  { asHomogeneousIdeal :=
      ⟨Ideal.span {coordinateZero}, by
        exact Ideal.homogeneous_span Grading _ (by
          intro x hx
          rcases Set.mem_singleton_iff.mp hx with rfl
          exact ⟨1, coordinateZero_homogeneous⟩)⟩
    isPrime := by
      change (Ideal.span {coordinateZero} : Ideal (MvPolynomial (Fin 3) ℂ)).IsPrime
      rw [Ideal.span_singleton_prime (by exact MvPolynomial.X_ne_zero 0)]
      exact MvPolynomial.X_prime
    not_irrelevant_le := by
      intro h
      let e : MvPolynomial (Fin 3) ℂ →+* ℂ :=
        MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun i : Fin 3 => if i = 1 then 1 else 0)
      have hX1 : MvPolynomial.X 1 ∉
          (Ideal.span {coordinateZero} : Ideal (MvPolynomial (Fin 3) ℂ)) := by
        intro hX1
        have hmap : e (MvPolynomial.X 1) ∈
            Ideal.map e (Ideal.span {coordinateZero}) :=
          Ideal.mem_map_of_mem e hX1
        have hle : Ideal.map e (Ideal.span {coordinateZero}) ≤
            Ideal.span ({e coordinateZero} : Set ℂ) := by
          rw [Ideal.map_le_iff_le_comap]
          exact Ideal.span_le.mpr (by
            intro x hx
            rcases Set.mem_singleton_iff.mp hx with rfl
            exact Ideal.subset_span (Set.mem_singleton (e coordinateZero)))
        have he : e (MvPolynomial.X 1) ∈
            Ideal.span ({e coordinateZero} : Set ℂ) := hle hmap
        simpa [e, coordinateZero] using he
      have hmem : MvPolynomial.X 1 ∈ HomogeneousIdeal.irrelevant Grading := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
        exact DirectSum.decompose_of_mem_ne Grading (i := 1) (j := 0)
          ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X 1)).2
            (MvPolynomial.isHomogeneous_X ℂ 1)) (by decide)
      exact hX1 (h hmem) }

lemma hyperplaneAmbientGenericPoint_mem :
    hyperplaneAmbientGenericPoint ∈ hyperplaneLocus := by
  rw [hyperplaneLocus, ProjectiveSpectrum.mem_zeroLocus]
  exact Set.singleton_subset_iff.mpr (Ideal.subset_span (Set.mem_singleton coordinateZero))

lemma closure_hyperplaneAmbientGenericPoint :
    closure ({hyperplaneAmbientGenericPoint} :
      Set (ProjectiveSpectrum Grading)) = hyperplaneLocus := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure
    Grading {hyperplaneAmbientGenericPoint}]
  rw [ProjectiveSpectrum.vanishingIdeal_singleton]
  change ProjectiveSpectrum.zeroLocus Grading
    (Ideal.span {coordinateZero} : Set (MvPolynomial (Fin 3) ℂ)) = hyperplaneLocus
  rw [ProjectiveSpectrum.zeroLocus_span]
  rfl

/-- The closed immersion of the explicit hyperplane into `ℙ²`. -/
def hyperplaneι : hyperplane ⟶ plane :=
  (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeι

instance : IsClosedImmersion hyperplaneι := by
  change IsClosedImmersion
    ((Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeι)
  infer_instance

/-- The explicit hyperplane, regarded as a scheme over `Spec ℂ`. -/
def hyperplaneOver : Over (Spec ↧ℂ) :=
  Over.mk (hyperplaneι ≫ structureMap)

/-- The zero locus `{X₀ = 0}` as a closed immersion over the explicit projective plane. -/
def hyperplaneOverι : hyperplaneOver ⟶ planeOver :=
  Over.homMk hyperplaneι rfl

instance : IsClosedImmersion hyperplaneOverι.left := by
  change IsClosedImmersion hyperplaneι
  infer_instance

@[simp]
lemma range_hyperplaneι : Set.range hyperplaneι = hyperplaneLocus := by
  change Set.range
    ((Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeι) = hyperplaneLocus
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- On complex points, the analytic open `D₊(X₀)` is exactly the complement of the actual
analytic image of the closed immersion cut out by `X₀`.

Thus the support occurring in relative singular cohomology is the support of the displayed
scheme-theoretic zero locus, not merely the zero set of a separately chosen analytic function. -/
lemma hyperplaneComplementOpen_eq_compl_range_complexPoint :
    Point.overOpen (X := planeOver) hyperplaneComplementOpen =
      (Set.range (Point.map hyperplaneOverι))ᶜ := by
  rw [ComplexPoint.range_map_of_closedImmersion hyperplaneOverι]
  ext z
  change z.underlying ∈ hyperplaneComplementOpen ↔ z.underlying ∉ Set.range hyperplaneι
  rw [range_hyperplaneι]
  change z.underlying ∈ (hyperplaneComplementOpen : Set plane) ↔
    z.underlying ∉ hyperplaneLocus
  rw [hyperplaneComplementOpen_eq_compl]
  rfl

/-- Degree-two rational cohomology of the explicit projective plane. -/
abbrev H2 := H^2(planeOver; ℚ)

/-- Degree-two rational singular cohomology of the analytic projective plane. -/
abbrev SingularH2 : Type :=
  AlgebraicTopology.Singular.Cohomology ℚ
    (TopCat.of (ComplexPoint planeOver)) 2

/-- The raw degree-two singular cochains of the analytic projective plane. -/
abbrev SingularCochain2 : Type :=
  ((AlgebraicTopology.Singular.singularChainComplex ℚ
    (TopCat.of (ComplexPoint planeOver))).linearDualCochainComplex).X 2

/-- A literal closed singular two-cochain determines a degree-two singular cohomology class.
This is the entry point for the explicitly constructed hyperplane cocycle. -/
def singularClassOfCochain (φ : SingularCochain2)
    (hφ : ((AlgebraicTopology.Singular.singularChainComplex ℚ
      (TopCat.of (ComplexPoint planeOver))).linearDualCochainComplex).d 2 3 φ = 0) :
    SingularH2 :=
  AlgebraicTopology.Singular.singularCohomologyClassOfCochain ℚ
    (TopCat.of (ComplexPoint planeOver)) 2 φ hφ

/-- The elementary cellular cochain complex for the middle cell of `ℂP²`.

The usual cell structure has one cell in dimensions `0`, `2`, and `4`.  Only the middle
summand is needed for the degree-two calculation, and it is represented by the cochain complex
concentrated in degree `2` with value `ℚ` and zero differential.

This is a manual model, not yet a theorem identifying it with singular cohomology. -/
noncomputable abbrev cellularTwoCellComplex : CochainComplex (ModuleCat ℚ) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℚ) (2 : ℤ)).obj (ModuleCat.of ℚ ℚ)

/-- Degree-two cohomology of the middle-cell model. -/
abbrev cellularTwoCellCohomology : Type :=
  (cellularTwoCellComplex).homology 2

/-- The direct calculation that the middle-cell model has one rational generator. -/
noncomputable def cellularTwoCellEquiv : cellularTwoCellCohomology ≃ₗ[ℚ] ℚ :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (2 : ℤ)
    (ModuleCat.of ℚ ℚ)).toLinearEquiv

/-- The unit of the middle-cell model, representing the hyperplane cell. -/
noncomputable def cellularHyperplaneClass : cellularTwoCellCohomology :=
  cellularTwoCellEquiv.symm 1

/-- The hand calculation in the cellular model: the hyperplane cell spans degree two. -/
lemma span_cellularHyperplaneClass_eq_top :
    Submodule.span ℚ {cellularHyperplaneClass} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff ℚ]
  intro α
  obtain ⟨q, rfl⟩ := cellularTwoCellEquiv.symm.surjective α
  refine ⟨q, ?_⟩
  change q • cellularTwoCellEquiv.symm 1 = cellularTwoCellEquiv.symm q
  rw [← cellularTwoCellEquiv.symm.map_smul]
  simp

/-- A concrete comparison from the hand-built cellular calculation to singular cohomology.

The class is constructed on the singular side first.  Supplying this equivalence is the
remaining computation of the cellular model with the actual analytic space; it is independent of
the sheaf/hypercohomology comparison below. -/
structure SingularH2CellularComparison where
  cellularToSingular : cellularTwoCellCohomology ≃ₗ[ℚ] SingularH2

/-- The normalized class in degree-two singular cohomology. -/
def singularHyperplaneClass (c : SingularH2CellularComparison) : SingularH2 :=
  c.cellularToSingular cellularHyperplaneClass

/-- Once the cellular model is identified with singular cohomology, the explicit class spans the
degree-two singular cohomology group. -/
lemma span_singularHyperplaneClass_eq_top (c : SingularH2CellularComparison) :
    Submodule.span ℚ {singularHyperplaneClass c} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff ℚ]
  intro α
  obtain ⟨β, rfl⟩ := c.cellularToSingular.surjective α
  obtain ⟨q, rfl⟩ := cellularTwoCellEquiv.symm.surjective β
  refine ⟨q, ?_⟩
  change q • c.cellularToSingular cellularHyperplaneClass = c.cellularToSingular
    (cellularTwoCellEquiv.symm q)
  rw [← c.cellularToSingular.map_smul]
  change c.cellularToSingular (q • cellularTwoCellEquiv.symm 1) = _
  rw [← cellularTwoCellEquiv.symm.map_smul]
  simp

/-- The Betti comparison for the direct `Proj` plane, using its already formalized smooth
relative dimension `2`.  No integrality presentation is needed for this comparison. -/
def planeBettiComparison_of_smoothOfRelativeDimension
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    H2 ≃ SingularH2 :=
  AlgebraicGeometry.ComplexPoint.rationalCohomologyEquivSingularCohomology_of_smoothOfRelativeDimension
    planeOver 2 2

/-- Move any literal closed singular two-cochain on the direct projective plane to its
constant-sheaf hypercohomology model using the dimension-specific comparison. -/
def hypercohomologyClassOfCochain_of_smoothOfRelativeDimension
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U]
    (φ : SingularCochain2)
    (hφ : ((AlgebraicTopology.Singular.singularChainComplex ℚ
      (TopCat.of (ComplexPoint planeOver))).linearDualCochainComplex).d 2 3 φ = 0) : H2 :=
  (planeBettiComparison_of_smoothOfRelativeDimension).symm (singularClassOfCochain φ hφ)

/-- The canonical rational Betti comparison for the explicit plane, when the standard geometric
and topological hypotheses needed by the comparison theorem are available. -/
def planeBettiComparison
    [IsIntegral planeOver.left] [Smooth planeOver.hom]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    H2 ≃ₗ[ℚ] SingularH2 :=
  AlgebraicGeometry.ComplexPoint.rationalCohomologyLinearEquivSingularCohomology
    planeOver 2

/-- Move a class represented by an explicit closed singular two-cochain into the constant-sheaf
hypercohomology model. -/
def hypercohomologyClassOfCochain
    [IsIntegral planeOver.left] [Smooth planeOver.hom]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U]
    (φ : SingularCochain2)
    (hφ : ((AlgebraicTopology.Singular.singularChainComplex ℚ
      (TopCat.of (ComplexPoint planeOver))).linearDualCochainComplex).d 2 3 φ = 0) : H2 :=
  (planeBettiComparison).symm (singularClassOfCochain φ hφ)

/-- The singular class transported to the repository's hypercohomology model. -/
def hyperplaneClass
    (c : SingularH2CellularComparison)
    [IsIntegral planeOver.left] [Smooth planeOver.hom]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] : H2 :=
  (planeBettiComparison).symm (singularHyperplaneClass c)

@[simp]
lemma planeBettiComparison_hyperplaneClass
    (c : SingularH2CellularComparison)
    [IsIntegral planeOver.left] [Smooth planeOver.hom]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    planeBettiComparison (hyperplaneClass c) = singularHyperplaneClass c := by
  simp [hyperplaneClass]

set_option maxRecDepth 10000 in
/-- The transported explicit class spans the repository's degree-two hypercohomology group. -/
lemma span_hyperplaneClass_eq_top
    (c : SingularH2CellularComparison)
    [IsIntegral planeOver.left] [Smooth planeOver.hom]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    Submodule.span ℚ {hyperplaneClass c} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff ℚ]
  intro α
  obtain ⟨β, rfl⟩ := (planeBettiComparison).symm.surjective α
  obtain ⟨γ, rfl⟩ := c.cellularToSingular.surjective β
  obtain ⟨q, rfl⟩ := cellularTwoCellEquiv.symm.surjective γ
  refine ⟨q, ?_⟩
  let e : H2 ≃ₗ[ℚ] SingularH2 := planeBettiComparison
  change q • e.symm (c.cellularToSingular cellularHyperplaneClass) =
    e.symm (c.cellularToSingular (cellularTwoCellEquiv.symm q))
  rw [← e.symm.map_smul, ← c.cellularToSingular.map_smul]
  change e.symm (c.cellularToSingular
    (q • cellularTwoCellEquiv.symm 1)) = _
  rw [← cellularTwoCellEquiv.symm.map_smul]
  simp

end AlgebraicGeometry.ProjectivePlane
