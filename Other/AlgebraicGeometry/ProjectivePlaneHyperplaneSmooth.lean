/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneCoordinateCharts
public import Other.AlgebraicGeometry.ProjectivePlanePresentation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smoothness of the coordinate hyperplane in the projective plane

The reduced closed subscheme `X₀ = 0` is covered by its intersections with `D₊(X₁)` and
`D₊(X₂)`.  On either chart its coordinate ring is the two-variable polynomial ring modulo
the first variable, hence a polynomial ring in one variable.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial AlgebraicGeometry HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HyperplaneSmooth

/-- Affineness of a standard projective chart. -/
def chartIsAffine (i : Fin 3) : IsAffineOpen (CoordinateCharts.chartOpen i) :=
  Proj.isAffineOpen_basicOpen Grading (X i)
    (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos

/-- The affine standard chart `D₊(Xᵢ)` of the direct projective-plane model. -/
abbrev chartAffineOpen (i : Fin 3) : plane.affineOpens :=
  ⟨CoordinateCharts.chartOpen i, chartIsAffine i⟩

/-- The chart coordinate ring, written as a polynomial ring in two variables. -/
def chartGlobalRingEquiv (i : Fin 3) :
    MvPolynomial (Fin 2) ℂ ≃+* Γ(plane, CoordinateCharts.chartOpen i) :=
  (Other.ProjectiveChart.chartRingEquiv ℂ i).trans
    (Proj.basicOpenIsoAway Grading (X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).commRingCatIsoToRingEquiv

/-- The equation `X₀/Xᵢ` on a chart on which `Xᵢ` is invertible. -/
def normalSection (i : Fin 3) : Γ(plane, CoordinateCharts.chartOpen i) :=
  (Proj.basicOpenIsoAway Grading (X i)
    (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom
      (Other.ProjectiveChart.gen ℂ i 0)

lemma chartGlobalRingEquiv_X_zero (i : Fin 3) (hi : i ≠ 0) :
    chartGlobalRingEquiv i (X 0) = normalSection i := by
  have hsucc : i.succAbove (0 : Fin 2) = 0 := by
    fin_cases i <;> simp_all
  change (Proj.basicOpenIsoAway Grading (X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom
        (Other.ProjectiveChart.chartRingEquiv ℂ i (X 0)) = _
  rw [Other.ProjectiveChart.chartRingEquiv_apply,
    Other.ProjectiveChart.chartHom_X]
  unfold normalSection
  rfl

lemma firstChart_zeroLocus_normalSection :
    (CoordinateCharts.chartOpen 1).toScheme.zeroLocus
        ({CoordinateCharts.firstNormalSection} :
          Set Γ((CoordinateCharts.chartOpen 1).toScheme, ⊤)) =
      (CoordinateCharts.chartOpen 1).ι ⁻¹'
      (hyperplaneClosed : Set plane) := by
  classical
  rw [Scheme.zeroLocus_singleton]
  ext y
  change y ∉ (CoordinateCharts.chartOpen 1).toScheme.basicOpen
      CoordinateCharts.firstNormalSection ↔
    (CoordinateCharts.chartOpen 1).ι y ∈ hyperplaneLocus
  rw [CoordinateCharts.firstNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen]
  rw [Scheme.Hom.mem_preimage]
  convert not_congr
    ((Set.ext_iff.mp hyperplaneComplementOpen_eq_compl
      ((CoordinateCharts.chartOpen 1).ι y)).trans
    (Set.mem_compl_iff hyperplaneLocus ((CoordinateCharts.chartOpen 1).ι y))) using 1 <;>
    simp [Classical.not_not] <;> rfl

lemma secondChart_zeroLocus_normalSection :
    (CoordinateCharts.chartOpen 2).toScheme.zeroLocus
        ({CoordinateCharts.secondNormalSection} :
          Set Γ((CoordinateCharts.chartOpen 2).toScheme, ⊤)) =
      (CoordinateCharts.chartOpen 2).ι ⁻¹'
      (hyperplaneClosed : Set plane) := by
  classical
  rw [Scheme.zeroLocus_singleton]
  ext y
  change y ∉ (CoordinateCharts.chartOpen 2).toScheme.basicOpen
      CoordinateCharts.secondNormalSection ↔
    (CoordinateCharts.chartOpen 2).ι y ∈ hyperplaneLocus
  rw [CoordinateCharts.secondNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen]
  rw [Scheme.Hom.mem_preimage]
  convert not_congr
    ((Set.ext_iff.mp hyperplaneComplementOpen_eq_compl
      ((CoordinateCharts.chartOpen 2).ι y)).trans
    (Set.mem_compl_iff hyperplaneLocus ((CoordinateCharts.chartOpen 2).ι y))) using 1 <;>
    simp [Classical.not_not] <;> rfl

lemma firstChart_fromSpec_preimage_hyperplaneComplementOpen :
    (chartIsAffine 1).fromSpec ⁻¹ᵁ hyperplaneComplementOpen =
      PrimeSpectrum.basicOpen (normalSection 1) := by
  let hU : IsAffineOpen (CoordinateCharts.chartOpen 1) := chartIsAffine 1
  change ((hU.isoSpec.inv ≫
      (CoordinateCharts.chartOpen 1).ι) ⁻¹ᵁ hyperplaneComplementOpen) = _
  rw [Scheme.Hom.comp_preimage]
  change hU.isoSpec.inv ⁻¹ᵁ
      ((CoordinateCharts.chartOpen 1).ι ⁻¹ᵁ hyperplaneComplementOpen) = _
  rw [← CoordinateCharts.firstNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen,
    Scheme.preimage_basicOpen]
  change (Spec Γ(plane, CoordinateCharts.chartOpen 1)).basicOpen
      (hU.isoSpec.inv.appTop CoordinateCharts.firstNormalSection) = _
  rw [IsAffineOpen.isoSpec_inv_appTop]
  change (Spec Γ(plane, CoordinateCharts.chartOpen 1)).basicOpen
      ((Scheme.ΓSpecIso Γ(plane, CoordinateCharts.chartOpen 1)).inv (normalSection 1)) = _
  rw [basicOpen_eq_of_affine]

lemma secondChart_fromSpec_preimage_hyperplaneComplementOpen :
    (chartIsAffine 2).fromSpec ⁻¹ᵁ hyperplaneComplementOpen =
      PrimeSpectrum.basicOpen (normalSection 2) := by
  let hU : IsAffineOpen (CoordinateCharts.chartOpen 2) := chartIsAffine 2
  change ((hU.isoSpec.inv ≫
      (CoordinateCharts.chartOpen 2).ι) ⁻¹ᵁ hyperplaneComplementOpen) = _
  rw [Scheme.Hom.comp_preimage]
  change hU.isoSpec.inv ⁻¹ᵁ
      ((CoordinateCharts.chartOpen 2).ι ⁻¹ᵁ hyperplaneComplementOpen) = _
  rw [← CoordinateCharts.secondNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen,
    Scheme.preimage_basicOpen]
  change (Spec Γ(plane, CoordinateCharts.chartOpen 2)).basicOpen
      (hU.isoSpec.inv.appTop CoordinateCharts.secondNormalSection) = _
  rw [IsAffineOpen.isoSpec_inv_appTop]
  change (Spec Γ(plane, CoordinateCharts.chartOpen 2)).basicOpen
      ((Scheme.ΓSpecIso Γ(plane, CoordinateCharts.chartOpen 2)).inv (normalSection 2)) = _
  rw [basicOpen_eq_of_affine]

lemma firstChart_fromSpec_preimage_hyperplaneClosed :
    (chartIsAffine 1).fromSpec ⁻¹' (hyperplaneClosed : Set plane) =
      PrimeSpectrum.zeroLocus ({normalSection 1} :
        Set Γ(plane, CoordinateCharts.chartOpen 1)) := by
  ext p
  have hcomp :
      (chartIsAffine 1).fromSpec p ∈ hyperplaneLocus ↔
        (chartIsAffine 1).fromSpec p ∉ hyperplaneComplementOpen := by
    have h := Set.ext_iff.mp hyperplaneComplementOpen_eq_compl
      ((chartIsAffine 1).fromSpec p)
    convert (not_congr (h.trans
      (Set.mem_compl_iff hyperplaneLocus ((chartIsAffine 1).fromSpec p)))).symm using 1
    · tauto
    · tauto
  have hopen :
      (chartIsAffine 1).fromSpec p ∈ hyperplaneComplementOpen ↔
        p ∈ PrimeSpectrum.basicOpen (normalSection 1) := by
    exact Set.ext_iff.mp
      (congrArg TopologicalSpace.Opens.carrier
        firstChart_fromSpec_preimage_hyperplaneComplementOpen) p
  change _ ↔ normalSection 1 ∉ p.asIdeal at hopen
  have hmain : (chartIsAffine 1).fromSpec p ∈ hyperplaneLocus ↔
      normalSection 1 ∈ p.asIdeal := by
    tauto
  convert hmain using 1
  · rfl
  · erw [PrimeSpectrum.mem_zeroLocus]
    simp

lemma secondChart_fromSpec_preimage_hyperplaneClosed :
    (chartIsAffine 2).fromSpec ⁻¹' (hyperplaneClosed : Set plane) =
      PrimeSpectrum.zeroLocus ({normalSection 2} :
        Set Γ(plane, CoordinateCharts.chartOpen 2)) := by
  ext p
  have hcomp :
      (chartIsAffine 2).fromSpec p ∈ hyperplaneLocus ↔
        (chartIsAffine 2).fromSpec p ∉ hyperplaneComplementOpen := by
    have h := Set.ext_iff.mp hyperplaneComplementOpen_eq_compl
      ((chartIsAffine 2).fromSpec p)
    convert (not_congr (h.trans
      (Set.mem_compl_iff hyperplaneLocus ((chartIsAffine 2).fromSpec p)))).symm using 1
    · tauto
    · tauto
  have hopen :
      (chartIsAffine 2).fromSpec p ∈ hyperplaneComplementOpen ↔
        p ∈ PrimeSpectrum.basicOpen (normalSection 2) := by
    exact Set.ext_iff.mp
      (congrArg TopologicalSpace.Opens.carrier
        secondChart_fromSpec_preimage_hyperplaneComplementOpen) p
  change _ ↔ normalSection 2 ∉ p.asIdeal at hopen
  have hmain : (chartIsAffine 2).fromSpec p ∈ hyperplaneLocus ↔
      normalSection 2 ∈ p.asIdeal := by
    tauto
  convert hmain using 1
  · rfl
  · erw [PrimeSpectrum.mem_zeroLocus]
    simp

lemma normalSection_prime (i : Fin 3) (hi : i ≠ 0) : Prime (normalSection i) := by
  rw [← chartGlobalRingEquiv_X_zero i hi]
  exact (MulEquiv.prime_iff (chartGlobalRingEquiv i).toMulEquiv).2 MvPolynomial.X_prime

lemma normalSection_span_isPrime (i : Fin 3) (hi : i ≠ 0) :
    (Ideal.span ({normalSection i} :
      Set Γ(plane, CoordinateCharts.chartOpen i))).IsPrime := by
  rw [Ideal.span_singleton_prime (normalSection_prime i hi).ne_zero]
  exact normalSection_prime i hi

lemma firstChart_fromPrimeSpectrum_preimage_hyperplaneClosed :
    (fun p : PrimeSpectrum Γ(plane, CoordinateCharts.chartOpen 1) ↦
      (chartIsAffine 1).fromSpec p) ⁻¹' (hyperplaneClosed : Set plane) =
        PrimeSpectrum.zeroLocus ({normalSection 1} :
          Set Γ(plane, CoordinateCharts.chartOpen 1)) := by
  ext p
  exact Set.ext_iff.mp firstChart_fromSpec_preimage_hyperplaneClosed p

lemma secondChart_fromPrimeSpectrum_preimage_hyperplaneClosed :
    (fun p : PrimeSpectrum Γ(plane, CoordinateCharts.chartOpen 2) ↦
      (chartIsAffine 2).fromSpec p) ⁻¹' (hyperplaneClosed : Set plane) =
        PrimeSpectrum.zeroLocus ({normalSection 2} :
          Set Γ(plane, CoordinateCharts.chartOpen 2)) := by
  ext p
  exact Set.ext_iff.mp secondChart_fromSpec_preimage_hyperplaneClosed p

lemma hyperplaneVanishingIdeal_firstChart :
    (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).ideal (chartAffineOpen 1) =
      Ideal.span ({normalSection 1} :
        Set Γ(plane, CoordinateCharts.chartOpen 1)) := by
  change PrimeSpectrum.vanishingIdeal
      ((chartIsAffine 1).fromSpec ⁻¹' (hyperplaneClosed : Set plane)) = _
  rw [firstChart_fromPrimeSpectrum_preimage_hyperplaneClosed,
    ← PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (normalSection_span_isPrime 1 (by decide)).isRadical.radical

lemma hyperplaneVanishingIdeal_secondChart :
    (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).ideal (chartAffineOpen 2) =
      Ideal.span ({normalSection 2} :
        Set Γ(plane, CoordinateCharts.chartOpen 2)) := by
  change PrimeSpectrum.vanishingIdeal
      ((chartIsAffine 2).fromSpec ⁻¹' (hyperplaneClosed : Set plane)) = _
  rw [secondChart_fromPrimeSpectrum_preimage_hyperplaneClosed,
    ← PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (normalSection_span_isPrime 2 (by decide)).isRadical.radical

/-! ### The elementary polynomial quotient -/

/-- Set the first variable of `ℂ[x₀,x₁]` equal to zero. -/
def dropFirstVariable :
    MvPolynomial (Fin 2) ℂ →+* MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.eval₂Hom C (Fin.cases 0 fun j ↦ X j)

/-- Include `ℂ[t]` as the subring generated by the second variable. -/
def includeSecondVariable :
    MvPolynomial (Fin 1) ℂ →+* MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.rename (fun i : Fin 1 ↦ Fin.succ i)).toRingHom

@[simp] lemma dropFirstVariable_X_zero : dropFirstVariable (X 0) = 0 := by
  simp [dropFirstVariable]

@[simp] lemma dropFirstVariable_X_one : dropFirstVariable (X 1) = X 0 := by
  unfold dropFirstVariable
  rw [MvPolynomial.eval₂Hom_X']
  rfl

@[simp] lemma includeSecondVariable_X_zero : includeSecondVariable (X 0) = X 1 := by
  simp [includeSecondVariable]

lemma dropFirstVariable_comp_includeSecondVariable :
    dropFirstVariable.comp includeSecondVariable = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dropFirstVariable, includeSecondVariable]
  · intro i
    fin_cases i
    simp

/-- The map from the quotient by the first variable to the remaining polynomial variable. -/
def quotientByFirstVariableToLine :
    (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ))) →+*
      MvPolynomial (Fin 1) ℂ :=
  Ideal.Quotient.lift _ dropFirstVariable (by
    intro x hx
    have hle : Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ)) ≤
        RingHom.ker dropFirstVariable := by
      rw [Ideal.span_le]
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      simp
    exact RingHom.mem_ker.mp (hle hx))

/-- The inverse map, sending the remaining variable to the class of the second variable. -/
def lineToQuotientByFirstVariable :
    MvPolynomial (Fin 1) ℂ →+*
      (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ))) :=
  (Ideal.Quotient.mk _).comp includeSecondVariable

lemma quotientByFirstVariableToLine_comp_lineToQuotientByFirstVariable :
    quotientByFirstVariableToLine.comp lineToQuotientByFirstVariable = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [quotientByFirstVariableToLine, lineToQuotientByFirstVariable,
      dropFirstVariable, includeSecondVariable]
  · intro i
    fin_cases i
    simp [quotientByFirstVariableToLine, lineToQuotientByFirstVariable]

lemma lineToQuotientByFirstVariable_comp_quotientByFirstVariableToLine :
    lineToQuotientByFirstVariable.comp quotientByFirstVariableToLine = RingHom.id _ := by
  apply RingHom.ext
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk _
      (includeSecondVariable (dropFirstVariable p)) = Ideal.Quotient.mk _ p
  have hmaps :
      (Ideal.Quotient.mk (Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ)))).comp
          (includeSecondVariable.comp dropFirstVariable) =
        Ideal.Quotient.mk (Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dropFirstVariable, includeSecondVariable]
    · intro i
      fin_cases i
      · change Ideal.Quotient.mk _
          (includeSecondVariable (dropFirstVariable (X 0))) = Ideal.Quotient.mk _ (X 0)
        rw [dropFirstVariable_X_zero]
        simp [Ideal.Quotient.eq_zero_iff_mem]
      · change Ideal.Quotient.mk _
          (includeSecondVariable (dropFirstVariable (X 1))) = Ideal.Quotient.mk _ (X 1)
        rw [dropFirstVariable_X_one, includeSecondVariable_X_zero]
  exact DFunLike.congr_fun hmaps p

/-- `ℂ[x₀,x₁]/(x₀) ≅ ℂ[t]`. -/
def quotientByFirstVariableEquivLine :
    (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ))) ≃+*
      MvPolynomial (Fin 1) ℂ :=
  RingEquiv.ofRingHom quotientByFirstVariableToLine lineToQuotientByFirstVariable
    quotientByFirstVariableToLine_comp_lineToQuotientByFirstVariable
    lineToQuotientByFirstVariable_comp_quotientByFirstVariableToLine

lemma map_span_X_zero_chartGlobalRingEquiv (i : Fin 3) (hi : i ≠ 0) :
    (Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ))).map
        (chartGlobalRingEquiv i : MvPolynomial (Fin 2) ℂ →+*
          Γ(plane, CoordinateCharts.chartOpen i)) =
      Ideal.span ({normalSection i} :
        Set Γ(plane, CoordinateCharts.chartOpen i)) := by
  rw [Ideal.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl, rfl⟩
    exact chartGlobalRingEquiv_X_zero i hi
  · rintro rfl
    exact ⟨X 0, rfl, chartGlobalRingEquiv_X_zero i hi⟩

/-- The quotient of the actual `i`-th chart ring by the displayed normal coordinate is an
affine-line coordinate ring. -/
def normalSectionQuotientEquivLine (i : Fin 3) (hi : i ≠ 0) :
    (Γ(plane, CoordinateCharts.chartOpen i) ⧸
        Ideal.span ({normalSection i} :
          Set Γ(plane, CoordinateCharts.chartOpen i))) ≃+*
      MvPolynomial (Fin 1) ℂ :=
  (Ideal.quotientEquiv
      (Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℂ)))
      (Ideal.span ({normalSection i} :
        Set Γ(plane, CoordinateCharts.chartOpen i)))
      (chartGlobalRingEquiv i)
      (map_span_X_zero_chartGlobalRingEquiv i hi).symm).symm.trans
    quotientByFirstVariableEquivLine

/-- The actual coordinate ring of the first hyperplane chart is a polynomial ring in one
variable. -/
def firstHyperplaneChartQuotientEquivLine :
    (Γ(plane, CoordinateCharts.chartOpen 1) ⧸
        (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).ideal (chartAffineOpen 1)) ≃+*
      MvPolynomial (Fin 1) ℂ :=
  (Ideal.quotEquivOfEq hyperplaneVanishingIdeal_firstChart).trans
    (normalSectionQuotientEquivLine 1 (by decide))

/-- The actual coordinate ring of the second hyperplane chart is a polynomial ring in one
variable. -/
def secondHyperplaneChartQuotientEquivLine :
    (Γ(plane, CoordinateCharts.chartOpen 2) ⧸
        (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).ideal (chartAffineOpen 2)) ≃+*
      MvPolynomial (Fin 1) ℂ :=
  (Ideal.quotEquivOfEq hyperplaneVanishingIdeal_secondChart).trans
    (normalSectionQuotientEquivLine 2 (by decide))

/-! ### The local structure morphisms -/

lemma specMap_basicOpenIsoAway_hom_comp_basicOpenIsoSpec_inv (i : Fin 3) :
    Spec.map (Proj.basicOpenIsoAway Grading (X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom ≫
        (Proj.basicOpenIsoSpec Grading (X i)
          (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).inv =
      (Proj.isAffineOpen_basicOpen Grading (X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).isoSpec.inv := by
  rw [← cancel_epi (Proj.isAffineOpen_basicOpen Grading (X i)
    (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).isoSpec.hom]
  rw [← Category.assoc]
  change ((Proj.basicOpen Grading (X i)).toSpecΓ ≫
      Spec.map (Proj.basicOpenIsoAway Grading (X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom) ≫
        (Proj.basicOpenIsoSpec Grading (X i)
          (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).inv = _
  rw [Proj.basicOpenIsoAway_hom]
  change Proj.basicOpenToSpec Grading (X i) ≫
      (Proj.basicOpenIsoSpec Grading (X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).inv = _
  rw [← Proj.basicOpenIsoSpec_hom Grading (X i)
    (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos]
  simp

/-- The base-ring map to the quotient coordinate ring on the `i`-th hyperplane chart. -/
def chartBaseRingHom (i : Fin 3) :
    ℂ →+* (Γ(plane, CoordinateCharts.chartOpen i) ⧸
      (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).ideal (chartAffineOpen i)) :=
  (Ideal.Quotient.mk _).comp
    ((chartGlobalRingEquiv i).toRingHom.comp
      (C : ℂ →+* MvPolynomial (Fin 2) ℂ))

lemma firstHyperplaneChartQuotientEquivLine_comp_chartBaseRingHom :
    firstHyperplaneChartQuotientEquivLine.toRingHom.comp (chartBaseRingHom 1) =
      (C : ℂ →+* MvPolynomial (Fin 1) ℂ) := by
  ext r
  simp [firstHyperplaneChartQuotientEquivLine, chartBaseRingHom,
    normalSectionQuotientEquivLine, quotientByFirstVariableEquivLine,
    quotientByFirstVariableToLine, dropFirstVariable, chartGlobalRingEquiv]

lemma secondHyperplaneChartQuotientEquivLine_comp_chartBaseRingHom :
    secondHyperplaneChartQuotientEquivLine.toRingHom.comp (chartBaseRingHom 2) =
      (C : ℂ →+* MvPolynomial (Fin 1) ℂ) := by
  ext r
  simp [secondHyperplaneChartQuotientEquivLine, chartBaseRingHom,
    normalSectionQuotientEquivLine, quotientByFirstVariableEquivLine,
    quotientByFirstVariableToLine, dropFirstVariable, chartGlobalRingEquiv]

lemma chartGlobalRingEquiv_comp_C (i : Fin 3) :
    (chartGlobalRingEquiv i).toRingHom.comp
        (C : ℂ →+* MvPolynomial (Fin 2) ℂ) =
      (Proj.basicOpenIsoAway Grading (X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).commRingCatIsoToRingEquiv.toRingHom.comp
        (Other.ProjectiveChart.cR ℂ i) := by
  ext r
  change (Proj.basicOpenIsoAway Grading (X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom
      (Other.ProjectiveChart.chartRingEquiv ℂ i (C r)) =
    (Proj.basicOpenIsoAway Grading (X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom
      (Other.ProjectiveChart.cR ℂ i r)
  congr 1
  exact DFunLike.congr_fun (Other.ProjectiveChart.chartRingEquiv_comp_C ℂ i) r

lemma chartFromSpec_eq_specMap_comp_awayι (i : Fin 3) :
    (Proj.isAffineOpen_basicOpen Grading (X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).fromSpec =
      Spec.map (Proj.basicOpenIsoAway Grading (X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom ≫
        Proj.awayι Grading (X i)
          (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos := by
  change (Proj.isAffineOpen_basicOpen Grading (X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).isoSpec.inv ≫
        (Proj.basicOpen Grading (X i)).ι = _
  rw [← specMap_basicOpenIsoAway_hom_comp_basicOpenIsoSpec_inv i,
    Category.assoc, Proj.basicOpenIsoSpec_inv_ι]

lemma chartFromSpec_comp_structureMap (i : Fin 3) :
    (chartIsAffine i).fromSpec ≫ structureMap =
      Spec.map (CommRingCat.ofHom
        ((chartGlobalRingEquiv i).toRingHom.comp
          (C : ℂ →+* MvPolynomial (Fin 2) ℂ))) := by
  have hfrom : (chartIsAffine i).fromSpec =
      Spec.map (Proj.basicOpenIsoAway Grading (X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom ≫
        Proj.awayι Grading (X i)
          (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos :=
    chartFromSpec_eq_specMap_comp_awayι i
  rw [hfrom]
  calc
    _ = Spec.map (Proj.basicOpenIsoAway Grading (X i)
          (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom ≫
        (Proj.awayι Grading (X i)
          (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos ≫ structureMap) :=
      Category.assoc _ _ _
    _ = Spec.map (Proj.basicOpenIsoAway Grading (X i)
          (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)) := by
      rw [ProjectivePlane.awayι_structureMap]
    _ = _ := by
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact DFunLike.congr_fun (chartGlobalRingEquiv_comp_C i) r |>.symm

lemma chartBaseRingHom_first_isStandardSmoothOfRelativeDimension :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (chartBaseRingHom 1) := by
  have hC : RingHom.IsStandardSmoothOfRelativeDimension 1
      (C : ℂ →+* MvPolynomial (Fin 1) ℂ) := by
    rw [show (C : ℂ →+* MvPolynomial (Fin 1) ℂ) =
      algebraMap ℂ (MvPolynomial (Fin 1) ℂ) from rfl,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    infer_instance
  have h := (RingHom.IsStandardSmoothOfRelativeDimension.equiv
    firstHyperplaneChartQuotientEquivLine.symm).comp hC
  have heq : ((firstHyperplaneChartQuotientEquivLine.symm :
      MvPolynomial (Fin 1) ℂ →+*
        (Γ(plane, CoordinateCharts.chartOpen 1) ⧸
          (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).ideal
            (chartAffineOpen 1))).comp
      (C : ℂ →+* MvPolynomial (Fin 1) ℂ)) = chartBaseRingHom 1 := by
    apply RingHom.ext
    intro r
    change firstHyperplaneChartQuotientEquivLine.symm (C r) = _
    rw [← DFunLike.congr_fun
      firstHyperplaneChartQuotientEquivLine_comp_chartBaseRingHom r]
    exact firstHyperplaneChartQuotientEquivLine.symm_apply_apply _
  simpa only [Nat.zero_add, heq] using h

lemma chartBaseRingHom_second_isStandardSmoothOfRelativeDimension :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (chartBaseRingHom 2) := by
  have hC : RingHom.IsStandardSmoothOfRelativeDimension 1
      (C : ℂ →+* MvPolynomial (Fin 1) ℂ) := by
    rw [show (C : ℂ →+* MvPolynomial (Fin 1) ℂ) =
      algebraMap ℂ (MvPolynomial (Fin 1) ℂ) from rfl,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    infer_instance
  have h := (RingHom.IsStandardSmoothOfRelativeDimension.equiv
    secondHyperplaneChartQuotientEquivLine.symm).comp hC
  have heq : ((secondHyperplaneChartQuotientEquivLine.symm :
      MvPolynomial (Fin 1) ℂ →+*
        (Γ(plane, CoordinateCharts.chartOpen 2) ⧸
          (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).ideal
            (chartAffineOpen 2))).comp
      (C : ℂ →+* MvPolynomial (Fin 1) ℂ)) = chartBaseRingHom 2 := by
    apply RingHom.ext
    intro r
    change secondHyperplaneChartQuotientEquivLine.symm (C r) = _
    rw [← DFunLike.congr_fun
      secondHyperplaneChartQuotientEquivLine_comp_chartBaseRingHom r]
    exact secondHyperplaneChartQuotientEquivLine.symm_apply_apply _
  simpa only [Nat.zero_add, heq] using h

lemma subschemeCover_chart_comp_hyperplaneOver (i : Fin 3) :
    (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeCover.f
        (chartAffineOpen i) ≫ hyperplaneOver.hom =
      Spec.map (CommRingCat.ofHom (chartBaseRingHom i)) := by
  change (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeCover.f
      (chartAffineOpen i) ≫
        ((Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeι ≫
          structureMap) = _
  rw [← Category.assoc,
    (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeCover_map_subschemeι]
  rw [(Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).glueDataObjι_ι]
  dsimp only [Scheme.IdealSheafData.subschemeCover,
    Scheme.IdealSheafData.glueDataObj]
  erw [Category.assoc]
  rw [chartFromSpec_comp_structureMap, ← Spec.map_comp]
  congr 1

lemma firstHyperplaneChart_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1
      ((Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeCover.f
        (chartAffineOpen 1) ≫ hyperplaneOver.hom) := by
  rw [subschemeCover_chart_comp_hyperplaneOver]
  have hs : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (chartBaseRingHom 1))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        chartBaseRingHom_first_isStandardSmoothOfRelativeDimension)
  exact hs

lemma secondHyperplaneChart_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1
      ((Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeCover.f
        (chartAffineOpen 2) ≫ hyperplaneOver.hom) := by
  rw [subschemeCover_chart_comp_hyperplaneOver]
  have hs : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (chartBaseRingHom 2))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        chartBaseRingHom_second_isStandardSmoothOfRelativeDimension)
  exact hs

/-! ### The two-chart cover -/

lemma hyperplane_preimage_chartOpen_zero_eq_bot :
    hyperplaneι ⁻¹ᵁ CoordinateCharts.chartOpen 0 = ⊥ := by
  ext x
  constructor
  · intro hx
    have hxLocus : hyperplaneι x ∈ hyperplaneLocus := by
      rw [← range_hyperplaneι]
      exact Set.mem_range_self x
    change hyperplaneι x ∈ (hyperplaneComplementOpen : Set plane) at hx
    rw [hyperplaneComplementOpen_eq_compl] at hx
    exact (hx hxLocus).elim
  · intro hx
    exact hx.elim

lemma iSup_hyperplane_preimage_chartOpen_succ_eq_top :
    ⨆ i : Fin 2, hyperplaneι ⁻¹ᵁ CoordinateCharts.chartOpen i.succ = ⊤ := by
  have hall : (⨆ i : Fin 3, hyperplaneι ⁻¹ᵁ CoordinateCharts.chartOpen i) = ⊤ :=
    hyperplaneι.iSup_preimage_eq_top
      (Other.ProjectiveChart.iSup_basicOpen_X_eq_top ℂ 2)
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hall.ge (Set.mem_univ x))
  fin_cases i
  · have : x ∈ (⊥ : hyperplane.Opens) := by
      rw [← hyperplane_preimage_chartOpen_zero_eq_bot]
      exact hi
    exact this.elim
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨0, hi⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨1, hi⟩

/-- The explicit coordinate hyperplane `X₀ = 0` is smooth of relative dimension one over
`Spec ℂ`, with no smoothness hypothesis. -/
theorem smoothOfRelativeDimension_hyperplaneOver :
    SmoothOfRelativeDimension 1 hyperplaneOver.hom := by
  change SmoothOfRelativeDimension 1 (hyperplaneι ≫ structureMap)
  let U : Fin 2 → hyperplane.Opens := fun i ↦
    hyperplaneι ⁻¹ᵁ CoordinateCharts.chartOpen i.succ
  have hU : ⨆ i, U i = ⊤ := iSup_hyperplane_preimage_chartOpen_succ_eq_top
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 1) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).respectsIso
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension 1)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
    (P := @SmoothOfRelativeDimension 1) U hU]
  intro i
  change SmoothOfRelativeDimension 1
    ((hyperplaneι ⁻¹ᵁ CoordinateCharts.chartOpen i.succ).ι ≫
      hyperplaneι ≫ structureMap)
  let f := (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeCover.f
    (chartAffineOpen i.succ)
  let g := (hyperplaneι ⁻¹ᵁ CoordinateCharts.chartOpen i.succ).ι
  change SmoothOfRelativeDimension 1 (g ≫ hyperplaneι ≫ structureMap)
  have hf : IsOpenImmersion f := by
    dsimp only [f]
    exact (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).subschemeCover.map_prop _
  have hrange : f.opensRange = U i := by
    dsimp only [f, U]
    exact (Scheme.IdealSheafData.vanishingIdeal hyperplaneClosed).opensRange_subschemeCover_map
      (chartAffineOpen i.succ)
  have hg : IsOpenImmersion g := by
    dsimp only [g]
    infer_instance
  have hrange' : Set.range f = Set.range g := by
    rw [← Scheme.Hom.coe_opensRange f, ← Scheme.Hom.coe_opensRange g]
    exact congrArg TopologicalSpace.Opens.carrier
      (hrange.trans (U i).opensRange_ι.symm)
  let e := @IsOpenImmersion.isoOfRangeEq _ _ _ f g hf hg hrange'
  letI : IsIso e.inv := by
    dsimp [e]
    infer_instance
  have hfac : e.inv ≫ f = g :=
    @IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _ f g hf hg hrange'
  change SmoothOfRelativeDimension 1 (g ≫ hyperplaneι ≫ structureMap)
  have hlocal : SmoothOfRelativeDimension 1 (f ≫ hyperplaneOver.hom) := by
    fin_cases i
    · exact firstHyperplaneChart_smoothOfRelativeDimension
    · exact secondHyperplaneChart_smoothOfRelativeDimension
  have hcancel : SmoothOfRelativeDimension 1 (e.inv ≫ (f ≫ hyperplaneOver.hom)) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1) e.inv (f ≫ hyperplaneOver.hom)).2 hlocal
  convert hcancel using 1
  change g ≫ (hyperplaneι ≫ structureMap) =
    e.inv ≫ f ≫ (hyperplaneι ≫ structureMap)
  rw [← hfac]
  exact Category.assoc _ _ _

instance : SmoothOfRelativeDimension 1 hyperplaneOver.hom :=
  smoothOfRelativeDimension_hyperplaneOver

end HyperplaneSmooth

end AlgebraicGeometry.ProjectivePlane
