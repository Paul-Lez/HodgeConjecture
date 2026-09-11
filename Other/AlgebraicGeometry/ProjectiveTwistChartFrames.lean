/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistObligations
public import Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff

/-!
# Chartwise frames for the projective twists (G2)

The algebraic twist `𝒪(−n)` on `ℙᴺ` is trivialised on the standard basic opens `D₊(Xᵢ)`, and
those are exactly the standard homogeneous charts of the analytification.  This file proves the
topological half of that statement: the analytic open attached to `D₊(Xᵢ)` is the chart set
`complexPointChartSet i`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A coordinate point lies in a positive-degree basic open of complex projective space exactly
when the defining homogeneous polynomial does not vanish on its coordinates. -/
theorem vectorToComplexPoint_mem_projectiveSpaceBasicOpen_iff {n d : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0) (r : UniversalRing n) (hd : 0 < d)
    (hr : r ∈ UniversalGrading n d) :
    vectorToComplexPoint v hv ∈ Point.overOpen (projectiveSpaceBasicOpen n r) ↔
      coordinateEvaluationHom v r ≠ 0 := by
  refine ⟨fun hmem hzero ↦ ?_,
    vectorToComplexPoint_mem_projectiveSpaceBasicOpen v hv r hd hr⟩
  have hchange : IsLocalRing.closedPoint ℂ ∈
      chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r := by
    have h : (vectorToProjectiveSpace v hv) (IsLocalRing.closedPoint ℂ) ∈
        projectiveSpaceBasicOpen n r := hmem
    unfold projectiveSpaceBasicOpen at h
    change ((vectorToProjectiveSpace v hv) ≫ Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ))
      (Limits.terminal.from (Proj (UniversalGrading n))))
        (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen (UniversalGrading n) r at h
    rwa [vectorToProjectiveSpace_toProj] at h
  rw [chartIntegralProj_preimage_basicOpen v hv r hd hr, if_pos hzero] at hchange
  exact hchange

/-- The analytic open attached to the `i`-th standard basic open of `ℙᴺ` is the `i`-th standard
homogeneous chart of the analytification. -/
theorem overOpen_projectiveSpaceBasicOpen_X (N : ℕ) (i : Fin (N + 1)) :
    (Point.overOpen (projectiveSpaceBasicOpen N (MvPolynomial.X i)) :
      Set (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))))) =
      complexPointChartSet i := by
  ext z
  obtain ⟨p, rfl⟩ := surjective_projectivizationToComplexPoint z
  induction p using Projectivization.ind with
  | _ v hv =>
    rw [projectivizationToComplexPoint_mk]
    have hX : (MvPolynomial.X i : UniversalRing N) ∈ UniversalGrading N 1 :=
      MvPolynomial.isHomogeneous_X _ i
    rw [vectorToComplexPoint_mem_projectiveSpaceBasicOpen_iff v hv _ Nat.one_pos hX,
      coordinateEvaluationHom_X]
    constructor
    · intro hvi
      refine ⟨Projectivization.mk ℂ v hv, ?_, rfl⟩
      have : (⟨v, hv⟩ : {w : CoordinateSpace N // w ≠ 0}) ∈ projMk ⁻¹' chartSet i := by
        rw [preimage_chartSet]
        exact hvi
      exact this
    · rintro ⟨q, hq, hqz⟩
      have hinj := injective_projectivizationToComplexPoint (n := N)
      have hqeq : q = Projectivization.mk ℂ v hv := by
        apply hinj
        exact hqz
      subst hqeq
      have : (⟨v, hv⟩ : {w : CoordinateSpace N // w ≠ 0}) ∈ projMk ⁻¹' chartSet i := hq
      rwa [preimage_chartSet] at this

/-! ### The algebraic trivialisations on the standard charts -/

open ProjectiveSpectrum.NegativeTwist ComplexPoint in
/-- The standard degree-`n` trivialising family of `𝒪(−n)` on the universal `Proj` model, with
members the standard coordinate basic opens. -/
def universalTwistTrivializations (N n : ℕ) :
    TauCeti.SheafOfModules.LocalTrivializations
      (ProjectiveSpectrum.NegativeTwist.schemeSheafOfModules (UniversalGrading N) n) :=
  localTrivializationsOfBasicOpenCover (UniversalGrading N)
    (fun i : Fin (N + 1) ↦ degreeOnePower (UniversalGrading N) (homogeneousCoordinate N i) n)
    (by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · refine top_unique fun x _ ↦ ?_
        refine TopologicalSpace.Opens.mem_iSup.2 ⟨0, ?_⟩
        simp [degreeOnePower]
      · exact iSup_basicOpen_degreeOnePower_eq_top (UniversalGrading N)
          (homogeneousCoordinate N) (iSup_coordinateBasicOpen_eq_top N) n hn)

open ComplexPoint in
/-- The induced trivialising family of the presentation-induced algebraic twist on `ℙᴺ`. -/
def twistTrivializations (N n : ℕ) :
    TauCeti.SheafOfModules.LocalTrivializations
      (ComplexPoint.ProjectiveTwist.algebraic (Other.ProjectiveChart.projectiveSpaceOver N)
        (Other.ProjectiveChart.projPresentation N) n) :=
  Scheme.Modules.localTrivializationsPullback
      (Other.ProjectiveChart.projPresentation N).immersion _
    (Scheme.Modules.localTrivializationsPullback (toUniversalProj N) _
      (universalTwistTrivializations N n))

open ProjectiveSpectrum.NegativeTwist ComplexPoint in
/-- The `i`-th standard chart is contained in the `i`-th member of the trivialising family. -/
theorem projectiveSpaceBasicOpen_le_twistTrivializations (N n : ℕ) (i : Fin (N + 1)) :
    projectiveSpaceBasicOpen N (MvPolynomial.X i) ≤ (twistTrivializations N n).X i := by
  have hbasic : ProjectiveSpectrum.basicOpen (UniversalGrading N)
      (MvPolynomial.X i : UniversalRing N) ≤
      ProjectiveSpectrum.basicOpen (UniversalGrading N)
        ((degreeOnePower (UniversalGrading N) (homogeneousCoordinate N i) n :
          UniversalRing N)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [degreeOnePower]
    · rw [show ((degreeOnePower (UniversalGrading N) (homogeneousCoordinate N i) n :
          UniversalRing N)) = (MvPolynomial.X i : UniversalRing N) ^ n from rfl,
        ProjectiveSpectrum.basicOpen_pow _ _ n hn]
  exact fun x hx ↦ hbasic hx

/-! ### (G2) -/

open ComplexPoint in
/-- **(G2): chartwise frames for the algebraic twist on `ℙᴺ`.**  The twist `𝒪(−n)` has a
generating section on each standard basic open `D₊(Xᵢ)`, and the analytic open attached to that
basic open is exactly the `i`-th standard homogeneous chart of `ℙᴺ(ℂ)^an`. -/
theorem twistChartFramesProj (N n : ℕ) : Other.ProjectiveChart.TwistChartFramesProj N n := by
  intro i
  have hle := projectiveSpaceBasicOpen_le_twistTrivializations N n i
  refine ⟨projectiveSpaceBasicOpen N (MvPolynomial.X i),
    Scheme.Modules.resSection _ hle
      (Scheme.Modules.unitIsoSection
        ((TauCeti.SheafOfModules.freePUnitIsoUnit _).symm ≪≫ (twistTrivializations N n).iso i)),
    (Scheme.Modules.generates_unitIsoSection _).restrict hle, ?_⟩
  exact overOpen_projectiveSpaceBasicOpen_X N i

end AlgebraicGeometry.ComplexProjectiveSpace
