/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveSpectrumTwistFrames
public import Other.AlgebraicGeometry.SchemePullbackGenerates
public import Other.AlgebraicGeometry.ProjectiveTwistAnalyticFrames

/-!
# Canonical chart frames of the twists on `ℙᴺ`, and their explicit transition units

The universal twist `𝒪(−n)` on `Proj ℤ[X₀, …, X_N]` has the explicit frame `1 / Xᵢⁿ` on the
basic open `D₊(Xᵢⁿ)` (`ProjectiveSpectrumTwistFrames.lean`).  Inverse image along
`toUniversalProj N` and along the (identity) immersion of the tautological presentation carries
that frame — and, by `Scheme.Modules.generates_pullbackSection`, its generating property — to the
algebraic twist on `ℙᴺ`, and `analyticSection` carries it further to `𝒪(−n)^an`.

Because the frames are inverse images of the *explicit* universal ones, the transition identity
computed on `Proj` transports verbatim: on the overlap of the `i`-th and `j`-th standard
homogeneous charts,

```
(Xⱼ/Xᵢ)ⁿ • frameⱼ = frameᵢ
```

both algebraically and, after evaluation of the regular function `(Xⱼ/Xᵢ)ⁿ`, analytically.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (N n : ℕ) (i j : Fin (N + 1))

/-- The `n`-th power of the `i`-th homogeneous coordinate, in degree `n`. -/
def coordPower : UniversalGrading N n :=
  degreeOnePower (UniversalGrading N) (homogeneousCoordinate N i) n

@[simp]
theorem coe_coordPower :
    ((coordPower N n i : UniversalGrading N n) : UniversalRing N) =
      (MvPolynomial.X i : UniversalRing N) ^ n := rfl

/-- The universal frame `1 / Xᵢⁿ` of `𝒪(−n)` on `D₊(Xᵢⁿ) ⊆ Proj ℤ[X]`. -/
def universalChartFrame :
    Γ(schemeSheafOfModules (UniversalGrading N) n,
      (ProjectiveSpectrum.basicOpen (UniversalGrading N)
        ((coordPower N n i : UniversalRing N)) : (Proj (UniversalGrading N)).Opens)) :=
  projFrame (UniversalGrading N) (coordPower N n i)

theorem generates_universalChartFrame :
    Scheme.Modules.Generates (universalChartFrame N n i) :=
  generates_projFrame (UniversalGrading N) (coordPower N n i)

/-- The frame of the algebraic twist on `ℙᴺ` over the preimage of `D₊(Xᵢⁿ)`. -/
def spaceChartFrameBig :
    Γ(negativeTwist N n,
      projectiveSpaceBasicOpen N ((MvPolynomial.X i : UniversalRing N) ^ n)) :=
  Scheme.Modules.pullbackSection (toUniversalProj N) _ _ (universalChartFrame N n i)

theorem generates_spaceChartFrameBig :
    Scheme.Modules.Generates (spaceChartFrameBig N n i) :=
  Scheme.Modules.generates_pullbackSection _ (generates_universalChartFrame N n i)

/-- The frame of the presentation-induced algebraic twist on `ℙᴺ` over the preimage of
`D₊(Xᵢⁿ)`. -/
def algChartFrameBig :
    Γ(ComplexPoint.ProjectiveTwist.algebraic (Other.ProjectiveChart.projectiveSpaceOver N)
        (Other.ProjectiveChart.projPresentation N) n,
      projectiveSpaceBasicOpen N ((MvPolynomial.X i : UniversalRing N) ^ n)) :=
  Scheme.Modules.pullbackSection (Other.ProjectiveChart.projPresentation N).immersion _ _
    (spaceChartFrameBig N n i)

theorem generates_algChartFrameBig :
    Scheme.Modules.Generates (algChartFrameBig N n i) :=
  Scheme.Modules.generates_pullbackSection _ (generates_spaceChartFrameBig N n i)

/-- The `i`-th standard chart is contained in the basic open of the `n`-th power. -/
theorem basicOpen_le_pow (f : UniversalRing N) :
    ProjectiveSpectrum.basicOpen (UniversalGrading N) f ≤
      ProjectiveSpectrum.basicOpen (UniversalGrading N) (f ^ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [ProjectiveSpectrum.basicOpen_pow _ _ n hn]

theorem projectiveSpaceBasicOpen_le_pow :
    projectiveSpaceBasicOpen N (MvPolynomial.X i) ≤
      projectiveSpaceBasicOpen N ((MvPolynomial.X i : UniversalRing N) ^ n) :=
  fun _ hx => basicOpen_le_pow N n (MvPolynomial.X i) hx

/-- **The canonical algebraic chart frame** of `𝒪(−n)` on `ℙᴺ`: the inverse image of the
universal frame `1 / Xᵢⁿ`, restricted to the `i`-th standard chart. -/
def algChartFrame :
    Γ(ComplexPoint.ProjectiveTwist.algebraic (Other.ProjectiveChart.projectiveSpaceOver N)
        (Other.ProjectiveChart.projPresentation N) n,
      projectiveSpaceBasicOpen N (MvPolynomial.X i)) :=
  Scheme.Modules.resSection _ (projectiveSpaceBasicOpen_le_pow N n i) (algChartFrameBig N n i)

theorem generates_algChartFrame : Scheme.Modules.Generates (algChartFrame N n i) :=
  (generates_algChartFrameBig N n i).restrict _

/-- **The canonical analytic chart frame** of `𝒪(−n)^an` on the `i`-th homogeneous chart. -/
def anChartFrame :
    (ComplexPoint.ProjectiveTwist.analytic (Other.ProjectiveChart.projectiveSpaceOver N) N
      (Other.ProjectiveChart.projPresentation N) n).val.obj (op (chartOpen N i)) :=
  ComplexPoint.analyticSection (Other.ProjectiveChart.projectiveSpaceOver N) N _ _
    (algChartFrame N n i)

/-- The canonical analytic chart frame generates. -/
theorem holomorphicGenerates_anChartFrame :
    ComplexPoint.HolomorphicGenerates
      (M := ComplexPoint.ProjectiveTwist.analytic
        (Other.ProjectiveChart.projectiveSpaceOver N) N
        (Other.ProjectiveChart.projPresentation N) n)
      (anChartFrame N n i) :=
  ComplexPoint.analytificationGenerates (Other.ProjectiveChart.projectiveSpaceOver N) N
    _ _ _ (generates_algChartFrame N n i)

/-! ### The explicit transition unit on chart overlaps -/

/-- The overlap of the `i`-th and `j`-th coordinate basic opens on the universal model. -/
def universalOverlap : (Proj (UniversalGrading N)).Opens :=
  (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) ⊓
    ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X j) :
      (Proj (UniversalGrading N)).Opens)

theorem universalOverlap_le_coordPower :
    universalOverlap N i j ≤
      (ProjectiveSpectrum.basicOpen (UniversalGrading N)
        ((coordPower N n i : UniversalRing N)) : (Proj (UniversalGrading N)).Opens) :=
  fun _ hx => basicOpen_le_pow N n (MvPolynomial.X i) hx.1

theorem universalOverlap_le_coordPower' :
    universalOverlap N i j ≤
      (ProjectiveSpectrum.basicOpen (UniversalGrading N)
        ((coordPower N n j : UniversalRing N)) : (Proj (UniversalGrading N)).Opens) :=
  fun _ hx => basicOpen_le_pow N n (MvPolynomial.X j) hx.2

theorem coordPower_notMem (x : universalOverlap N i j) :
    ((coordPower N n i : UniversalRing N)) ∉ x.1.asHomogeneousIdeal :=
  universalOverlap_le_coordPower N n i j x.2

/-- The regular function `Xⱼⁿ / Xᵢⁿ` on the universal chart overlap. -/
def universalRatio : Γ(Proj (UniversalGrading N), universalOverlap N i j) :=
  projRatio (UniversalGrading N) (coordPower N n j) (coordPower N n i) (universalOverlap N i j)
    (coordPower_notMem N n i j)

/-- **The universal transition identity.** -/
theorem universalRatio_smul_universalChartFrame :
    universalRatio N n i j •
        Scheme.Modules.resSection (schemeSheafOfModules (UniversalGrading N) n)
          (universalOverlap_le_coordPower' N n i j) (universalChartFrame N n j) =
      Scheme.Modules.resSection (schemeSheafOfModules (UniversalGrading N) n)
        (universalOverlap_le_coordPower N n i j) (universalChartFrame N n i) :=
  projRatio_smul_projFrame (UniversalGrading N) (coordPower N n i) (coordPower N n j)
    (universalOverlap N i j) (universalOverlap_le_coordPower N n i j)
    (universalOverlap_le_coordPower' N n i j) (coordPower_notMem N n i j)

/-- The regular function `Xⱼⁿ / Xᵢⁿ` on the overlap of two standard charts of `ℙᴺ`. -/
def spaceRatio : Γ((Other.ProjectiveChart.projectiveSpaceOver N).left,
    projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
      projectiveSpaceBasicOpen N (MvPolynomial.X j)) :=
  Scheme.Modules.pullbackFunction (Other.ProjectiveChart.projPresentation N).immersion _
    (Scheme.Modules.pullbackFunction (toUniversalProj N) _ (universalRatio N n i j))

/-- The chart overlap is contained in the basic open of `Xᵢⁿ`. -/
theorem spaceOverlap_le_pow_left :
    projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
        projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤
      projectiveSpaceBasicOpen N ((MvPolynomial.X i : UniversalRing N) ^ n) :=
  fun _ hx => basicOpen_le_pow N n (MvPolynomial.X i) hx.1

/-- The chart overlap is contained in the basic open of `Xⱼⁿ`. -/
theorem spaceOverlap_le_pow_right :
    projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
        projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤
      projectiveSpaceBasicOpen N ((MvPolynomial.X j : UniversalRing N) ^ n) :=
  fun _ hx => basicOpen_le_pow N n (MvPolynomial.X j) hx.2

set_option maxHeartbeats 1000000 in
/-- **The algebraic transition identity on `ℙᴺ`,** for the frames over the preimages of the
basic opens of `Xᵢⁿ`. -/
theorem spaceRatio_smul_algChartFrameBig :
    spaceRatio N n i j •
        Scheme.Modules.resSection (ComplexPoint.ProjectiveTwist.algebraic
            (Other.ProjectiveChart.projectiveSpaceOver N)
            (Other.ProjectiveChart.projPresentation N) n)
          (spaceOverlap_le_pow_right N n i j) (algChartFrameBig N n j) =
      Scheme.Modules.resSection (ComplexPoint.ProjectiveTwist.algebraic
          (Other.ProjectiveChart.projectiveSpaceOver N)
          (Other.ProjectiveChart.projPresentation N) n)
        (spaceOverlap_le_pow_left N n i j) (algChartFrameBig N n i) := by
  have h1 := Scheme.Modules.pullbackSection_smul_res (toUniversalProj N)
    (schemeSheafOfModules (UniversalGrading N) n)
    (universalOverlap_le_coordPower' N n i j) (universalOverlap_le_coordPower N n i j)
    (universalRatio N n i j) (universalChartFrame N n j) (universalChartFrame N n i)
    (universalRatio_smul_universalChartFrame N n i j)
  exact Scheme.Modules.pullbackSection_smul_res
    (Other.ProjectiveChart.projPresentation N).immersion (negativeTwist N n)
    (Scheme.Modules.preimage_mono (toUniversalProj N)
      (universalOverlap_le_coordPower' N n i j))
    (Scheme.Modules.preimage_mono (toUniversalProj N)
      (universalOverlap_le_coordPower N n i j))
    (Scheme.Modules.pullbackFunction (toUniversalProj N) _ (universalRatio N n i j))
    (spaceChartFrameBig N n j) (spaceChartFrameBig N n i) h1

set_option maxHeartbeats 1000000 in
/-- **The algebraic transition identity on `ℙᴺ`,** for the canonical chart frames. -/
theorem spaceRatio_smul_algChartFrame :
    spaceRatio N n i j •
        Scheme.Modules.resSection (ComplexPoint.ProjectiveTwist.algebraic
            (Other.ProjectiveChart.projectiveSpaceOver N)
            (Other.ProjectiveChart.projPresentation N) n)
          (inf_le_right : projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
            projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤ _)
          (algChartFrame N n j) =
      Scheme.Modules.resSection (ComplexPoint.ProjectiveTwist.algebraic
          (Other.ProjectiveChart.projectiveSpaceOver N)
          (Other.ProjectiveChart.projPresentation N) n)
        (inf_le_left : projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
          projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤ _)
        (algChartFrame N n i) := by
  have hi := Scheme.Modules.resSection_resSection
    (L := ComplexPoint.ProjectiveTwist.algebraic (Other.ProjectiveChart.projectiveSpaceOver N)
      (Other.ProjectiveChart.projPresentation N) n)
    (projectiveSpaceBasicOpen_le_pow N n i)
    (inf_le_left : projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
      projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤ _) (algChartFrameBig N n i)
  have hj := Scheme.Modules.resSection_resSection
    (L := ComplexPoint.ProjectiveTwist.algebraic (Other.ProjectiveChart.projectiveSpaceOver N)
      (Other.ProjectiveChart.projPresentation N) n)
    (projectiveSpaceBasicOpen_le_pow N n j)
    (inf_le_right : projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
      projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤ _) (algChartFrameBig N n j)
  rw [show algChartFrame N n i = Scheme.Modules.resSection _
      (projectiveSpaceBasicOpen_le_pow N n i) (algChartFrameBig N n i) from rfl,
    show algChartFrame N n j = Scheme.Modules.resSection _
      (projectiveSpaceBasicOpen_le_pow N n j) (algChartFrameBig N n j) from rfl, hi, hj]
  exact spaceRatio_smul_algChartFrameBig N n i j

set_option maxHeartbeats 1000000 in
/-- **The analytic transition identity on `ℙᴺ`.**  On the overlap of the `i`-th and `j`-th
homogeneous charts, the canonical analytic frames differ by the evaluation of the regular
function `Xⱼⁿ / Xᵢⁿ`. -/
theorem analyticFunction_spaceRatio_smul_anChartFrame :
    ComplexPoint.analyticFunction (Other.ProjectiveChart.projectiveSpaceOver N) N
        (projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
          projectiveSpaceBasicOpen N (MvPolynomial.X j)) (spaceRatio N n i j) •
        ComplexPoint.holRes (ComplexPoint.ProjectiveTwist.analytic
            (Other.ProjectiveChart.projectiveSpaceOver N) N
            (Other.ProjectiveChart.projPresentation N) n)
          (ComplexPoint.analyticOpen_mono (Other.ProjectiveChart.projectiveSpaceOver N)
            (inf_le_right : projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
              projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤ _))
          (anChartFrame N n j) =
      ComplexPoint.holRes (ComplexPoint.ProjectiveTwist.analytic
          (Other.ProjectiveChart.projectiveSpaceOver N) N
          (Other.ProjectiveChart.projPresentation N) n)
        (ComplexPoint.analyticOpen_mono (Other.ProjectiveChart.projectiveSpaceOver N)
          (inf_le_left : projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
            projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤ _))
        (anChartFrame N n i) :=
  ComplexPoint.analyticSection_smul_res
    (ComplexPoint.ProjectiveTwist.algebraic (Other.ProjectiveChart.projectiveSpaceOver N)
      (Other.ProjectiveChart.projPresentation N) n)
    inf_le_right inf_le_left (spaceRatio N n i j) (algChartFrame N n j) (algChartFrame N n i)
    (spaceRatio_smul_algChartFrame N n i j)

end AlgebraicGeometry.ComplexProjectiveSpace
