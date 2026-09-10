/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal
public import Other.AlgebraicGeometry.ExplicitEllipticSegre
public import Other.AlgebraicGeometry.ExplicitEllipticSurfacePointProduct
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates

/-!
# The topological CM endomorphism of the explicit elliptic curve

The global CM map is assembled from complex-algebra automorphisms of the two affine
charts.  This file proves that it is a morphism over `Spec ℂ`, packages it as an
endomorphism of the explicit complex variety, and records its order-four relation after
analytification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

/-- The explicit CM automorphism on the Z chart respects the structure map to `Spec ℂ`. -/
theorem curveZCMChartIso_toBase :
    curveZCMChartIso.hom ≫ curveZOpen.ι ≫ curveToBase =
      curveZOpen.ι ≫ curveToBase := by
  letI : IsAffine curveZOpen.toScheme := curveZOpen_isAffine
  letI : IsAffine base := by
    dsimp [base]
    infer_instance
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  rw [curveZCMChartIso_appTop]
  have ht : curveZOpen.ι.appTop ≫ curveZOpen.topIso.hom =
      curve.presheaf.map (homOfLE (show curveZOpen ≤ ⊤ from le_top)).op :=
    Scheme.Opens.ι_appTop_topIso_hom curveZOpen
  apply CommRingCat.hom_ext
  ext s
  let c : ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom s
  have hs : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c = s := by
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply s
  rw [← hs]
  change curveZOpen.topIso.inv
      (curveZCMAlgEquiv
        (curveZOpen.topIso.hom
          (curveZOpen.ι.appTop
            (curveToBase.appTop
              ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))))) =
    curveZOpen.ι.appTop
      (curveToBase.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  have hcscalar : curveZOpen.topIso.hom
        (curveZOpen.ι.appTop
          (curveToBase.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
      curveScalar curveZOpen c := by
    change (curveZOpen.ι.appTop ≫ curveZOpen.topIso.hom)
        (curveToBase.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = _
    rw [ht]
    rfl
  rw [hcscalar]
  have he : curveZCMAlgEquiv (curveScalar curveZOpen c) =
      curveScalar curveZOpen c := by
    change curveZCMAlgEquiv (algebraMap ℂ Γ(curve, curveZOpen) c) =
      algebraMap ℂ Γ(curve, curveZOpen) c
    exact curveZCMAlgEquiv.commutes c
  rw [he]
  rw [← hcscalar]
  exact curveZOpen.topIso.hom_inv_id_apply _

/-- The explicit CM automorphism on the Y chart respects the structure map to `Spec ℂ`. -/
theorem curveYCMChartIso_toBase :
    curveYCMChartIso.hom ≫ curveYOpen.ι ≫ curveToBase =
      curveYOpen.ι ≫ curveToBase := by
  letI : IsAffine curveYOpen.toScheme := curveYOpen_isAffine
  letI : IsAffine base := by
    dsimp [base]
    infer_instance
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  rw [curveYCMChartIso_appTop]
  have ht : curveYOpen.ι.appTop ≫ curveYOpen.topIso.hom =
      curve.presheaf.map (homOfLE (show curveYOpen ≤ ⊤ from le_top)).op :=
    Scheme.Opens.ι_appTop_topIso_hom curveYOpen
  apply CommRingCat.hom_ext
  ext s
  let c : ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom s
  have hs : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c = s := by
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply s
  rw [← hs]
  change curveYOpen.topIso.inv
      (curveYCMAlgEquiv
        (curveYOpen.topIso.hom
          (curveYOpen.ι.appTop
            (curveToBase.appTop
              ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))))) =
    curveYOpen.ι.appTop
      (curveToBase.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  have hcscalar : curveYOpen.topIso.hom
        (curveYOpen.ι.appTop
          (curveToBase.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
      curveScalar curveYOpen c := by
    change (curveYOpen.ι.appTop ≫ curveYOpen.topIso.hom)
        (curveToBase.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = _
    rw [ht]
    rfl
  rw [hcscalar]
  have he : curveYCMAlgEquiv (curveScalar curveYOpen c) =
      curveScalar curveYOpen c := by
    change curveYCMAlgEquiv (algebraMap ℂ Γ(curve, curveYOpen) c) =
      algebraMap ℂ Γ(curve, curveYOpen) c
    exact curveYCMAlgEquiv.commutes c
  rw [he]
  rw [← hcscalar]
  exact curveYOpen.topIso.hom_inv_id_apply _

/-- The global CM endomorphism is a morphism over the complex base. -/
theorem curveCMEnd_toBase : curveCMEnd ≫ curveToBase = curveToBase := by
  apply curveCMCover.hom_ext
  change ∀ i : Fin 2, _
  intro i
  fin_cases i
  · change curveZOpen.ι ≫ curveCMEnd ≫ curveToBase =
      curveZOpen.ι ≫ curveToBase
    simpa only [Category.assoc, curveZOpen_ι_curveCMEnd_assoc] using
      curveZCMChartIso_toBase
  · change curveYOpen.ι ≫ curveCMEnd ≫ curveToBase =
      curveYOpen.ι ≫ curveToBase
    simpa only [Category.assoc, curveYOpen_ι_curveCMEnd_assoc] using
      curveYCMChartIso_toBase

/-- The explicit CM endomorphism as an endomorphism of the complex variety. -/
def curveVarietyCMEnd : curveVariety ⟶ curveVariety :=
  Over.homMk (U := curveVariety) (V := curveVariety)
    curveCMEnd curveCMEnd_toBase

/-- The fourth iterate of the CM endomorphism is the identity over `Spec ℂ`. -/
theorem curveVarietyCMEnd_four :
    curveVarietyCMEnd ≫ curveVarietyCMEnd ≫
        curveVarietyCMEnd ≫ curveVarietyCMEnd = 𝟙 curveVariety := by
  apply Over.OverMorphism.ext
  exact curveCMEnd_four

/-- The continuous self-map of complex points induced by complex multiplication. -/
def curveCMAnalyticMap :
    complexAnalytification.obj curveVariety ⟶
      complexAnalytification.obj curveVariety :=
  complexAnalytification.map curveVarietyCMEnd

/-- The analytified CM map has order dividing four. -/
theorem curveCMAnalyticMap_four :
    curveCMAnalyticMap ≫ curveCMAnalyticMap ≫
        curveCMAnalyticMap ≫ curveCMAnalyticMap =
      𝟙 (complexAnalytification.obj curveVariety) := by
  unfold curveCMAnalyticMap
  rw [← complexAnalytification.map_comp,
    ← complexAnalytification.map_comp,
    ← complexAnalytification.map_comp,
    curveVarietyCMEnd_four, complexAnalytification.map_id]

/-! ## Factorwise CM maps on the elliptic surface -/

/-- The first scheme-theoretic projection from the explicit surface.  Naming the
projection here keeps later pullback universal-property arguments independent of
unfolding the opaque abbreviation `surface`. -/
def surfaceFstScheme : surface ⟶ curve := by
  exact surfaceVarietyFst.left

/-- The second scheme-theoretic projection from the explicit surface. -/
def surfaceSndScheme : surface ⟶ curve := by
  exact surfaceVarietySnd.left

theorem surfaceFstScheme_eq_pullbackFst :
    surfaceFstScheme = pullback.fst curveToBase curveToBase := by
  rfl

theorem surfaceSndScheme_eq_pullbackSnd :
    surfaceSndScheme = pullback.snd curveToBase curveToBase := by
  rfl

theorem surfaceFstScheme_toBase :
    surfaceFstScheme ≫ curveToBase = surfaceToBase := by
  rfl

theorem surfaceSndScheme_toBase :
    surfaceSndScheme ≫ curveToBase = surfaceToBase := by
  change pullback.snd curveToBase curveToBase ≫ curveToBase =
    pullback.fst curveToBase curveToBase ≫ curveToBase
  exact pullback.condition.symm

theorem surfaceFirstCMCompatibility :
    (surfaceFstScheme ≫ curveCMEnd) ≫ curveToBase =
      surfaceSndScheme ≫ curveToBase := by
  rw [Category.assoc, curveCMEnd_toBase,
    surfaceFstScheme_toBase, surfaceSndScheme_toBase]

theorem surfaceSecondCMCompatibility :
    surfaceFstScheme ≫ curveToBase =
      (surfaceSndScheme ≫ curveCMEnd) ≫ curveToBase := by
  rw [Category.assoc, curveCMEnd_toBase,
    surfaceFstScheme_toBase, surfaceSndScheme_toBase]

/-- Complex multiplication on the first factor of the scheme-theoretic self-product. -/
def surfaceFirstCMEnd : surface ⟶ surface := by
  change surface ⟶ pullback curveToBase curveToBase
  exact pullback.lift
    (surfaceFstScheme ≫ curveCMEnd) surfaceSndScheme
      surfaceFirstCMCompatibility

/-- Complex multiplication on the second factor of the scheme-theoretic self-product. -/
def surfaceSecondCMEnd : surface ⟶ surface := by
  change surface ⟶ pullback curveToBase curveToBase
  exact pullback.lift
    surfaceFstScheme (surfaceSndScheme ≫ curveCMEnd)
      surfaceSecondCMCompatibility

@[reassoc]
theorem surfaceFirstCMEnd_fst :
    surfaceFirstCMEnd ≫ surfaceFstScheme =
      surfaceFstScheme ≫ curveCMEnd := by
  rw [surfaceFstScheme_eq_pullbackFst]
  change (pullback.lift (surfaceFstScheme ≫ curveCMEnd)
    surfaceSndScheme surfaceFirstCMCompatibility) ≫
      pullback.fst curveToBase curveToBase =
        surfaceFstScheme ≫ curveCMEnd
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem surfaceFirstCMEnd_snd :
    surfaceFirstCMEnd ≫ surfaceSndScheme = surfaceSndScheme := by
  rw [surfaceSndScheme_eq_pullbackSnd]
  change (pullback.lift (surfaceFstScheme ≫ curveCMEnd)
    surfaceSndScheme surfaceFirstCMCompatibility) ≫
      pullback.snd curveToBase curveToBase = surfaceSndScheme
  exact pullback.lift_snd _ _ _

@[reassoc]
theorem surfaceSecondCMEnd_fst :
    surfaceSecondCMEnd ≫ surfaceFstScheme = surfaceFstScheme := by
  rw [surfaceFstScheme_eq_pullbackFst]
  change (pullback.lift surfaceFstScheme
    (surfaceSndScheme ≫ curveCMEnd) surfaceSecondCMCompatibility) ≫
      pullback.fst curveToBase curveToBase = surfaceFstScheme
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem surfaceSecondCMEnd_snd :
    surfaceSecondCMEnd ≫ surfaceSndScheme =
      surfaceSndScheme ≫ curveCMEnd := by
  rw [surfaceSndScheme_eq_pullbackSnd]
  change (pullback.lift surfaceFstScheme
    (surfaceSndScheme ≫ curveCMEnd) surfaceSecondCMCompatibility) ≫
      pullback.snd curveToBase curveToBase =
        surfaceSndScheme ≫ curveCMEnd
  exact pullback.lift_snd _ _ _

/-- The first-factor CM map has order dividing four. -/
theorem surfaceFirstCMEnd_four :
    surfaceFirstCMEnd ≫ surfaceFirstCMEnd ≫
        surfaceFirstCMEnd ≫ surfaceFirstCMEnd = 𝟙 surface := by
  change (surfaceFirstCMEnd ≫ surfaceFirstCMEnd ≫
    surfaceFirstCMEnd ≫ surfaceFirstCMEnd) =
      𝟙 (pullback curveToBase curveToBase)
  apply pullback.hom_ext
  · change (surfaceFirstCMEnd ≫ surfaceFirstCMEnd ≫
      surfaceFirstCMEnd ≫ surfaceFirstCMEnd) ≫ surfaceFstScheme =
        𝟙 surface ≫ surfaceFstScheme
    have h₂ : (surfaceFirstCMEnd ≫ surfaceFirstCMEnd) ≫ surfaceFstScheme =
        surfaceFstScheme ≫ (curveCMEnd ≫ curveCMEnd) := by
      rw [Category.assoc, surfaceFirstCMEnd_fst]
      rw [← Category.assoc, surfaceFirstCMEnd_fst, Category.assoc]
    have h₄ :
        ((surfaceFirstCMEnd ≫ surfaceFirstCMEnd) ≫
          (surfaceFirstCMEnd ≫ surfaceFirstCMEnd)) ≫ surfaceFstScheme =
        surfaceFstScheme ≫
          ((curveCMEnd ≫ curveCMEnd) ≫ (curveCMEnd ≫ curveCMEnd)) := by
      rw [Category.assoc, h₂]
      rw [← Category.assoc, h₂, Category.assoc]
    have hc₄ : (curveCMEnd ≫ curveCMEnd) ≫
        (curveCMEnd ≫ curveCMEnd) = 𝟙 curve := by
      simpa only [Category.assoc] using curveCMEnd_four
    rw [hc₄, Category.comp_id] at h₄
    simpa only [Category.assoc, Category.id_comp] using h₄
  · change (surfaceFirstCMEnd ≫ surfaceFirstCMEnd ≫
      surfaceFirstCMEnd ≫ surfaceFirstCMEnd) ≫ surfaceSndScheme =
        𝟙 surface ≫ surfaceSndScheme
    have h₂ : (surfaceFirstCMEnd ≫ surfaceFirstCMEnd) ≫ surfaceSndScheme =
        surfaceSndScheme := by
      rw [Category.assoc, surfaceFirstCMEnd_snd,
        surfaceFirstCMEnd_snd]
    have h₄ :
        ((surfaceFirstCMEnd ≫ surfaceFirstCMEnd) ≫
          (surfaceFirstCMEnd ≫ surfaceFirstCMEnd)) ≫ surfaceSndScheme =
        surfaceSndScheme := by
      rw [Category.assoc, h₂, h₂]
    simpa only [Category.assoc, Category.id_comp] using h₄

/-- The second-factor CM map has order dividing four. -/
theorem surfaceSecondCMEnd_four :
    surfaceSecondCMEnd ≫ surfaceSecondCMEnd ≫
        surfaceSecondCMEnd ≫ surfaceSecondCMEnd = 𝟙 surface := by
  change (surfaceSecondCMEnd ≫ surfaceSecondCMEnd ≫
    surfaceSecondCMEnd ≫ surfaceSecondCMEnd) =
      𝟙 (pullback curveToBase curveToBase)
  apply pullback.hom_ext
  · change (surfaceSecondCMEnd ≫ surfaceSecondCMEnd ≫
      surfaceSecondCMEnd ≫ surfaceSecondCMEnd) ≫ surfaceFstScheme =
        𝟙 surface ≫ surfaceFstScheme
    have h₂ : (surfaceSecondCMEnd ≫ surfaceSecondCMEnd) ≫ surfaceFstScheme =
        surfaceFstScheme := by
      rw [Category.assoc, surfaceSecondCMEnd_fst,
        surfaceSecondCMEnd_fst]
    have h₄ :
        ((surfaceSecondCMEnd ≫ surfaceSecondCMEnd) ≫
          (surfaceSecondCMEnd ≫ surfaceSecondCMEnd)) ≫ surfaceFstScheme =
        surfaceFstScheme := by
      rw [Category.assoc, h₂, h₂]
    simpa only [Category.assoc, Category.id_comp] using h₄
  · change (surfaceSecondCMEnd ≫ surfaceSecondCMEnd ≫
      surfaceSecondCMEnd ≫ surfaceSecondCMEnd) ≫ surfaceSndScheme =
        𝟙 surface ≫ surfaceSndScheme
    have h₂ : (surfaceSecondCMEnd ≫ surfaceSecondCMEnd) ≫ surfaceSndScheme =
        surfaceSndScheme ≫ (curveCMEnd ≫ curveCMEnd) := by
      rw [Category.assoc, surfaceSecondCMEnd_snd]
      rw [← Category.assoc, surfaceSecondCMEnd_snd, Category.assoc]
    have h₄ :
        ((surfaceSecondCMEnd ≫ surfaceSecondCMEnd) ≫
          (surfaceSecondCMEnd ≫ surfaceSecondCMEnd)) ≫ surfaceSndScheme =
        surfaceSndScheme ≫
          ((curveCMEnd ≫ curveCMEnd) ≫ (curveCMEnd ≫ curveCMEnd)) := by
      rw [Category.assoc, h₂]
      rw [← Category.assoc, h₂, Category.assoc]
    have hc₄ : (curveCMEnd ≫ curveCMEnd) ≫
        (curveCMEnd ≫ curveCMEnd) = 𝟙 curve := by
      simpa only [Category.assoc] using curveCMEnd_four
    rw [hc₄, Category.comp_id] at h₄
    simpa only [Category.assoc, Category.id_comp] using h₄

/-- The first-factor CM endomorphism respects the surface structure map. -/
theorem surfaceFirstCMEnd_toBase :
    surfaceFirstCMEnd ≫ surfaceToBase = surfaceToBase := by
  rw [← surfaceFstScheme_toBase,
    surfaceFirstCMEnd_fst_assoc, curveCMEnd_toBase]

/-- The second-factor CM endomorphism respects the surface structure map. -/
theorem surfaceSecondCMEnd_toBase :
    surfaceSecondCMEnd ≫ surfaceToBase = surfaceToBase := by
  rw [← surfaceFstScheme_toBase, surfaceSecondCMEnd_fst_assoc]

/-- Complex multiplication on the first factor as an endomorphism over `Spec ℂ`. -/
def surfaceVarietyFirstCMEnd : surfaceVariety ⟶ surfaceVariety :=
  Over.homMk (U := surfaceVariety) (V := surfaceVariety)
    surfaceFirstCMEnd surfaceFirstCMEnd_toBase

/-- Complex multiplication on the second factor as an endomorphism over `Spec ℂ`. -/
def surfaceVarietySecondCMEnd : surfaceVariety ⟶ surfaceVariety :=
  Over.homMk (U := surfaceVariety) (V := surfaceVariety)
    surfaceSecondCMEnd surfaceSecondCMEnd_toBase

@[reassoc]
theorem surfaceVarietyFirstCMEnd_fst :
    surfaceVarietyFirstCMEnd ≫ surfaceVarietyFst =
      surfaceVarietyFst ≫ curveVarietyCMEnd := by
  apply Over.OverMorphism.ext
  exact surfaceFirstCMEnd_fst

@[reassoc]
theorem surfaceVarietyFirstCMEnd_snd :
    surfaceVarietyFirstCMEnd ≫ surfaceVarietySnd = surfaceVarietySnd := by
  apply Over.OverMorphism.ext
  exact surfaceFirstCMEnd_snd

@[reassoc]
theorem surfaceVarietySecondCMEnd_fst :
    surfaceVarietySecondCMEnd ≫ surfaceVarietyFst = surfaceVarietyFst := by
  apply Over.OverMorphism.ext
  exact surfaceSecondCMEnd_fst

@[reassoc]
theorem surfaceVarietySecondCMEnd_snd :
    surfaceVarietySecondCMEnd ≫ surfaceVarietySnd =
      surfaceVarietySnd ≫ curveVarietyCMEnd := by
  apply Over.OverMorphism.ext
  exact surfaceSecondCMEnd_snd

theorem surfaceVarietyFirstCMEnd_four :
    surfaceVarietyFirstCMEnd ≫ surfaceVarietyFirstCMEnd ≫
        surfaceVarietyFirstCMEnd ≫ surfaceVarietyFirstCMEnd =
      𝟙 surfaceVariety := by
  apply Over.OverMorphism.ext
  exact surfaceFirstCMEnd_four

theorem surfaceVarietySecondCMEnd_four :
    surfaceVarietySecondCMEnd ≫ surfaceVarietySecondCMEnd ≫
        surfaceVarietySecondCMEnd ≫ surfaceVarietySecondCMEnd =
      𝟙 surfaceVariety := by
  apply Over.OverMorphism.ext
  exact surfaceSecondCMEnd_four

/-- The analytic first-factor CM self-map of the explicit surface. -/
def surfaceFirstCMAnalyticMap :
    complexAnalytification.obj surfaceVariety ⟶
      complexAnalytification.obj surfaceVariety :=
  complexAnalytification.map surfaceVarietyFirstCMEnd

/-- The analytic second-factor CM self-map of the explicit surface. -/
def surfaceSecondCMAnalyticMap :
    complexAnalytification.obj surfaceVariety ⟶
      complexAnalytification.obj surfaceVariety :=
  complexAnalytification.map surfaceVarietySecondCMEnd

theorem surfaceFirstCMAnalyticMap_four :
    surfaceFirstCMAnalyticMap ≫ surfaceFirstCMAnalyticMap ≫
        surfaceFirstCMAnalyticMap ≫ surfaceFirstCMAnalyticMap =
      𝟙 (complexAnalytification.obj surfaceVariety) := by
  unfold surfaceFirstCMAnalyticMap
  rw [← complexAnalytification.map_comp,
    ← complexAnalytification.map_comp,
    ← complexAnalytification.map_comp,
    surfaceVarietyFirstCMEnd_four, complexAnalytification.map_id]

theorem surfaceSecondCMAnalyticMap_four :
    surfaceSecondCMAnalyticMap ≫ surfaceSecondCMAnalyticMap ≫
        surfaceSecondCMAnalyticMap ≫ surfaceSecondCMAnalyticMap =
      𝟙 (complexAnalytification.obj surfaceVariety) := by
  unfold surfaceSecondCMAnalyticMap
  rw [← complexAnalytification.map_comp,
    ← complexAnalytification.map_comp,
    ← complexAnalytification.map_comp,
    surfaceVarietySecondCMEnd_four, complexAnalytification.map_id]

end AlgebraicGeometry.ExplicitEllipticCandidate
