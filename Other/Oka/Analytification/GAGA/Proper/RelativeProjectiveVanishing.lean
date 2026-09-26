/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.RelativeProjectiveAn
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceVanishing

/-!
# Vanishing of `Hᵠ(B × ℙᴺ, G^an)` for `q > N`

Let `P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])` and `G` a coherent sheaf on `P`. For an open box `B ⊆ ℂᵐ` we
show `Hᵠ(tube B, G^an) = 0` for `q > N`
(`ComplexAnalytic.relProjectiveSpaceAn.subsingleton_H_tube_analytificationModules`), where
`tube B ⊆ P^an` is the preimage of `B`.

The `N + 1` opens `tube B ⊓ π⁻¹(U i)` cover `tube B`, and their nonempty intersections are the
chart pieces `tube B ⊓ π⁻¹(UI I)`, on which `𝒪` is acyclic by Theorem B on mixed domains
(`ComplexAnalytic.relProjectiveSpaceAn.subsingleton_H_tube_inf_opensUI`). The syzygy argument of
`Other/Oka/Analytification/GAGA/ProjectiveSpaceVanishing.lean` works on any open `V ⊆ π⁻¹ U` of an
affine open `U` whose ring is a localisation of a polynomial ring over a field
(`ComplexAnalytic.subsingleton_H_restrictOpen_analytificationModules_of_le`): the functor
`M ↦ (M^~)^an|_V` is still exact. The chart rings of `P` are localisations of
`A[Y₀, …, Y_{N-1}] ≅ ℂ[x₀, …, x_{N+m-1}]`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace ComplexAnalytic

variable {X : SchemeLFTℂ.{u}} {U : X.obj.left.Opens} {R : CommRingCat.{u}}
  (e : (U : Scheme.{u}) ≅ Spec R)

/-- The open `V ⊆ π⁻¹ U`, as an open of the subspace `π⁻¹ U`. -/
def analytificationPreimageOpens (V : (analytification.obj X).Opens) :
    Opens ((analytification.obj X).restrict
      (analytificationPreimage X U)).toLocallyRingedSpace.toPresheafedSpace :=
  ⟨Subtype.val ⁻¹' (V : Set (analytification.obj X)), V.isOpen.preimage continuous_subtype_val⟩

lemma functor_obj_analytificationPreimageOpens {V : (analytification.obj X).Opens}
    (hV : V ≤ analytificationPreimage X U) :
    (analytificationPreimage X U).isOpenEmbedding.isOpenMap.functor.obj
      (analytificationPreimageOpens (U := U) V) = V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hV hx⟩, hx, rfl⟩

include e in
/-- **Acyclicity of `F^an` on an open `V ⊆ π⁻¹ U` for a coherent `F`**, when `U` is an affine
open whose coordinate ring is a localisation of a polynomial ring over a field, given acyclicity
of `𝒪_{X^an}` on `V`. -/
theorem subsingleton_H_restrictOpen_analytificationModules_of_le {k : Type u} [Field k] {n : ℕ}
    {S : Submonoid (MvPolynomial (Fin n) k)} [Algebra (MvPolynomial (Fin n) k) R]
    [IsLocalization S R] {V : (analytification.obj X).Opens}
    (hV : V ≤ analytificationPreimage X U)
    (hO : ∀ q : ℕ, Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen V).obj
        (SheafOfModules.unit (analytification.obj X).toLocallyRingedSpace.ringSheaf).toAb)
      (q + 1)))
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen V).obj
      ((analytificationModules X).obj F).toAb) (q + 1)) := by
  set V' := analytificationPreimageOpens (U := U) V
  have hW := functor_obj_analytificationPreimageOpens hV
  let Φ : ModuleCat.{u} R ⥤ TopCat.AbSheaf ((Opens.toTopCat _).obj V') :=
    analytificationTildeAb e ⋙ TopCat.Sheaf.restrictOpen V'
  have hΦ : ∀ S : ShortComplex (ModuleCat.{u} R), S.ShortExact → (S.map Φ).ShortExact :=
    fun S hS ↦ (shortExact_map_analytificationTildeAb e hS).map_of_exact
      (TopCat.Sheaf.restrictOpen V')
  have hR : ∀ q : ℕ, Subsingleton (TopCat.Sheaf.H (Φ.obj (ModuleCat.of R R)) (q + 1)) := by
    intro q
    have e₁ : Φ.obj (ModuleCat.of R R) ≅ (TopCat.Sheaf.restrictOpen V').obj
        ((TopCat.Sheaf.restrictOpen (analytificationPreimage X U)).obj
          (SheafOfModules.unit (analytification.obj X).toLocallyRingedSpace.ringSheaf).toAb) :=
      (TopCat.Sheaf.restrictOpen V').mapIso
        (analytificationTildeAbSelfIso e ≪≫ analytificationRestrictAbUnitIso X U)
    exact (TopCat.Sheaf.H.addEquivOfIso e₁ _).toEquiv.subsingleton_congr.2
      ((TopCat.Sheaf.H.restrictOpenAddEquivOfEq _ V' _ _ hW).symm.toEquiv.subsingleton_congr.2
        (hO q))
  haveI : SheafOfModules.IsQuasicoherent (R := X.obj.left.ringCatSheaf) F :=
    Scheme.Modules.isQuasicoherent_of_isCoherent F
  haveI : SheafOfModules.IsFiniteType (R := X.obj.left.ringCatSheaf) F :=
    (inferInstance : F.IsFiniteType)
  let j : Spec R ⟶ X.obj.left := e.inv ≫ U.ι
  let G : (Spec R).Modules := Scheme.Modules.restrict (X := Spec R) F j
  haveI : Module.Finite R (moduleSpecΓFunctor.obj G) := Scheme.Modules.module_finite_Γ_restrict j F
  have hM := TopCat.Sheaf.subsingleton_H_of_isLocalization_mvPolynomial k n S R Φ hΦ hR
    (moduleSpecΓFunctor.obj G) q
  let ι : (X.obj.left.toLocallyRingedSpace.restrictModules U).obj F ≅
      (Scheme.Modules.restrictFunctor e.hom).obj (tilde (moduleSpecΓFunctor.obj G)) :=
    (Scheme.Modules.restrictFunctorIsoRestrictModules X.obj.left U).symm.app F ≪≫
      (Scheme.Modules.restrictFunctorCongr (show U.ι = e.hom ≫ j by simp [j])).app F ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom j).app F ≪≫
      (Scheme.Modules.restrictFunctor e.hom).mapIso (asIso G.fromTildeΓ).symm
  have e₂ : (TopCat.Sheaf.restrictOpen V').obj ((TopCat.Sheaf.restrictOpen
      (analytificationPreimage X U)).obj ((analytificationModules X).obj F).toAb) ≅
        Φ.obj (ModuleCat.of R (moduleSpecΓFunctor.obj G)) :=
    (TopCat.Sheaf.restrictOpen V').mapIso ((analytificationRestrictAbObjIso X U F).symm ≪≫
      (analytificationRestrictAb X U).mapIso ι)
  exact (TopCat.Sheaf.H.restrictOpenAddEquivOfEq _ V' _ _ hW).toEquiv.subsingleton_congr.2
    ((TopCat.Sheaf.H.addEquivOfIso e₂ _).toEquiv.subsingleton_congr.2 hM)

end ComplexAnalytic

namespace ComplexAnalytic.relProjectiveSpaceAn

open ProjectiveSpace

variable {m N : ℕ}

/-- **Acyclicity of `G^an` on the chart pieces over a box**: for coherent `G` on
`P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])`, `I` nonempty and `B` an open box,
`Hᵠ(tube B ⊓ π⁻¹(UI I), G^an) = 0` for `q ≥ 1`. -/
theorem subsingleton_H_tube_inf_opensUI_analytificationModules (a b : Fin m → ℂ)
    {B : Opens (Fin m → ℂ)} (hB : (B : Set (Fin m → ℂ)) = Complex.openBox a b)
    {I : Finset (Fin (N + 1))} (hI : I.Nonempty)
    (F : SheafOfModules.{u} (relProjectiveSpace.{u} m N).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := N) B ⊓ opensUI I)).obj
      ((analytificationModules (relProjectiveSpace.{u} m N)).obj F).toAb) q) := by
  obtain ⟨i, hi⟩ := hI
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
  let f := MvPolynomial.dehomogenize (RelBase.{u} m) i (∏ j ∈ I, MvPolynomial.X j)
  letI : Algebra (MvPolynomial (Fin (N + m)) (ULift.{u} ℂ))
      (CommRingCat.of (Localization.Away f)) :=
    ((algebraMap _ (Localization.Away f)).comp
      (relChartRingEquiv.{u} m N).symm.toRingHom).toAlgebra
  haveI : IsLocalization ((Submonoid.powers f).map (relChartRingEquiv.{u} m N))
      (CommRingCat.of (Localization.Away f)) :=
    IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers f) (Localization.Away f)
      (relChartRingEquiv.{u} m N)
  exact subsingleton_H_restrictOpen_analytificationModules_of_le
    (X := relProjectiveSpace.{u} m N) (U := ProjectiveSpace.UI N (RelBase.{u} m) I)
    (k := ULift.{u} ℂ) (S := (Submonoid.powers f).map (relChartRingEquiv.{u} m N))
    (ProjectiveSpace.UIIsoSpec i I hi) inf_le_right
    (fun q ↦ subsingleton_H_tube_inf_opensUI a b hB ⟨i, hi⟩ (q + 1) q.succ_pos) F q

/-- The opens `tube B ⊓ π⁻¹(U i)` cover `tube B`. -/
lemma iSup_tube_inf_chartOpens (B : Opens (Fin m → ℂ)) :
    ⨆ i, tube.{u} (N := N) B ⊓ chartOpens i = tube B := by
  rw [← inf_iSup_eq, iSup_chartOpens, inf_top_eq]

lemma iInf_tube_inf_chartOpens (B : Opens (Fin m → ℂ)) {I : Finset (Fin (N + 1))}
    (hI : I.Nonempty) :
    ⨅ i ∈ I, tube.{u} (N := N) B ⊓ chartOpens i = tube B ⊓ opensUI I := by
  rw [← iInf_chartOpens]
  obtain ⟨i₀, hi₀⟩ := hI
  refine le_antisymm (le_inf ((iInf₂_le i₀ hi₀).trans inf_le_left)
    (le_iInf₂ fun i hi ↦ (iInf₂_le i hi).trans inf_le_right))
    (le_iInf₂ fun i hi ↦ le_inf inf_le_left (inf_le_right.trans (iInf₂_le i hi)))

/-- **`Hᵠ(B × ℙᴺ, G^an) = 0` for `q > N`**: for coherent `G` on `P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])`
and an open box `B ⊆ ℂᵐ`, the cohomology of `G^an` on the preimage `tube B` of `B` vanishes in
degrees `q > N`. -/
theorem subsingleton_H_tube_analytificationModules (a b : Fin m → ℂ) {B : Opens (Fin m → ℂ)}
    (hB : (B : Set (Fin m → ℂ)) = Complex.openBox a b)
    (F : SheafOfModules.{u} (relProjectiveSpace.{u} m N).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] (q : ℕ) (hq : N < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := N) B)).obj
      ((analytificationModules (relProjectiveSpace.{u} m N)).obj F).toAb) q) :=
  TopCat.Sheaf.subsingleton_H_restrictOpen_of_iSup_eq _ (fun i ↦ tube.{u} (N := N) B ⊓ chartOpens i)
    (iSup_tube_inf_chartOpens B)
    (fun I hI q hq ↦ by
      rw [iInf_tube_inf_chartOpens B hI]
      exact subsingleton_H_tube_inf_opensUI_analytificationModules a b hB hI F q hq)
    q (by simpa using hq)

end ComplexAnalytic.relProjectiveSpaceAn

end
