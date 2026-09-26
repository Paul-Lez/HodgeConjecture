/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Field.ULift
public import Other.Oka.Algebra.Category.ModuleCat.ProjectiveDimension
public import Other.Oka.AlgebraicGeometry.Modules.CoherentLocalPresentation
public import Other.Oka.AlgebraicGeometry.Modules.QuasicoherentCover
public import Other.Oka.AlgebraicGeometry.Modules.TildeExact
public import Other.Oka.Analytification.GAGA.CohomologyComparison
public import Other.Oka.Analytification.GAGA.TheoremB
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CohomologyRestrict
public import Other.Oka.Topology.Sheaves.Cohomology.Vanishing

/-!
# Vanishing of `Hᵠ(ℙⁿ_an, F^an)` for `q > n`

Let `F` be a coherent sheaf on `ℙⁿ = ℙⁿ_ℂ` and `F^an` its analytification on `ℙⁿ_an`. We show
`Hᵠ(ℙⁿ_an, F^an) = 0` for `q > n`
(`ComplexAnalytic.projectiveSpaceAn.subsingleton_H_analytificationModules_of_lt`).

The `n + 1` chart images `π⁻¹(U i)` cover `ℙⁿ_an`, so by the Mayer–Vietoris dimension bound
(`TopCat.Sheaf.subsingleton_H_of_iSup_eq_top`) it suffices that `F^an` is acyclic on every
nonempty intersection `π⁻¹(UI I)`. Given acyclicity of `𝒪_{ℙⁿ_an}` there (Theorem B,
`ComplexAnalytic.projectiveSpaceAn.subsingleton_H_restrictOpen_opensUI`), this is
`ComplexAnalytic.projectiveSpaceAn.subsingleton_H_restrictOpen_opensUI_analytificationModules`.
Its proof works for any affine open `U` of a scheme `X` locally of finite type over `ℂ` whose
coordinate ring `R` is a localisation of a polynomial ring over a field
(`ComplexAnalytic.subsingleton_H_restrictOpen_analytificationModules`):

* on `U ≅ Spec R`, `F|_U ≅ M^~` with `M = Γ(U, F)` finitely generated
  (`AlgebraicGeometry.Scheme.Modules.module_finite_Γ_restrict`);
* `M ↦ (M^~|_U)^an|_{π⁻¹ U}` is an exact additive functor to abelian sheaves on `π⁻¹ U`
  (`ComplexAnalytic.shortExact_map_analytificationTildeAb`): `M ↦ M^~` is exact
  (`AlgebraicGeometry.tilde.shortExact_map`), and so is the analytification;
* it sends `R` to `𝒪_{X^an}|_{π⁻¹ U}` (`ComplexAnalytic.analytificationTildeAbSelfIso`,
  `ComplexAnalytic.analytificationRestrictAbUnitIso`), and `F|_U` to `F^an|_{π⁻¹ U}`
  (`ComplexAnalytic.analytificationRestrictAbObjIso`);
* for such a functor, acyclicity of the image of `R` implies acyclicity of the image of every
  finitely generated `R`-module (`TopCat.Sheaf.subsingleton_H_of_isLocalization_mvPolynomial`),
  by Hilbert's syzygy theorem: projective modules are retracts of free ones, and
  `0 → K → Rᵏ → M → 0` shifts dimension.

The versions `..._of_structureSheafAb` take the acyclicity of `𝒪` on the chart intersections as
a hypothesis.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

/-- **Acyclicity along a Hilbert syzygy induction.** Let `R` be a localisation of a polynomial
ring in finitely many variables over a field, and let `Φ` be an additive functor from `R`-modules
to abelian sheaves on `Y` sending short exact sequences to short exact sequences. If `Φ(R)` has
vanishing higher cohomology, then so does `Φ(M)` for every finitely generated `R`-module `M`.

By Hilbert's syzygy theorem (`ModuleCat.induction_of_isLocalization_mvPolynomial`) it suffices to
treat finitely generated projective modules, which are retracts of some `Rⁿ`, whose image under
`Φ` is a finite sum of copies of `Φ(R)`, and to shift dimension along `0 → K → Rⁿ → M → 0`. -/
theorem TopCat.Sheaf.subsingleton_H_of_isLocalization_mvPolynomial {Y : TopCat.{u}}
    (k : Type u) [Field k] (m : ℕ) (S : Submonoid (MvPolynomial (Fin m) k)) (R : Type u)
    [CommRing R] [Algebra (MvPolynomial (Fin m) k) R] [IsLocalization S R]
    (Φ : ModuleCat.{u} R ⥤ TopCat.AbSheaf Y) [Φ.Additive]
    (hΦ : ∀ S : ShortComplex (ModuleCat.{u} R), S.ShortExact → (S.map Φ).ShortExact)
    (hR : ∀ q : ℕ, Subsingleton (TopCat.Sheaf.H (Φ.obj (ModuleCat.of R R)) (q + 1)))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (q : ℕ) :
    Subsingleton (TopCat.Sheaf.H (Φ.obj (ModuleCat.of R M)) (q + 1)) := by
  have hfree : ∀ (n q : ℕ),
      Subsingleton (TopCat.Sheaf.H (Φ.obj (ModuleCat.of R (Fin n → R))) (q + 1)) := by
    intro n q
    have key : ∑ i : Fin n, ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ ↦ R) i) ≫
        ModuleCat.ofHom (LinearMap.single R (fun _ ↦ R) i) =
          𝟙 (ModuleCat.of R (Fin n → R)) := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom,
        LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.coe_single, LinearMap.coe_proj,
        Finset.sum_apply, Function.comp_apply, Function.eval, ModuleCat.hom_id, LinearMap.id_coe,
        id_eq]
      exact Finset.univ_sum_single x
    refine TopCat.Sheaf.subsingleton_H_of_sum Finset.univ (fun _ : Fin n ↦ Φ.obj (ModuleCat.of R R))
      (fun i ↦ Φ.map (ModuleCat.ofHom (LinearMap.proj i)))
      (fun i ↦ Φ.map (ModuleCat.ofHom (LinearMap.single R (fun _ ↦ R) i))) ?_ _
      (fun _ _ ↦ hR q)
    rw [← Φ.map_id, ← key, Φ.map_sum]
    simp only [Φ.map_comp]
  let P : ∀ (M : Type u) [AddCommGroup M] [Module R M], Prop := fun M _ _ ↦
    ∀ q : ℕ, Subsingleton (TopCat.Sheaf.H (Φ.obj (ModuleCat.of R M)) (q + 1))
  have hproj : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M], P M := by
    intro M _ _ _ _ q
    obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
    haveI := hfree n q
    refine TopCat.Sheaf.subsingleton_H_of_retract (Φ.map (ModuleCat.ofHom g))
      (Φ.map (ModuleCat.ofHom f)) ?_ _
    rw [← Φ.map_comp, ← ModuleCat.ofHom_comp, hfg]
    exact Φ.map_id _
  have hstep : ∀ (K M : Type u) [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M]
      [Module.Finite R K] [Module.Finite R M] (n : ℕ) (f : K →ₗ[R] (Fin n → R))
      (g : (Fin n → R) →ₗ[R] M), Function.Exact f g → Function.Injective f →
        Function.Surjective g → P K → P M := by
    intro K M _ _ _ _ _ _ n f g hex hf hg hK q
    let S := ShortComplex.moduleCatMk f g (LinearMap.ext fun x ↦ hex.apply_apply_eq_zero x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hex
        mono_f := (ModuleCat.mono_iff_injective _).2 hf
        epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
    haveI : Subsingleton (TopCat.Sheaf.H (S.map Φ).X₂ (q + 1)) := hfree n q
    haveI : Subsingleton (TopCat.Sheaf.H (S.map Φ).X₁ (q + 1 + 1)) := hK (q + 1)
    exact TopCat.Sheaf.subsingleton_H_X₃_of_shortExact (hΦ S hS) (q + 1)
  exact ModuleCat.induction_of_isLocalization_mvPolynomial k m S R P hproj hstep M q

namespace ComplexAnalytic

variable (X : SchemeLFTℂ.{u}) (U : X.obj.left.Opens)

/-- The analytification over an open `U ⊆ X` followed by the underlying abelian sheaf. -/
def analytificationRestrictAb :
    (U : Scheme.{u}).Modules ⥤
      TopCat.AbSheaf ((analytification.obj X).restrict
        (analytificationPreimage X U)).toLocallyRingedSpace.toPresheafedSpace :=
  analytificationModulesRestrict X U ⋙ LocallyRingedSpace.modulesToAb _

instance : PreservesFiniteLimits (analytificationRestrictAb X U) := by
  haveI : PreservesFiniteLimits (analytificationModulesRestrict X U) :=
    preservesFiniteLimits_analytificationModulesRestrict X U
  exact comp_preservesFiniteLimits (analytificationModulesRestrict X U)
    (LocallyRingedSpace.modulesToAb _)

instance : PreservesFiniteColimits (analytificationRestrictAb X U) := by
  haveI : PreservesColimits (analytificationModulesRestrict X U) :=
    preservesColimits_analytificationModulesRestrict X U
  exact comp_preservesFiniteColimits (analytificationModulesRestrict X U)
    (LocallyRingedSpace.modulesToAb _)

instance : (analytificationRestrictAb X U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `(F|_U)^an`, as an abelian sheaf on `π⁻¹ U`, is the restriction of `F^an` to `π⁻¹ U`. -/
def analytificationRestrictAbObjIso
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) :
    (analytificationRestrictAb X U).obj
        ((X.obj.left.toLocallyRingedSpace.restrictModules U).obj F) ≅
      (TopCat.Sheaf.restrictOpen (analytificationPreimage X U)).obj
        ((analytificationModules X).obj F).toAb :=
  (LocallyRingedSpace.modulesToAb _).mapIso
      ((analytificationModulesRestrictIso X U).app F).symm ≪≫
    LocallyRingedSpace.restrictModulesToAbIso _ _ _

/-- `(𝒪_U)^an`, as an abelian sheaf on `π⁻¹ U`, is the restriction of `𝒪_{X^an}` to `π⁻¹ U`. -/
def analytificationRestrictAbUnitIso :
    (analytificationRestrictAb X U).obj (SheafOfModules.unit _) ≅
      (TopCat.Sheaf.restrictOpen (analytificationPreimage X U)).obj
        (SheafOfModules.unit (analytification.obj X).toLocallyRingedSpace.ringSheaf).toAb :=
  (LocallyRingedSpace.modulesToAb _).mapIso
      ((restrictπ (analytificationπ X) U).left.pullbackModulesUnitIso ≪≫
        ((analytification.obj X).toLocallyRingedSpace.ofRestrict
          (analytificationPreimage X U).isOpenEmbedding).pullbackModulesUnitIso.symm) ≪≫
    LocallyRingedSpace.restrictModulesToAbIso _ _ _

section Local

variable {X U} {R : CommRingCat.{u}} (e : (U : Scheme.{u}) ≅ Spec R)

/-- For an isomorphism `e : U ≅ Spec R`, the functor sending an `R`-module `M` to the
analytification of `e^* M^~`, as an abelian sheaf on `π⁻¹ U`. -/
def analytificationTildeAb :
    ModuleCat.{u} R ⥤ TopCat.AbSheaf ((analytification.obj X).restrict
        (analytificationPreimage X U)).toLocallyRingedSpace.toPresheafedSpace :=
  tilde.functor R ⋙ Scheme.Modules.restrictFunctor e.hom ⋙
    analytificationRestrictAb X U

instance : (analytificationTildeAb e).Additive := by
  haveI : (Scheme.Modules.restrictFunctor e.hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (Scheme.Modules.restrictFunctor e.hom ⋙ analytificationRestrictAb X U).Additive :=
    inferInstance
  exact (inferInstance : (tilde.functor R ⋙
    (Scheme.Modules.restrictFunctor e.hom ⋙ analytificationRestrictAb X U)).Additive)

/-- `M ↦ (e^* M^~)^an` is exact. -/
lemma shortExact_map_analytificationTildeAb {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) : (S.map (analytificationTildeAb e)).ShortExact :=
  ((tilde.shortExact_map hS).map_of_exact
    (Scheme.Modules.restrictFunctor e.hom)).map_of_exact (analytificationRestrictAb X U)

/-- `R^~ = 𝒪`, so `(e^* R^~)^an = 𝒪_U^an`. -/
def analytificationTildeAbSelfIso :
    (analytificationTildeAb e).obj (ModuleCat.of R R) ≅
      (analytificationRestrictAb X U).obj (SheafOfModules.unit _) :=
  (analytificationRestrictAb X U).mapIso
    ((Scheme.Modules.restrictFunctor e.hom).mapIso (tildeSelf (R := R)) ≪≫
      Scheme.Modules.restrictUnitIso e.hom)

/-- **Acyclicity of the analytification of `M^~` for a finitely generated `M` over a localised
polynomial ring**, given acyclicity of `𝒪_U^an`. -/
theorem subsingleton_H_analytificationTildeAb {k : Type u} [Field k] {m : ℕ}
    {S : Submonoid (MvPolynomial (Fin m) k)} [Algebra (MvPolynomial (Fin m) k) R]
    [IsLocalization S R]
    (hO : ∀ q : ℕ, Subsingleton (TopCat.Sheaf.H
      ((analytificationRestrictAb X U).obj (SheafOfModules.unit _)) (q + 1)))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (q : ℕ) :
    Subsingleton (TopCat.Sheaf.H ((analytificationTildeAb e).obj (ModuleCat.of R M)) (q + 1)) :=
  TopCat.Sheaf.subsingleton_H_of_isLocalization_mvPolynomial k m S R (analytificationTildeAb e)
    (fun _ hS ↦ shortExact_map_analytificationTildeAb e hS)
    (fun q ↦ by
      haveI := hO q
      exact TopCat.Sheaf.subsingleton_H_of_iso (analytificationTildeAbSelfIso e) _) M q

include e in
/-- **Acyclicity of `F^an` on `π⁻¹ U` for a coherent `F`**, when `U` is an affine open whose
coordinate ring is a localisation of a polynomial ring over a field, given acyclicity of
`𝒪_{X^an}` on `π⁻¹ U`. On `U ≅ Spec R`, `F|_U ≅ M^~` with `M = Γ(U, F)` finitely generated
(`AlgebraicGeometry.Scheme.Modules.module_finite_Γ_restrict`), and
`ComplexAnalytic.subsingleton_H_analytificationTildeAb` applies. -/
theorem subsingleton_H_restrictOpen_analytificationModules {k : Type u} [Field k] {m : ℕ}
    {S : Submonoid (MvPolynomial (Fin m) k)} [Algebra (MvPolynomial (Fin m) k) R]
    [IsLocalization S R]
    (hO : ∀ q : ℕ, Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen (analytificationPreimage X U)).obj
        (SheafOfModules.unit (analytification.obj X).toLocallyRingedSpace.ringSheaf).toAb)
      (q + 1)))
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (analytificationPreimage X U)).obj
      ((analytificationModules X).obj F).toAb) (q + 1)) := by
  have hO' : ∀ q : ℕ, Subsingleton (TopCat.Sheaf.H
      ((analytificationRestrictAb X U).obj (SheafOfModules.unit _)) (q + 1)) := fun q ↦
    (TopCat.Sheaf.H.addEquivOfIso (analytificationRestrictAbUnitIso X U)
      _).toEquiv.subsingleton_congr.2 (hO q)
  haveI : SheafOfModules.IsQuasicoherent (R := X.obj.left.ringCatSheaf) F :=
    Scheme.Modules.isQuasicoherent_of_isCoherent F
  haveI : SheafOfModules.IsFiniteType (R := X.obj.left.ringCatSheaf) F :=
    (inferInstance : F.IsFiniteType)
  let j : Spec R ⟶ X.obj.left := e.inv ≫ U.ι
  let G : (Spec R).Modules := Scheme.Modules.restrict (X := Spec R) F j
  haveI : Module.Finite R (moduleSpecΓFunctor.obj G) := Scheme.Modules.module_finite_Γ_restrict j F
  have hM := subsingleton_H_analytificationTildeAb (S := S) e hO' (moduleSpecΓFunctor.obj G) q
  let ι : (X.obj.left.toLocallyRingedSpace.restrictModules U).obj F ≅
      (Scheme.Modules.restrictFunctor e.hom).obj (tilde (moduleSpecΓFunctor.obj G)) :=
    (Scheme.Modules.restrictFunctorIsoRestrictModules X.obj.left U).symm.app F ≪≫
      (Scheme.Modules.restrictFunctorCongr (show U.ι = e.hom ≫ j by simp [j])).app F ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom j).app F ≪≫
      (Scheme.Modules.restrictFunctor e.hom).mapIso (asIso G.fromTildeΓ).symm
  exact (TopCat.Sheaf.H.addEquivOfIso ((analytificationRestrictAbObjIso X U F).symm ≪≫
    (analytificationRestrictAb X U).mapIso ι) _).toEquiv.subsingleton_congr.2 hM

end Local

end ComplexAnalytic

namespace ComplexAnalytic.projectiveSpaceAn

variable {n : ℕ}

/-- **Acyclicity of `F^an` on the chart intersections of `ℙⁿ_an`, given acyclicity of `𝒪`
there**: for coherent `F` on `ℙⁿ` and nonempty `I`, `Hᵠ(π⁻¹(UI I), F^an) = 0` for `q ≥ 1`,
provided `Hᵠ(π⁻¹(UI I), 𝒪_{ℙⁿ_an}) = 0` for `q ≥ 1` (hypothesis `hO`). The ring of `UI I` is a
localisation of `ℂ[Y₀, …, Yₙ₋₁]` (`AlgebraicGeometry.ProjectiveSpace.UIIsoSpec`). -/
theorem subsingleton_H_restrictOpen_opensUI_analytificationModules_of_structureSheafAb
    {I : Finset (Fin (n + 1))} (hI : I.Nonempty)
    (hO : ∀ q : ℕ, 0 < q → Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen (opensUI.{u} I)).obj
        (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb) q))
    (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (opensUI.{u} I)).obj
      ((analytificationModules (projectiveSpace.{u} n)).obj F).toAb) q) := by
  obtain ⟨i, hi⟩ := hI
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
  let f := MvPolynomial.dehomogenize (ULift.{u} ℂ) i (∏ j ∈ I, MvPolynomial.X j)
  letI : Algebra (MvPolynomial (Fin n) (ULift.{u} ℂ)) (CommRingCat.of (Localization.Away f)) :=
    inferInstanceAs (Algebra _ (Localization.Away f))
  haveI : IsLocalization (Submonoid.powers f) (CommRingCat.of (Localization.Away f)) :=
    inferInstanceAs (IsLocalization (Submonoid.powers f) (Localization.Away f))
  exact subsingleton_H_restrictOpen_analytificationModules (X := projectiveSpace.{u} n)
    (U := ProjectiveSpace.UI n (ULift.{u} ℂ) I) (k := ULift.{u} ℂ) (S := Submonoid.powers f)
    (ProjectiveSpace.UIIsoSpec i I hi) (fun q ↦ hO (q + 1) q.succ_pos) F q

/-- **Acyclicity of `F^an` on the chart intersections of `ℙⁿ_an`**: for coherent `F` on `ℙⁿ` and
nonempty `I`, `Hᵠ(π⁻¹(UI I), F^an) = 0` for `q ≥ 1`. -/
theorem subsingleton_H_restrictOpen_opensUI_analytificationModules
    {I : Finset (Fin (n + 1))} (hI : I.Nonempty)
    (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (opensUI.{u} I)).obj
      ((analytificationModules (projectiveSpace.{u} n)).obj F).toAb) q) :=
  subsingleton_H_restrictOpen_opensUI_analytificationModules_of_structureSheafAb hI
    (fun q hq ↦ subsingleton_H_restrictOpen_opensUI hI q hq) F q hq

/-- **`Hᵠ(ℙⁿ_an, F^an) = 0` for `q > n`, given acyclicity of `𝒪` on the chart intersections**
(hypothesis `hO`, Theorem B), for every coherent `F` on `ℙⁿ`: the `n + 1` chart images cover
`ℙⁿ_an` and `F^an` is acyclic on all their nonempty finite intersections. -/
theorem subsingleton_H_analytificationModules_of_lt_of_structureSheafAb
    (hO : ∀ I : Finset (Fin (n + 1)), I.Nonempty → ∀ q : ℕ, 0 < q →
      Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (opensUI.{u} I)).obj
        (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb) q))
    (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] (q : ℕ) (hq : n < q) :
    Subsingleton
      (LocallyRingedSpace.H ((analytificationModules (projectiveSpace.{u} n)).obj F) q) :=
  TopCat.Sheaf.subsingleton_H_of_iSup_eq_top _ chartOpens iSup_chartOpens
    (fun I hI q hq ↦ by
      rw [iInf_chartOpens]
      exact subsingleton_H_restrictOpen_opensUI_analytificationModules_of_structureSheafAb hI
        (hO I hI) F q hq)
    q (by simpa using hq)

/-- **`Hᵠ(ℙⁿ_an, F^an) = 0` for `q > n`** for every coherent sheaf `F` on `ℙⁿ`. -/
theorem subsingleton_H_analytificationModules_of_lt
    (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] (q : ℕ) (hq : n < q) :
    Subsingleton
      (LocallyRingedSpace.H ((analytificationModules (projectiveSpace.{u} n)).obj F) q) :=
  subsingleton_H_analytificationModules_of_lt_of_structureSheafAb
    (fun _ hI q hq ↦ subsingleton_H_restrictOpen_opensUI hI q hq) F q hq

end ComplexAnalytic.projectiveSpaceAn

end
