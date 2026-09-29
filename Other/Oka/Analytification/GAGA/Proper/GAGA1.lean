/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.CoherentOfFinite
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.TwistAlongMul
public import Other.Oka.Analytification.GAGA.Proper.Chow
public import Other.Oka.Analytification.GAGA.Proper.Induction
public import Other.Oka.Analytification.GAGA.Proper.PushforwardComparison
public import Other.Oka.Analytification.GAGA.Proper.RelativeSerre
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkLocal

/-!
# GAGA-1 for proper schemes over `ℂ`

Let `X` be a proper scheme over `ℂ`. We show that the comparison maps
`Hᵠ(X, F) → Hᵠ(X^an, F^an)` are bijective for every coherent `F`
(`ComplexAnalytic.gaga₁_of_isProperℂ`), assuming the analytic relative Serre theorem
`ComplexAnalytic.RelativeAnalyticSerre`: for `π : Y' ⟶ Y` and `j : Y' ⟶ ℙᴺ` such that
`(π, j) : Y' ⟶ Y × ℙᴺ` is a closed immersion, `Y` quasi-compact, and `G` coherent on `Y'`, the
twists `G(m)^an` are `π^an`-acyclic and `(π_* G(m))^an ⟶ (π^an)_* G(m)^an` is an isomorphism for
`m ≫ 0`.

By noetherian induction (`ComplexAnalytic.IsProperℂ.gagaMap_bijective_of_genericGAGA`) it
suffices to prove `ComplexAnalytic.GenericGAGA X`
(`ComplexAnalytic.genericGAGA_of_isProperℂ`). For an integral closed subscheme `Y` and a coherent
`F` on `Y`, Chow's lemma (`ComplexAnalytic.exists_chow`) provides `π : Y' ⟶ Y`, an isomorphism
over a nonempty open `U`, and `j : Y' ⟶ ℙᴺ`. With `G = π^* F`, a coordinate `Xₗ` not vanishing
at some point of `π⁻¹ U`, and `m ≫ 0`, the morphism
`F ⟶ π_* π^* F ⟶ π_* G(m)` (unit, then multiplication by `Xₗᵐ`) is bijective on stalks over
`π(π⁻¹ U ∩ j⁻¹ D₊(Xₗ))`. Its target `A = π_* G(m)` is coherent
(`ComplexAnalytic.exists_isCoherent_pushforward_twistAlong`), and its comparison maps are
bijective: `G(m)` is `π`-acyclic (`ComplexAnalytic.exists_isPushforwardAcyclic_twistAlong`), so
this reduces to GAGA-1 for `G(m)` on the projective scheme `Y'` (`ComplexAnalytic.gaga₁`) by
`ComplexAnalytic.forall_bijective_gagaMap_pushforward_iff_of_isPushforwardAcyclic`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]

/-- If `f` restricts to an isomorphism `f⁻¹ U ≅ U`, then `f⁻¹ U ⟶ Y` is an open immersion. -/
lemma isOpenImmersion_ι_comp_of_isIso_morphismRestrict : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
  rw [← morphismRestrict_ι]
  infer_instance

/-- If `f` restricts to an isomorphism `f⁻¹ U ≅ U`, every open neighbourhood of a point `x` of
`f⁻¹ U` contains the preimage of an open neighbourhood of `f x`. -/
lemma exists_preimage_le_of_isIso_morphismRestrict (w : f ⁻¹ᵁ U) (W : X.Opens)
    (hW : (f ⁻¹ᵁ U).ι w ∈ W) : ∃ V : Y.Opens, f ((f ⁻¹ᵁ U).ι w) ∈ V ∧ f ⁻¹ᵁ V ≤ W := by
  haveI := isOpenImmersion_ι_comp_of_isIso_morphismRestrict f U
  let e := (f ⁻¹ᵁ U).ι ≫ f
  refine ⟨e ''ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ W), ⟨w, hW, rfl⟩, fun z hz ↦ ?_⟩
  obtain ⟨w', hw', hzw⟩ := hz
  have hz' : z ∈ f ⁻¹ᵁ U := by
    change f z ∈ U
    rw [← hzw]
    exact w'.2
  have : w' = ⟨z, hz'⟩ := e.isOpenEmbedding.injective hzw
  subst this
  exact hw'

/-- If `f` restricts to an isomorphism `f⁻¹ U ≅ U`, the stalk maps of `f` at the points of
`f⁻¹ U` are isomorphisms. -/
lemma isIso_stalkMap_of_isIso_morphismRestrict (w : f ⁻¹ᵁ U) :
    IsIso (f.stalkMap ((f ⁻¹ᵁ U).ι w)) := by
  have h := (IsOpenImmersion.iff_isIso_stalkMap.1
    (isOpenImmersion_ι_comp_of_isIso_morphismRestrict f U)).2 w
  haveI : IsIso (f.stalkMap ((f ⁻¹ᵁ U).ι w) ≫ (f ⁻¹ᵁ U).ι.stalkMap w) := by
    rwa [← Scheme.Hom.stalkMap_comp]
  exact IsIso.of_isIso_comp_right _ ((f ⁻¹ᵁ U).ι.stalkMap w)

end AlgebraicGeometry

namespace ComplexAnalytic

/-- **The analytic relative Serre theorem**, as a hypothesis: for morphisms `π : Y' ⟶ Y` and
`j : Y' ⟶ ℙᴺ` of schemes locally of finite type over `ℂ` such that `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a
closed immersion, with `Y` quasi-compact, and every coherent `G` on `Y'`, for `m ≫ 0` the
analytification of `G(m) = G ⊗ j^* O(m)` is `π^an`-acyclic and the base change morphism
`(π_* G(m))^an ⟶ (π^an)_* G(m)^an` is an isomorphism. -/
def RelativeAnalyticSerre : Prop :=
  ∀ (Y Y' : SchemeLFTℂ.{u}) (π : Y' ⟶ Y) (N : ℕ) (j : Y' ⟶ projectiveSpace.{u} N),
    CompactSpace Y.obj.left →
    IsClosedImmersion (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) →
    ∀ G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf, G.IsCoherent →
      ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
        TopCat.Sheaf.IsPushforwardAcyclic (analytification.map π).toLRSHom.base
            ((analytificationModules Y').obj (twistAlong j G m)).toAb ∧
          IsIso (analytificationPushforwardBaseChange π (twistAlong j G m))

section Coherent

variable {Y Y' : SchemeLFTℂ.{u}} (π : Y' ⟶ Y) {N : ℕ} (j : Y' ⟶ projectiveSpace.{u} N)
  [IsClosedImmersion (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j))]

/-- **Coherence of direct images.** If `Y` is quasi-compact, for coherent `G` on `Y'` the direct
image `π_* G(m)` is coherent for `m ≫ 0`. -/
theorem exists_isCoherent_pushforward_twistAlong [CompactSpace Y.obj.left]
    (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf) [hG : G.IsCoherent] :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
      ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).obj
        (twistAlong j G m)).IsCoherent := by
  haveI : G.IsQuasicoherent := SheafOfModules.IsCoherent.isQuasicoherent G
  have hloc : ∀ y : Y.obj.left, ∃ (V : Y.obj.left.Opens) (m₀ : ℤ), IsAffineOpen V ∧ y ∈ V ∧
      ∀ m : ℤ, m₀ ≤ m → Module.Finite Γ(Y.obj.left, V)
        Γ((Scheme.Modules.pushforward π.hom.left).obj (twistAlong j G m), V) := by
    intro y
    obtain ⟨V, hV, hyV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.obj.left.Opens) from trivial)
    obtain ⟨m₀, hm₀⟩ := exists_module_finite_pushforward_twistAlong π j hV G
    exact ⟨V, m₀, hV, hyV, hm₀⟩
  choose V m₀ hV hyV hm₀ using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (V y : Set Y.obj.left))
    (fun y ↦ (V y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyV y⟩)
  refine ⟨∑ y ∈ t, |m₀ y|, fun m hm ↦ ?_⟩
  haveI : ((Scheme.Modules.pushforward π.hom.left).obj (twistAlong j G m)).IsQuasicoherent :=
    isQuasicoherent_pushforward_twistAlong π j G m
  have hc := Scheme.Modules.isCoherent_of_module_finite
    ((Scheme.Modules.pushforward π.hom.left).obj (twistAlong j G m)) fun z ↦ by
      obtain ⟨y, hyt, hz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
      exact ⟨V y, hV y, hz, hm₀ y m ((le_abs_self _).trans
        ((Finset.single_le_sum (fun y _ ↦ abs_nonneg (m₀ y)) hyt).trans hm))⟩
  exact hc

end Coherent

/-- **Generic GAGA for proper schemes**, assuming the analytic relative Serre theorem: for a
proper scheme `X` over `ℂ`, `ComplexAnalytic.GenericGAGA X` holds. -/
theorem genericGAGA_of_isProperℂ (H : RelativeAnalyticSerre.{u}) {X : SchemeLFTℂ.{u}}
    (hX : IsProperℂ X) : GenericGAGA X := by
  intro Y ι hι hY F hF
  have hYp : IsProperℂ Y := IsProperℂ.of_isClosedImmersion ι hX
  haveI : IsProper Y.obj.hom := hYp
  haveI : CompactSpace Y.obj.left := hYp.compactSpace
  obtain ⟨N, Y', j, π, U, hj, hπj, ⟨y₀, hy₀⟩, hπU, -⟩ := exists_chow Y
  haveI := hπU
  haveI : IsClosedImmersion
      (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) := hπj
  let P := π.hom.left
  let f := P.toLRSHom
  let G := f.pullbackModules.obj F
  haveI hG : G.IsCoherent :=
    LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
      Y'.obj.left.isCoherentStructureSheaf f F
  -- a point of `π⁻¹ U` and a standard chart containing its image in `ℙᴺ`
  let w₀ : P ⁻¹ᵁ U := (inv (P ∣_ U)).base ⟨y₀, hy₀⟩
  let J : Y'.obj.left ⟶ ℙₒ(N; ULift.{u} ℂ) := j.hom.left
  have h₀ : J ((P ⁻¹ᵁ U).ι w₀) ∈ ⨆ l, ProjectiveSpace.U N (ULift.{u} ℂ) l := by
    rw [ProjectiveSpace.iSup_U]
    trivial
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 h₀
  -- the twist
  obtain ⟨m₁, hm₁⟩ := exists_isPushforwardAcyclic_twistAlong π j G
  obtain ⟨m₂, hm₂⟩ := H Y Y' π N j inferInstance hπj G hG
  obtain ⟨m₃, hm₃⟩ := exists_isCoherent_pushforward_twistAlong π j G
  let m : ℕ := (max (max m₁ m₂) m₃).toNat
  have hm : max (max m₁ m₂) m₃ ≤ (m : ℤ) := Int.self_le_toNat _
  have h₁ : m₁ ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have h₂ : m₂ ≤ m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have h₃ : m₃ ≤ m := (le_max_right _ _).trans hm
  let μ : G ⟶ twistAlong j G m := ProjectiveSpace.mulXPowAlong J G m l
  let A := (SheafOfModules.pushforward.{u} f.toRingSheafHom).obj (twistAlong j G m)
  let φ : F ⟶ A :=
    f.pullbackModulesAdj.unit.app F ≫ (SheafOfModules.pushforward.{u} f.toRingSheafHom).map μ
  haveI := isOpenImmersion_ι_comp_of_isIso_morphismRestrict P U
  let e := (P ⁻¹ᵁ U).ι ≫ P
  let U' : Y.obj.left.Opens :=
    e ''ᵁ ((P ⁻¹ᵁ U).ι ⁻¹ᵁ (J ⁻¹ᵁ ProjectiveSpace.U N (ULift.{u} ℂ) l))
  refine ⟨U', A, φ, ⟨e w₀, ?_⟩, hm₃ m h₃, ?_, ?_⟩
  · rw [SetLike.mem_coe, ← SetLike.mem_coe, Scheme.Hom.coe_image]
    exact ⟨w₀, hl, rfl⟩
  · obtain ⟨hGan, hiso⟩ := hm₂ m h₂
    haveI := hiso
    haveI : (twistAlong j G m).IsCoherent := by
      haveI : SheafOfModules.IsCoherent (R := Y'.obj.left.ringCatSheaf) G := hG
      exact Scheme.Modules.isCoherent_twist (ProjectiveSpace.iSup_preimage_U J) G _
    exact (forall_bijective_gagaMap_pushforward_iff_of_isPushforwardAcyclic π _ (hm₁ m h₁)
      hGan).2 (gaga₁ Y' ⟨N, j, hj⟩ _)
  · intro y hy
    rw [← SetLike.mem_coe, Scheme.Hom.coe_image] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hf := exists_preimage_le_of_isIso_morphismRestrict P U w
    haveI : IsIso (f.stalkMap ((P ⁻¹ᵁ U).ι w)) := isIso_stalkMap_of_isIso_morphismRestrict P U w
    have hμ : Function.Bijective
        ((Y'.obj.left.toLocallyRingedSpace.stalkFunctor ((P ⁻¹ᵁ U).ι w)).map μ) :=
      LocallyRingedSpace.bijective_stalkFunctor_map_of_bijective_app μ
        (W := J ⁻¹ᵁ ProjectiveSpace.U N (ULift.{u} ℂ) l)
        (fun V hV ↦ ProjectiveSpace.mulXPowAlong_app_bijective J G m l hV) hw
    have h₁ := f.bijective_stalkFunctor_map_unit hf F
    have h₂ := f.bijective_stalkFunctor_map_pushforward hf μ hμ
    change Function.Bijective ((Y.obj.left.toLocallyRingedSpace.stalkFunctor
      (f.base ((P ⁻¹ᵁ U).ι w))).map φ)
    rw [Functor.map_comp]
    exact h₂.comp h₁

/-- **Serre's GAGA-1 for proper schemes**, assuming the analytic relative Serre theorem: for a
proper scheme `X` over `ℂ` and a coherent sheaf `F` on `X`, the comparison map
`Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective for all `q`. -/
theorem gaga₁_of_isProperℂ {X : SchemeLFTℂ.{u}} (hX : IsProperℂ X)
    (h : RelativeAnalyticSerre.{u})
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap X F q) :=
  hX.gagaMap_bijective_of_genericGAGA (genericGAGA_of_isProperℂ h hX) F q

end ComplexAnalytic

end
