/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.OpenImmersion
public import Other.Oka.Analytification.GAGA.ProjectiveGAGA3
public import Other.Oka.Analytification.GAGA.Proper.Chow
public import Other.Oka.Analytification.GAGA.Proper.GAGA3Induction
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PushforwardBaseChangeStalk

/-!
# GAGA-3 for proper schemes over `ℂ`

Let `X` be a proper scheme over `ℂ`. We prove `ComplexAnalytic.GenericAlgebraization X`
(`ComplexAnalytic.genericAlgebraization_of_isProperℂ`), assuming the analytic relative Serre
theorem `ComplexAnalytic.RelativeAnalyticSerre`, and deduce GAGA-3: every coherent sheaf on `X^an`
is isomorphic to the analytification of a coherent sheaf on `X` (`ComplexAnalytic.gaga₃_proper'`).

Let `T` be an irreducible closed subscheme of `X` and `M` a coherent sheaf on `T^an`. Chow's lemma
(`ComplexAnalytic.exists_chow_of_irreducibleSpace`) provides `π : T' ⟶ T`, an isomorphism over a
nonempty open `U`, and a closed immersion `j : T' ⟶ ℙᴺ`. By GAGA-3 for the projective scheme `T'`
(`ComplexAnalytic.gaga₃`), `(π^an)^* M ≅ G^an` for a coherent `G` on `T'`. For a coordinate `Xₗ`
not vanishing at some point of `π⁻¹ U` and `m ≫ 0`, the morphism
`M ⟶ π^an_* (π^an)^* M ≅ π^an_* G^an ⟶ π^an_* G(m)^an ≅ (π_* G(m))^an`
(unit, then multiplication by `Xₗᵐ`, then the inverse of the base change isomorphism) is
bijective on stalks over `π(π⁻¹ U ∩ j⁻¹ D₊(Xₗ))`, and `π_* G(m)` is coherent.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Q X Y : LocallyRingedSpace.{u}} (g : Q ⟶ X) (f : X ⟶ Y)

/-- If `g` and `g ≫ f` are open immersions, the stalk maps of `f` at the points of the image of
`g` are isomorphisms. -/
lemma Hom.isIso_stalkMap_of_isOpenImmersion_comp [IsOpenImmersion g] [IsOpenImmersion (g ≫ f)]
    (q : Q) : IsIso (f.stalkMap (g.base q)) := by
  have h : IsIso ((g ≫ f).stalkMap q) := inferInstance
  rw [stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g.stalkMap q) inferInstance h

/-- Let `g ≫ f` be an open immersion such that every point whose image under `f` lies in the
image of `g ≫ f` lies in the image of `g`. Then every open neighbourhood of a point `g q`
contains the preimage under `f` of an open neighbourhood of `f (g q)`. -/
lemma Hom.exists_preimage_le_of_isOpenImmersion_comp [IsOpenImmersion (g ≫ f)]
    (hg : ∀ x : X, f.base x ∈ Set.range (g ≫ f).base → x ∈ Set.range g.base) (q : Q)
    (W : Opens X.toPresheafedSpace) (hW : g.base q ∈ W) :
    ∃ V : Opens Y.toPresheafedSpace, f.base (g.base q) ∈ V ∧ (Opens.map f.base).obj V ≤ W := by
  have he : IsOpenEmbedding (g ≫ f).base :=
    PresheafedSpace.IsOpenImmersion.base_open (f := (g ≫ f).toHom)
  refine ⟨⟨(g ≫ f).base '' (g.base ⁻¹' W), he.isOpenMap _ (W.isOpen.preimage g.base.hom.2)⟩,
    ⟨q, hW, rfl⟩, fun x hx ↦ ?_⟩
  obtain ⟨q', hq', hx'⟩ := hx
  obtain ⟨q₁, rfl⟩ := hg x ⟨q', hx'⟩
  have : q' = q₁ := he.injective hx'
  subst this
  exact hq'

end AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic

section Local

variable {T T' : SchemeLFTℂ.{u}} (π : T' ⟶ T) (U : T.obj.left.Opens)

/-- The composite `π⁻¹ U ⟶ T' ⟶ T` of the inclusion of `π⁻¹ U` and `π : T' ⟶ T`. -/
abbrev restrictComp : T'.restrict (π.hom.left ⁻¹ᵁ U) ⟶ T :=
  T'.restrictι (π.hom.left ⁻¹ᵁ U) ≫ π

/-- The analytification of `π⁻¹ U ⟶ T' ⟶ T` is the composite of the analytifications. -/
lemma analytification_map_restrictComp :
    (analytification.map (restrictComp π U)).toLRSHom =
      (analytification.map (T'.restrictι (π.hom.left ⁻¹ᵁ U))).toLRSHom ≫
        (analytification.map π).toLRSHom := by
  rw [Functor.map_comp]
  rfl

instance (V : T'.obj.left.Opens) : IsOpenImmersion (T'.restrictι V).hom.left :=
  inferInstanceAs (IsOpenImmersion V.ι)

variable [IsIso (π.hom.left ∣_ U)]

instance : IsOpenImmersion (restrictComp π U).hom.left :=
  isOpenImmersion_ι_comp_of_isIso_morphismRestrict π.hom.left U

instance : LocallyRingedSpace.IsOpenImmersion
    ((analytification.map (T'.restrictι (π.hom.left ⁻¹ᵁ U))).toLRSHom ≫
      (analytification.map π).toLRSHom) := by
  rw [← analytification_map_restrictComp]
  infer_instance

/-- If `π` is an isomorphism over `U`, every point of `T'^an` mapping into the image of
`(π⁻¹ U)^an ⟶ T^an` lies in the image of `(π⁻¹ U)^an ⟶ T'^an`. -/
lemma mem_range_analytification_map_restrictι (x : analytification.obj T')
    (hx : (analytification.map π).toLRSHom.base x ∈
      Set.range ((analytification.map (T'.restrictι (π.hom.left ⁻¹ᵁ U))).toLRSHom ≫
        (analytification.map π).toLRSHom).base) :
    x ∈ Set.range (analytification.map (T'.restrictι (π.hom.left ⁻¹ᵁ U))).toLRSHom.base := by
  rw [← analytification_map_restrictComp, range_analytification_map] at hx
  obtain ⟨w, hw⟩ := (mem_analytificationOpenImmersionPreimage_iff _ _).1 hx
  rw [range_analytification_map_restrictι]
  have h : π.hom.left.base ((analytificationπLRS T').base x) =
      (restrictComp π U).hom.left.base w :=
    (analytificationπ_base_map π x).symm.trans hw.symm
  change π.hom.left.base ((analytificationπLRS T').base x) ∈ U
  rw [h]
  exact w.2

end Local

variable {X : SchemeLFTℂ.{u}}

/-- **Generic algebraization for proper schemes**, assuming the analytic relative Serre theorem:
for a proper scheme `X` over `ℂ`, `ComplexAnalytic.GenericAlgebraization X` holds. -/
theorem genericAlgebraization_of_isProperℂ (H : RelativeAnalyticSerre.{u})
    (hX : IsProperℂ X) : GenericAlgebraization X := by
  intro T ι hι hT M hM
  have hTp : IsProperℂ T := IsProperℂ.of_isClosedImmersion ι hX
  haveI : IsProper T.obj.hom := hTp
  haveI : CompactSpace T.obj.left := hTp.compactSpace
  obtain ⟨N, T', j, π, U, hj, hπj, ⟨t₀, ht₀⟩, hπU, -, -⟩ := exists_chow_of_irreducibleSpace T
  haveI := hπU
  haveI : IsClosedImmersion
      (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)) := hπj
  let P := π.hom.left
  let fA := (analytification.map π).toLRSHom
  -- `(π^an)^* M` is algebraic
  have hM' : (fA.pullbackModules.obj M).IsCoherent :=
    LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
      (analytification.obj T').isCoherentStructureSheaf fA M
  obtain ⟨G, hG, ⟨eG⟩⟩ := gaga₃ T' ⟨N, j, hj⟩ _ hM'
  -- a point of `π⁻¹ U` and a standard chart containing its image in `ℙᴺ`
  let w₀ : P ⁻¹ᵁ U := (inv (P ∣_ U)).base ⟨t₀, ht₀⟩
  let J : T'.obj.left ⟶ ℙₒ(N; ULift.{u} ℂ) := j.hom.left
  have h₀ : J ((P ⁻¹ᵁ U).ι w₀) ∈ ⨆ l, ProjectiveSpace.U N (ULift.{u} ℂ) l := by
    rw [ProjectiveSpace.iSup_U]
    trivial
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 h₀
  -- the twist
  obtain ⟨m₂, hm₂⟩ := H T T' π N j inferInstance hπj G hG
  obtain ⟨m₃, hm₃⟩ := exists_isCoherent_pushforward_twistAlong π j (hG := hG) G
  let m : ℕ := (max m₂ m₃).toNat
  have hm : max m₂ m₃ ≤ (m : ℤ) := Int.self_le_toNat _
  have h₂ : m₂ ≤ m := (le_max_left _ _).trans hm
  have h₃ : m₃ ≤ m := (le_max_right _ _).trans hm
  haveI := (hm₂ m h₂).2
  let μ : G ⟶ twistAlong j G m := ProjectiveSpace.mulXPowAlong J G m l
  let B := (SheafOfModules.pushforward.{u} P.toLRSHom.toRingSheafHom).obj (twistAlong j G m)
  let ψ : M ⟶ (analytificationModules T).obj B :=
    fA.pullbackModulesAdj.unit.app M ≫
      (SheafOfModules.pushforward.{u} fA.toRingSheafHom).map
        (eG.inv ≫ (analytificationModules T').map μ) ≫
      inv (analytificationPushforwardBaseChange π (twistAlong j G m))
  -- the open over which `ψ` is bijective on stalks
  let e := (restrictComp π U).hom.left
  let U' : T.obj.left.Opens :=
    e ''ᵁ ((P ⁻¹ᵁ U).ι ⁻¹ᵁ (J ⁻¹ᵁ ProjectiveSpace.U N (ULift.{u} ℂ) l))
  refine ⟨U', B, ψ, ⟨e w₀, ?_⟩, hm₃ m h₃, fun z hz ↦ ?_⟩
  · rw [SetLike.mem_coe, ← SetLike.mem_coe, Scheme.Hom.coe_image]
    exact ⟨w₀, hl, rfl⟩
  rw [← SetLike.mem_coe, Scheme.Hom.coe_image] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  -- a point `z'` of `T'^an` over `z` and over `w`
  let ιA := (analytification.map (T'.restrictι (P ⁻¹ᵁ U))).toLRSHom
  have hzr : z ∈ Set.range (ιA ≫ fA).base := by
    rw [← analytification_map_restrictComp, range_analytification_map]
    exact ⟨w, hwz⟩
  obtain ⟨q, rfl⟩ := hzr
  have hqw : (analytificationπLRS (T'.restrict (P ⁻¹ᵁ U))).base q = w := by
    refine (restrictComp π U).hom.left.isOpenEmbedding.injective (hwz.trans ?_).symm
    rw [← analytification_map_restrictComp]
    exact analytificationπ_base_map _ q
  have hf := LocallyRingedSpace.Hom.exists_preimage_le_of_isOpenImmersion_comp ιA fA
    (mem_range_analytification_map_restrictι π U) q
  haveI := LocallyRingedSpace.Hom.isIso_stalkMap_of_isOpenImmersion_comp ιA fA q
  have hμ : Function.Bijective (((analytification.obj T').toLocallyRingedSpace.stalkFunctor
      (ιA.base q)).map (eG.inv ≫ (analytificationModules T').map μ)) := by
    rw [Functor.map_comp, ConcreteCategory.coe_comp]
    refine Function.Bijective.comp
      ((analytificationπLRS T').bijective_stalkFunctor_map_pullbackModules _ μ ?_)
      ((((analytification.obj T').toLocallyRingedSpace.stalkFunctor _).mapIso
        eG.symm).toLinearEquiv.bijective)
    refine LocallyRingedSpace.bijective_stalkFunctor_map_of_bijective_app μ
      (W := J ⁻¹ᵁ ProjectiveSpace.U N (ULift.{u} ℂ) l)
      (fun V hV ↦ ProjectiveSpace.mulXPowAlong_app_bijective J G m l hV) ?_
    rw [analytificationπ_base_map, hqw]
    exact hw
  have b₁ := fA.bijective_stalkFunctor_map_unit hf M
  have b₂ := fA.bijective_stalkFunctor_map_pushforward hf _ hμ
  have b₃ := (((analytification.obj T).toLocallyRingedSpace.stalkFunctor
    (fA.base (ιA.base q))).mapIso
    (asIso (inv (analytificationPushforwardBaseChange π
      (twistAlong j G m))))).toLinearEquiv.bijective
  change Function.Bijective (((analytification.obj T).toLocallyRingedSpace.stalkFunctor
    (fA.base (ιA.base q))).map ψ)
  simp only [ψ, Functor.map_comp, ConcreteCategory.coe_comp]
  have b₄ := b₃.comp (b₂.comp b₁)
  set_option backward.isDefEq.respectTransparency false in
    simpa [B, Functor.map_comp, ConcreteCategory.coe_comp, Function.comp_def] using b₄

variable (X) in
/-- **GAGA-3 for proper schemes**, assuming the analytic relative Serre theorem
`ComplexAnalytic.RelativeAnalyticSerre`: every coherent sheaf on `X^an` is isomorphic to the
analytification of a coherent sheaf on `X`. -/
theorem gaga₃_proper' (hX : IsProperℂ X) (h : RelativeAnalyticSerre.{u})
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    [M.IsCoherent] :
    ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M) :=
  gaga₃_of_isProperℂ X hX h (genericAlgebraization_of_isProperℂ h hX) M

end ComplexAnalytic

end
