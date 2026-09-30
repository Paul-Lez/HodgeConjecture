/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.RelativeAnalyticSerreBaseChange
public import Other.Oka.Topology.Sheaves.Cohomology.ClosedEmbeddingOpen
public import Other.Oka.Topology.Sheaves.Cohomology.OpenEmbeddingPushforward

/-!
# Relative analytic Serre vanishing for projective morphisms

Let `π : Y' ⟶ Y` and `j : Y' ⟶ ℙᴺ` be morphisms of schemes locally of finite type over `ℂ` such
that `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion, and let `G` be coherent on `Y'`. For an affine
open `V ⊆ Y` we show that for `m ≫ 0` every neighbourhood of a point of `V^an` contains an open
neighbourhood `V'` with `Hᵠ((π^an)⁻¹ V', G(m)^an) = 0` for `q ≥ 1`
(`ComplexAnalytic.exists_HVanishesOn_twistAlong`); `V'` is the part of `V^an` over a small box in
`ℂʳ` for a presentation of `Γ(Y, V)`.

Vanishing of cohomology on an open (`ComplexAnalytic.HVanishesOn`) is transported along the
closed embedding `(π, j)^an` (`HVanishesOn.of_pushforward_closedEmbedding`), isomorphisms of sheaves
(`HVanishesOn.of_iso`), the morphism `F^an ⟶ u^an_* (u^* F)^an` for the open immersion
`u : ℙₒ(N; Γ(Y, V)) ⟶ Y ×_ℂ ℙᴺ`, which is bijective on stalks over the image of `u^an`
(`ComplexAnalytic.bijective_stalk_unit_comp_bc`, `HVanishesOn.of_bijective`), pushforward along
`u^an` (`HVanishesOn.pushforward_of_openEmbedding`) and the closed embedding
`ℙₒ(N; Γ(Y, V))^an ⟶ P^an`, where `P = ℙₒ(N; ℂ[y₀, …, y_{r-1}])`, down to the vanishing over boxes
`ComplexAnalytic.relProjectiveSpaceAn.exists_H_tube_twist_eq_zero`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Topology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.LocallyRingedSpace

universe u

noncomputable section

namespace ComplexAnalytic

open ProjectiveSpace

/-- The cohomology of `M` vanishes in positive degrees on the open `W`. -/
def HVanishesOn {X : LocallyRingedSpace.{u}} (M : SheafOfModules.{u} X.ringSheaf)
    (W : Opens X.toPresheafedSpace) : Prop :=
  ∀ (q : ℕ) (c : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj M.toAb) (q + 1)), c = 0

lemma HVanishesOn.of_addEquiv {X X' : LocallyRingedSpace.{u}} {M : SheafOfModules.{u} X.ringSheaf}
    {M' : SheafOfModules.{u} X'.ringSheaf} {W : Opens X.toPresheafedSpace}
    {W' : Opens X'.toPresheafedSpace}
    (e : ∀ q, TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj M.toAb) (q + 1) ≃+
      TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W').obj M'.toAb) (q + 1))
    (h : HVanishesOn M' W') : HVanishesOn M W :=
  fun q c ↦ (e q).injective (by rw [h q (e q c), map_zero])

lemma HVanishesOn.of_iso {X : LocallyRingedSpace.{u}} {M M' : SheafOfModules.{u} X.ringSheaf}
    (e : M ≅ M') {W : Opens X.toPresheafedSpace} (h : HVanishesOn M' W) : HVanishesOn M W :=
  fun q c ↦ by
    let e' : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj M.toAb) (q + 1) ≃+
        TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj M'.toAb) (q + 1) :=
      TopCat.Sheaf.H.restrictOpenAddEquivOfIso (Y := X.toPresheafedSpace) W
        ((modulesToAb X).mapIso e) (q + 1)
    exact e'.injective ((h q (e' c)).trans (map_zero e').symm)

/-- Vanishing along closed embeddings: the cohomology of `M` on `f⁻¹ W` vanishes if the cohomology
of `f_* M` on `W` does. -/
lemma HVanishesOn.of_pushforward_closedEmbedding {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hf : IsClosedEmbedding f.base) {M : SheafOfModules.{u} X.ringSheaf}
    {W : Opens Y.toPresheafedSpace}
    (h : HVanishesOn ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj M) W) :
    HVanishesOn M ((Opens.map f.base).obj W) :=
  fun q c ↦ by
    let e' := TopCat.Sheaf.H.restrictOpenPushforwardClosedEmbeddingAddEquiv
      (X := Y.toPresheafedSpace) (Y := X.toPresheafedSpace) (f := f.base) hf M.toAb W (q + 1)
    exact e'.injective ((h q (e' c)).trans (map_zero e').symm)

/-- Vanishing along open embeddings: the cohomology of `f_* N` on `f(U)` vanishes if the
cohomology of `N` on `U` does. -/
lemma HVanishesOn.pushforward_of_openEmbedding {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hf : IsOpenEmbedding f.base) {N : SheafOfModules.{u} X.ringSheaf}
    {U : Opens X.toPresheafedSpace} (h : HVanishesOn N U) {W : Opens Y.toPresheafedSpace}
    (hW : hf.isOpenMap.functor.obj U = W) :
    HVanishesOn ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj N) W :=
  fun q c ↦ by
    let e' := TopCat.Sheaf.H.restrictOpenPushforwardOpenEmbeddingAddEquiv (X := Y.toPresheafedSpace)
      (Y := X.toPresheafedSpace) (f := f.base) hf N.toAb U hW (q + 1)
    exact e'.injective ((h q (e' c)).trans (map_zero e').symm)

/-- Vanishing is invariant under morphisms which are bijective on the stalks over `W`. -/
lemma HVanishesOn.of_bijective {X : LocallyRingedSpace.{u}} {M M' : SheafOfModules.{u} X.ringSheaf}
    (φ : M ⟶ M') {W : Opens X.toPresheafedSpace}
    (hφ : ∀ x ∈ W, Function.Bijective ((X.stalkFunctor x).map φ)) (h : HVanishesOn M' W) :
    HVanishesOn M W :=
  fun q c ↦ by
    let e' := TopCat.Sheaf.H.restrictOpenAddEquivOfBijective (X := X.toPresheafedSpace)
      ((modulesToAb X).map φ) W
      (fun V hV ↦ bijective_app_of_bijective_stalkFunctor_map φ V fun x hx ↦ hφ x (hV hx)) (q + 1)
    exact e'.injective ((h q (e' c)).trans (map_zero e').symm)


/-- For an open immersion `u : V ⟶ Y`, the morphism `F^an ⟶ u^an_* (u^* F)^an` (the analytification
of the unit, followed by the base change morphism) is bijective on the stalks at the points of
`V^an`. -/
lemma bijective_stalk_unit_comp_bc {V Y : SchemeLFTℂ.{u}} (u : V ⟶ Y) [IsOpenImmersion u.hom.left]
    (F : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf)
    (z : analytification.obj V) :
    Function.Bijective (((analytification.obj Y).toLocallyRingedSpace.stalkFunctor
      ((analytification.map u).toLRSHom.base z)).map
        ((analytificationModules Y).map (u.hom.left.toLRSHom.pullbackModulesAdj.unit.app F) ≫
          analytificationPushforwardBaseChange u (u.hom.left.toLRSHom.pullbackModules.obj F))) := by
  refine Functor.bijective_map_comp _ _ _ ?_
    (bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_isOpenEmbedding
      (analytificationπLRS_naturality u) u.hom.left.isOpenEmbedding
      (isOpenEmbedding_analytification_map u) _ z)
  refine (analytificationπLRS Y).bijective_stalkFunctor_map_pullbackModules _ _ ?_
  have h := u.hom.left.toLRSHom.bijective_stalkFunctor_map_unit
    (x := (analytificationπLRS V).base z)
    (fun W hW ↦ u.hom.left.toLRSHom.exists_preimage_le_of_isInducing
      u.hom.left.isOpenEmbedding.isInducing W hW) F
  rw [← analytificationπ_base_map u z] at h
  exact h


variable {Y Y' : SchemeLFTℂ.{u}} (π : Y' ⟶ Y) {N : ℕ} (j : Y' ⟶ projectiveSpace.{u} N)
  [IsClosedImmersion (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j))]

/-- **Relative analytic Serre vanishing for `G(m)`, `m ≫ 0`, over an affine open**: for coherent
`G` on `Y'` and an affine open `V ⊆ Y` there is `m₀` such that for `m ≥ m₀` every neighbourhood of
a point of `V^an` contains an open neighbourhood `V'` with `Hᵠ((π^an)⁻¹ V', G(m)^an) = 0` for all
`q ≥ 1`. -/
theorem exists_HVanishesOn_twistAlong
    (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf) [hG : G.IsCoherent]
    {V : Y.obj.left.Opens} (hV : IsAffineOpen V) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∀ (v : analytification.obj (Y.affineSpec hV))
      (O : (analytification.obj Y).Opens),
      (analytification.map (Y.affineSpecι hV)).toLRSHom.base v ∈ O →
        ∃ V' ≤ O, (analytification.map (Y.affineSpecι hV)).toLRSHom.base v ∈ V' ∧
          HVanishesOn ((analytificationModules Y').obj (twistAlong j G m))
            ((Opens.map (analytification.map π).toLRSHom.base).obj V') := by
  obtain ⟨r, s, hsurj, hs⟩ := Y.exists_presentation hV
  haveI := Y'.isLocallyNoetherian
  haveI := (Y.relProj N).isLocallyNoetherian
  haveI := (Y.affineProj N hV).isLocallyNoetherian
  haveI := (relProjectiveSpace.{u} r N).isLocallyNoetherian
  haveI := Y.isClosedImmersion_affineSpecEmb hV hs hsurj
  haveI := Y.isClosedImmersion_affineProjEmb (N := N) hV hs hsurj
  haveI : SheafOfModules.IsCoherent (R := Y'.obj.left.ringCatSheaf) G := hG
  let F := (pushforward (Y.relProjLift π j).hom.left).obj G
  haveI : F.IsCoherent := isCoherent_pushforward _ G
  let FA := F.restrict (Y.affineProjChart N hV).hom.left
  haveI : FA.IsCoherent := isCoherent_restrict _ F
  let H := (pushforward (Y.affineProjEmb N hV hs).hom.left).obj FA
  haveI : H.IsCoherent := isCoherent_pushforward _ FA
  haveI : SheafOfModules.IsCoherent (R := ℙₒ(N; RelBase.{u} r).ringCatSheaf) H := ‹_›
  obtain ⟨n₀, hn₀⟩ := relProjectiveSpaceAn.exists_H_tube_twist_eq_zero (m := r) (N := N) H
  refine ⟨n₀, fun m hm v O hvO ↦ ?_⟩
  let ua := (analytification.map (Y.affineSpecι hV)).toLRSHom
  let ka := (analytification.map (Y.affineSpecEmb hV hs)).toLRSHom
  have hua : IsOpenEmbedding ua.base := isOpenEmbedding_analytification_map _
  obtain ⟨t, ht, hts⟩ := (isClosedEmbedding_analytification_map (Y.affineSpecEmb hV hs)).isInducing
    |>.isOpen_iff.1 ((Opens.map ua.base).obj O).isOpen
  have hvt : ka.base v ∈ t := by
    change v ∈ ka.base ⁻¹' t
    rw [hts]
    exact hvO
  obtain ⟨a, b, hvB, hBt⟩ := relProjectiveSpaceAn.exists_baseAnOpens_box_subset (O := ⟨t, ht⟩) hvt
  let W₀ := (Opens.map ka.base).obj
    (relProjectiveSpaceAn.baseAnOpens.{u} (relProjectiveSpaceAn.boxOpens a b))
  refine ⟨hua.isOpenMap.functor.obj W₀, ?_, ⟨v, hvB, rfl⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have h1 : w ∈ ka.base ⁻¹' t := hBt hw
    rw [hts] at h1
    exact h1
  -- reduce to `Y ×_ℂ ℙᴺ` along the closed immersion `(π, j)`
  have hπ : (analytification.map π).toLRSHom =
      (analytification.map (Y.relProjLift π j)).toLRSHom ≫
        (analytification.map (Y.relProjFst N)).toLRSHom := by
    have := congrArg (fun f ↦ (analytification.map f).toLRSHom) (Y.relProjLift_fst π j)
    simp only [Functor.map_comp] at this
    exact this.symm
  rw [hπ]
  refine HVanishesOn.of_pushforward_closedEmbedding (W := (Opens.map
    (analytification.map (Y.relProjFst N)).toLRSHom.base).obj (hua.isOpenMap.functor.obj W₀)) _
    (isClosedEmbedding_analytification_map (Y.relProjLift π j)) ?_
  haveI := isIso_analytificationPushforwardBaseChange (Y.relProjLift π j) (twistAlong j G m)
  let e₁ : (SheafOfModules.pushforward.{u}
      (analytification.map (Y.relProjLift π j)).toLRSHom.toRingSheafHom).obj
        ((analytificationModules Y').obj (twistAlong j G m)) ≅
      (analytificationModules (Y.relProj N)).obj
        (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m) :=
    (asIso (analytificationPushforwardBaseChange (Y.relProjLift π j) (twistAlong j G m))).symm ≪≫
      (analytificationModules (Y.relProj N)).mapIso (pushforwardTwistAlongIso π j G m)
  refine HVanishesOn.of_iso e₁ ?_
  -- restrict to `ℙₒ(N; Γ(Y, V))` along the open immersion `u'`
  let u' := Y.affineProjChart N hV
  let θ := u'.hom.left.toLRSHom.pullbackModulesAdj.unit.app
    (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m)
  have hc' : ∀ x, (analytification.map (Y.relProjFst N)).toLRSHom.base x ∈ Set.range ua.base →
      x ∈ Set.range (analytification.map u').toLRSHom.base := by
    intro x hx
    rw [range_analytification_map] at hx ⊢
    change (analytificationπLRS Y).base ((analytification.map (Y.relProjFst N)).toLRSHom.base x) ∈
      Set.range (Y.affineSpecι hV).hom.left.base at hx
    rw [analytificationπ_base_map] at hx
    exact Y.mem_range_affineProjChart hV _ hx
  refine HVanishesOn.of_bijective ((analytificationModules (Y.relProj N)).map θ ≫
    analytificationPushforwardBaseChange u' (u'.hom.left.toLRSHom.pullbackModules.obj
      (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m))) (fun x hx ↦ ?_) ?_
  · obtain ⟨w, rfl⟩ := hc' x (by obtain ⟨w, -, hw⟩ := hx; exact ⟨w, hw⟩)
    exact bijective_stalk_unit_comp_bc u' _ w
  have hsq : (analytification.map (Y.affineProjToSpec N hV)).toLRSHom ≫ ua =
      (analytification.map u').toLRSHom ≫ (analytification.map (Y.relProjFst N)).toLRSHom := by
    have := congrArg (fun f ↦ (analytification.map f).toLRSHom)
      (Y.affineProjToSpec_comp_affineSpecι (N := N) hV)
    simp only [Functor.map_comp] at this
    exact this
  have hW : (isOpenEmbedding_analytification_map u').isOpenMap.functor.obj
      ((Opens.map (analytification.map (Y.affineProjToSpec N hV)).toLRSHom.base).obj W₀) =
      (Opens.map (analytification.map (Y.relProjFst N)).toLRSHom.base).obj
        (hua.isOpenMap.functor.obj W₀) := by
    ext x
    constructor
    · rintro ⟨w', hw', rfl⟩
      exact ⟨_, hw', congr($(hsq).base w')⟩
    · rintro ⟨w, hw, hwx⟩
      obtain ⟨w', rfl⟩ := hc' x ⟨w, hwx⟩
      refine ⟨w', ?_, rfl⟩
      have h1 : ua.base ((analytification.map (Y.affineProjToSpec N hV)).toLRSHom.base w') =
          ua.base w := (congr($(hsq).base w')).trans hwx.symm
      change (analytification.map (Y.affineProjToSpec N hV)).toLRSHom.base w' ∈ W₀
      rw [hua.injective h1]
      exact hw
  refine HVanishesOn.pushforward_of_openEmbedding _ (isOpenEmbedding_analytification_map u') ?_ hW
  let e₅ : u'.hom.left.toLRSHom.pullbackModules.obj
      (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m) ≅ ProjectiveSpace.twist FA m :=
    ((restrictFunctorIsoPullbackModules u'.hom.left).app
      (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m)).symm ≪≫
      restrictTwistIso Y.obj.hom hV (Y.relProjLift π j).hom.left G m
  refine HVanishesOn.of_iso ((analytificationModules (Y.affineProj N hV)).mapIso e₅) ?_
  -- push forward to `ℙₒ(N; ℂ[y₀, …, y_{r-1}])` along the closed immersion given by `s`
  have hsq' : (analytification.map (Y.affineProjToSpec N hV)).toLRSHom ≫ ka =
      (analytification.map (Y.affineProjEmb N hV hs)).toLRSHom ≫
        (analytification.map (relProjectiveSpaceToAffine r N)).toLRSHom := by
    have := congrArg (fun f ↦ (analytification.map f).toLRSHom)
      (Y.affineProjEmb_comp (N := N) hV hs)
    simp only [Functor.map_comp] at this
    exact this.symm
  have hop : (Opens.map (analytification.map (Y.affineProjToSpec N hV)).toLRSHom.base).obj W₀ =
      (Opens.map (analytification.map (Y.affineProjEmb N hV hs)).toLRSHom.base).obj
        ((Opens.map (analytification.map (relProjectiveSpaceToAffine r N)).toLRSHom.base).obj
          (relProjectiveSpaceAn.baseAnOpens.{u} (relProjectiveSpaceAn.boxOpens a b))) :=
    by
    ext w
    change ka.base ((analytification.map (Y.affineProjToSpec N hV)).toLRSHom.base w) ∈
      relProjectiveSpaceAn.baseAnOpens.{u} (relProjectiveSpaceAn.boxOpens a b) ↔
      (analytification.map (relProjectiveSpaceToAffine r N)).toLRSHom.base
        ((analytification.map (Y.affineProjEmb N hV hs)).toLRSHom.base w) ∈
        relProjectiveSpaceAn.baseAnOpens.{u} (relProjectiveSpaceAn.boxOpens a b)
    rw [show ka.base ((analytification.map (Y.affineProjToSpec N hV)).toLRSHom.base w) =
      (analytification.map (relProjectiveSpaceToAffine r N)).toLRSHom.base
        ((analytification.map (Y.affineProjEmb N hV hs)).toLRSHom.base w) from
      congr($(hsq').base w)]
  rw [hop]
  refine HVanishesOn.of_pushforward_closedEmbedding _
    (isClosedEmbedding_analytification_map (Y.affineProjEmb N hV hs)) ?_
  haveI := isIso_analytificationPushforwardBaseChange (Y.affineProjEmb N hV hs)
    (ProjectiveSpace.twist FA m)
  let e₂ : (SheafOfModules.pushforward.{u}
      (analytification.map (Y.affineProjEmb N hV hs)).toLRSHom.toRingSheafHom).obj
        ((analytificationModules (Y.affineProj N hV)).obj (ProjectiveSpace.twist FA m)) ≅
      (analytificationModules (relProjectiveSpace r N)).obj (ProjectiveSpace.twist H m) :=
    (asIso (analytificationPushforwardBaseChange (Y.affineProjEmb N hV hs)
      (ProjectiveSpace.twist FA m))).symm ≪≫
      (analytificationModules (relProjectiveSpace r N)).mapIso (pushforwardMapTwistIso s FA m)
  refine HVanishesOn.of_iso e₂ ?_
  exact fun q c ↦ hn₀ m hm a b (relProjectiveSpaceAn.boxOpens a b) rfl q c

end ComplexAnalytic

end
