/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.RelativeSerreLocalModel

/-!
# The analytic base change morphism for projective morphisms

Let `π : Y' ⟶ Y` and `j : Y' ⟶ ℙᴺ` be morphisms of schemes locally of finite type over `ℂ` such
that `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion, and let `G` be coherent on `Y'`. For an affine
open `V ⊆ Y` we show that the base change morphism `(π_* G(m))^an ⟶ (π^an)_* G(m)^an` is bijective
on the stalks at the points of `V^an` for `m ≫ 0`
(`ComplexAnalytic.exists_bijective_bcStalk_twistAlong`).

With `A = Γ(Y, V)` and a presentation `ℂ[y₀, …, y_{r-1}] → A`, the stalks are compared along
`Y' ⟶ Y ×_ℂ ℙᴺ` (a closed immersion, where base change is an isomorphism), the open immersion
`ℙₒ(N; A) ⟶ Y ×_ℂ ℙᴺ` over `Spec A ⟶ Y`, and the closed immersions `ℙₒ(N; A) ⟶ P` over
`Spec A ⟶ 𝔸ʳ`, where `P = ℙₒ(N; ℂ[y₀, …, y_{r-1}])`, using
`Other/Oka/Analytification/GAGA/Proper/BaseChangeLocal.lean`. On `P` the statement is
`ComplexAnalytic.relProjectiveSpaceAn.exists_bijective_bcStalk_twist`, applied to the coherent
sheaf obtained by pushing `G` forward to `Y ×_ℂ ℙᴺ`, restricting to `ℙₒ(N; A)` and pushing forward to
`P`; twisting commutes with all of these (`ComplexAnalytic.pushforwardTwistAlongIso`,
`ComplexAnalytic.pushforwardMapTwistIso`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace ComplexAnalytic

open ProjectiveSpace

variable {Y Y' : SchemeLFTℂ.{u}} (π : Y' ⟶ Y) {N : ℕ} (j : Y' ⟶ projectiveSpace.{u} N)

/-- Twisting along `j = pr₂ ∘ (π, j)` commutes with pushforward along `(π, j)`. -/
def pushforwardTwistAlongIso (G : Y'.obj.left.Modules) (m : ℤ) :
    (pushforward (Y.relProjLift π j).hom.left).obj (ProjectiveSpace.twistAlong j.hom.left G m) ≅
      ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left
        ((pushforward (Y.relProjLift π j).hom.left).obj G) m :=
  (pushforward _).mapIso (twistComapIsoOfEq (pullback.lift_snd _ _ _).symm _ G ≪≫
    (twistComapCompIso _ _ _ G).symm) ≪≫ pushforwardTwistComapIso _ _ G

/-- Twisting commutes with pushforward along the embedding of `ℙₒ(N; A)` given by a
presentation `ℂ[y₀, …, y_{r-1}] → A`. -/
def pushforwardMapTwistIso {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (F : ℙₒ(N; A).Modules) (m : ℤ) :
    (pushforward (ProjectiveSpace.map (n := N) f)).obj (ProjectiveSpace.twist F m) ≅
      ProjectiveSpace.twist ((pushforward (ProjectiveSpace.map f)).obj F) m :=
  (pushforward _).mapIso (twistIsoOfIsPullback (map f) (fun i ↦ (map_preimage_U f i).symm)
    (cocycle N R ^ m) (cocycle N A ^ m) ((cocycle_isPullback f).zpow m) F).symm ≪≫
    pushforwardTwistComapIso _ _ F


/-- Schemes locally of finite type over `ℂ` are locally noetherian. -/
lemma SchemeLFTℂ.isLocallyNoetherian (X : SchemeLFTℂ.{u}) : IsLocallyNoetherian X.obj.left := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian X.obj.hom

variable [IsClosedImmersion (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j))]

instance : IsClosedImmersion (Y.relProjLift π j).hom.left :=
  inferInstanceAs (IsClosedImmersion
    (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)))

/-- **The analytic base change morphism for `G(m)`, `m ≫ 0`, over an affine open**: for coherent `G`
on `Y'` and an affine open `V ⊆ Y` there is `m₀` such that `(π_* G(m))^an ⟶ (π^an)_* G(m)^an` is
bijective on the stalks at the points of `V^an` for `m ≥ m₀`. -/
theorem exists_bijective_bcStalk_twistAlong
    (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf) [hG : G.IsCoherent]
    {V : Y.obj.left.Opens} (hV : IsAffineOpen V) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∀ v : analytification.obj (Y.affineSpec hV),
      Function.Bijective (bcStalk π (twistAlong j G m)
        ((analytification.map (Y.affineSpecι hV)).toLRSHom.base v)) := by
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
  obtain ⟨n₀, hn₀⟩ := relProjectiveSpaceAn.exists_bijective_bcStalk_twist (m := r) (N := N) H
  refine ⟨n₀, fun m hm v ↦ ?_⟩
  have h7 : Function.Bijective (bcStalk (Y.affineProjEmb N hV hs ≫ relProjectiveSpaceToAffine r N)
      (ProjectiveSpace.twist FA m)
        ((analytification.map (Y.affineSpecEmb hV hs)).toLRSHom.base v)) :=
    bijective_bcStalk_comp _ _ _ _ ((bijective_bcStalk_iff_of_iso _
      (pushforwardMapTwistIso s FA m) _).2 (hn₀ m hm _))
  have h6 : Function.Bijective (bcStalk (Y.affineProjToSpec N hV) (ProjectiveSpace.twist FA m) v) :=
    bijective_bcStalk_of_comp _ _ _ v (by rw [← Y.affineProjEmb_comp]; exact h7)
  have h5 : Function.Bijective (bcStalk (Y.affineProjToSpec N hV)
      ((Y.affineProjChart N hV).hom.left.toLRSHom.pullbackModules.obj
        (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m)) v) :=
    let e5 : (Y.affineProjChart N hV).hom.left.toLRSHom.pullbackModules.obj
        (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m) ≅ ProjectiveSpace.twist FA m :=
      ((restrictFunctorIsoPullbackModules (Y.affineProjChart N hV).hom.left).app
        (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m)).symm ≪≫
        restrictTwistIso Y.obj.hom hV (Y.relProjLift π j).hom.left G m
    (bijective_bcStalk_iff_of_iso _ e5 v).2 h6
  have h4 := bijective_bcStalk_of_isOpenImmersion (Y.relProjFst N) (Y.affineProjToSpec N hV)
    (Y.affineSpecι hV) (Y.affineProjChart N hV) (Y.affineProjToSpec_comp_affineSpecι hV)
    (fun z hz ↦ Y.mem_range_affineProjChart hV z hz) _ v h5
  have h2 := bijective_bcStalk_comp (Y.relProjLift π j) (Y.relProjFst N) (twistAlong j G m) _
    ((bijective_bcStalk_iff_of_iso _ (pushforwardTwistAlongIso π j G m) _).2 h4)
  rwa [Y.relProjLift_fst] at h2

end ComplexAnalytic

end
