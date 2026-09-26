/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.QuasicoherentSections

/-!
# Sections of quasi-coherent sheaves over basic opens of quasi-compact opens

Let `F` be a quasi-coherent `𝒪_X`-module and `W ⊆ X` an open covered by finitely many affine
opens `Wᵢ` with affine pairwise intersections. For `φ ∈ Γ(X, W)` the restriction
`Γ(F, W) → Γ(F, D(φ))` is the localisation away from `φ`, in the following elementwise forms:

- `AlgebraicGeometry.exists_restrictOpen_eq_pow_smul_of_cover`: every `s ∈ Γ(F, D(φ))` has some
  `φᵏ s` extending to a section over `W`;
- `AlgebraicGeometry.exists_pow_smul_eq_zero_of_cover`: a section over `W` vanishing on `D(φ)`
  is killed by a power of `φ` (this only needs the `Wᵢ` to be affine).

As an application we show:

- `AlgebraicGeometry.IsAffineOpen.isLocalizing_restrict_fromSpec`: an `𝒪_X`-module whose sections
  over an affine open `U` satisfy the two properties above for all `f ∈ Γ(X, U)` restricts to a
  localizing sheaf on `Spec Γ(X, U)`;
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_presentation_restrict`: an `𝒪_X`-module
  with a presentation on each member of an open cover is quasi-coherent;
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_cover`: the pushforward of a
  quasi-coherent sheaf along `π : Y' ⟶ Y` is quasi-coherent if the preimage of every affine open
  of `Y` is covered by finitely many affine opens with affine pairwise intersections (e.g. `π`
  quasi-compact and `Y'` separated).
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

namespace Scheme.Modules

/-- Restriction commutes with multiplication by a power. -/
lemma mres_pow_smul (F : X.Modules) {V U : X.Opens} (h : U ≤ V) (r : Γ(X, V)) (k : ℕ)
    (x : Γ(F, V)) :
    TopCat.Presheaf.restrictOpen (r ^ k • x) U h =
      TopCat.Presheaf.restrictOpen r U h ^ k • TopCat.Presheaf.restrictOpen x U h := by
  rw [mres_smul, ores_pow]

end Scheme.Modules

/-- The basic open of the restriction of `f` is monotone in the open restricted to. -/
lemma Scheme.basicOpen_restrictOpen_mono {V W W' : X.Opens} (h : W' ≤ W) (h' : W ≤ V)
    (f : Γ(X, V)) :
    X.basicOpen (TopCat.Presheaf.restrictOpen f W' (h.trans h')) ≤
      X.basicOpen (TopCat.Presheaf.restrictOpen f W h') := by
  rw [Scheme.basicOpen_restrictOpen, Scheme.basicOpen_restrictOpen]
  exact inf_le_inf_right _ h

private lemma pow_smul_eq_zero_of_le' {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : R} {x : M} {k K : ℕ} (hk : k ≤ K) (h : r ^ k • x = 0) : r ^ K • x = 0 := by
  rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, h, smul_zero]

section Cover

variable (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} {ι : Type*} [Finite ι]
  (Wi : ι → X.Opens) (hW : ⨆ i, Wi i = W)

include hW in
/-- **Sections vanishing on a basic open.** Let `F` be quasi-coherent and `W` a finite union of
affine opens. A section of `F` over `W` whose restriction to `D(φ)` vanishes is killed by a power
of `φ`. -/
theorem exists_pow_smul_eq_zero_of_cover (hWi : ∀ i, IsAffineOpen (Wi i)) (φ : Γ(X, W))
    (t : Γ(F, W))
    (ht : TopCat.Presheaf.restrictOpen t (X.basicOpen φ) (X.basicOpen_le φ) = 0) :
    ∃ k : ℕ, φ ^ k • t = 0 := by
  have hle i : Wi i ≤ W := hW ▸ le_iSup Wi i
  have hk i : ∃ k : ℕ, TopCat.Presheaf.restrictOpen φ (Wi i) (hle i) ^ k •
      TopCat.Presheaf.restrictOpen t (Wi i) (hle i) = 0 := by
    refine (hWi i).exists_pow_smul_eq_zero F _ _ ?_
    have hD : X.basicOpen (TopCat.Presheaf.restrictOpen φ (Wi i) (hle i)) ≤ X.basicOpen φ := by
      rw [Scheme.basicOpen_restrictOpen]
      exact inf_le_right
    rw [mres_res, ← mres_res F (X.basicOpen_le φ) hD, ht, mres_zero]
  choose k hk using hk
  obtain ⟨K, hK⟩ := (Set.finite_range k).bddAbove
  refine ⟨K, mres_eq_of_locally_eq F Wi hW.ge hle _ _ fun i ↦ ?_⟩
  rw [mres_pow_smul, mres_zero]
  exact pow_smul_eq_zero_of_le' (hK ⟨i, rfl⟩) (hk i)
include hW in
/-- **Extension of sections from a basic open.** Let `F` be quasi-coherent and `W` a finite union
of affine opens `Wᵢ` with affine pairwise intersections. For `φ ∈ Γ(X, W)`, every
`s ∈ Γ(F, D(φ))` has some `φᵏ s` extending to a section over `W`. -/
theorem exists_restrictOpen_eq_pow_smul_of_cover (hWi : ∀ i, IsAffineOpen (Wi i))
    (hWij : ∀ i j, IsAffineOpen (Wi i ⊓ Wi j)) (φ : Γ(X, W)) (s : Γ(F, X.basicOpen φ)) :
    ∃ (k : ℕ) (t : Γ(F, W)), TopCat.Presheaf.restrictOpen t (X.basicOpen φ) (X.basicOpen_le φ) =
      TopCat.Presheaf.restrictOpen φ (X.basicOpen φ) (X.basicOpen_le φ) ^ k • s := by
  have hle i : Wi i ≤ W := hW ▸ le_iSup Wi i
  let φi i : Γ(X, Wi i) := TopCat.Presheaf.restrictOpen φ (Wi i) (hle i)
  have hDi i : X.basicOpen (φi i) ≤ X.basicOpen φ := by
    rw [Scheme.basicOpen_restrictOpen]
    exact inf_le_right
  have h1 i : ∃ (k : ℕ) (t : Γ(F, Wi i)),
      TopCat.Presheaf.restrictOpen t (X.basicOpen (φi i)) (X.basicOpen_le _) =
        TopCat.Presheaf.restrictOpen φ (X.basicOpen (φi i)) ((X.basicOpen_le _).trans (hle i)) ^
          k • TopCat.Presheaf.restrictOpen s _ (hDi i) := by
    obtain ⟨k, t, ht⟩ := (hWi i).exists_restrictOpen_eq_pow_smul F (φi i)
      (TopCat.Presheaf.restrictOpen s _ (hDi i))
    exact ⟨k, t, ht.trans (by rw [ores_res])⟩
  choose k t ht using h1
  obtain ⟨K, hK⟩ := (Set.finite_range k).bddAbove
  let u i : Γ(F, Wi i) := φi i ^ (K - k i) • t i
  have hu i V (hV : V ≤ X.basicOpen (φi i)) :
      TopCat.Presheaf.restrictOpen (u i) V (hV.trans (X.basicOpen_le _)) =
        TopCat.Presheaf.restrictOpen φ V (hV.trans ((X.basicOpen_le _).trans (hle i))) ^ K •
          TopCat.Presheaf.restrictOpen s V (hV.trans (hDi i)) := by
    rw [← mres_res F (X.basicOpen_le _) hV, mres_pow_smul, ht]
    dsimp only [φi]
    rw [ores_res, smul_smul, ← pow_add, Nat.sub_add_cancel (hK ⟨i, rfl⟩), mres_pow_smul, ores_res,
      mres_res]
  have h2 (p : ι × ι) : ∃ m : ℕ,
      TopCat.Presheaf.restrictOpen φ (Wi p.1 ⊓ Wi p.2) (inf_le_left.trans (hle _)) ^ m •
        ((u p.1 |ₒ (Wi p.1 ⊓ Wi p.2)) - (u p.2 |ₒ (Wi p.1 ⊓ Wi p.2))) = 0 := by
    refine (hWij p.1 p.2).exists_pow_smul_eq_zero F _ _ ?_
    have hB1 := Scheme.basicOpen_restrictOpen_mono (inf_le_left : Wi p.1 ⊓ Wi p.2 ≤ _)
      (hle p.1) φ
    have hB2 := Scheme.basicOpen_restrictOpen_mono (inf_le_right : Wi p.1 ⊓ Wi p.2 ≤ _)
      (hle p.2) φ
    rw [mres_sub, mres_res, mres_res, hu p.1 _ hB1, hu p.2 _ hB2, sub_self]
  choose m hm using h2
  obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
  let v i : Γ(F, Wi i) := φi i ^ M • u i
  obtain ⟨w, hw, -⟩ := mres_existsUnique_gluing F Wi hW.ge hle v fun a b ↦ by
    rw [← sub_eq_zero]
    simp only [v, mres_pow_smul, φi, ores_res]
    rw [← smul_sub]
    exact pow_smul_eq_zero_of_le' (hM ⟨(a, b), rfl⟩) (hm (a, b))
  have hcov : X.basicOpen φ ≤ ⨆ i, X.basicOpen (φi i) := by
    intro x hx
    have hxW : x ∈ W := X.basicOpen_le φ hx
    rw [← hW] at hxW
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hxW
    refine Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [Scheme.basicOpen_restrictOpen]
    exact ⟨hi, hx⟩
  refine ⟨M + K, w, mres_eq_of_locally_eq F _ hcov hDi _ _ fun i ↦ ?_⟩
  rw [mres_res, ← mres_res F (hle i) (X.basicOpen_le _), hw, mres_pow_smul, hu i _ le_rfl]
  dsimp only [φi]
  rw [ores_res, smul_smul, ← pow_add, mres_pow_smul, ores_res]

end Cover

namespace IsAffineOpen

variable {U : X.Opens} (hU : IsAffineOpen U) (F : X.Modules)

set_option backward.isDefEq.respectTransparency false in
/-- **A localizing criterion.** Let `U` be an affine open and `F` an `𝒪_X`-module such that for
every `f ∈ Γ(X, U)`, sections over `D(f)` extend to `U` after multiplication by a power of `f`,
and sections over `U` vanishing on `D(f)` are killed by a power of `f`. Then the restriction of
`F` to `Spec Γ(X, U)` is localizing. -/
theorem isLocalizing_restrict_fromSpec
    (hex : ∀ (f : Γ(X, U)) (s : Γ(F, X.basicOpen f)), ∃ (k : ℕ) (t : Γ(F, U)),
      TopCat.Presheaf.restrictOpen t (X.basicOpen f) (X.basicOpen_le f) =
        TopCat.Presheaf.restrictOpen f (X.basicOpen f) (X.basicOpen_le f) ^ k • s)
    (hzero : ∀ (f : Γ(X, U)) (t : Γ(F, U)),
      TopCat.Presheaf.restrictOpen t (X.basicOpen f) (X.basicOpen_le f) = 0 →
        ∃ k : ℕ, f ^ k • t = 0) :
    IsLocalizing (modulesSpecToSheaf.obj (F.restrict hU.fromSpec)) := by
  intro f
  have hW := hU.fromSpec_image_basicOpen f
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl) (fun x ↦ ?_) (fun x hx ↦ ?_)
  · let x' : Γ(F, hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f) := x
    obtain ⟨k, t, ht⟩ := hex f (TopCat.Presheaf.restrictOpen x' _ hW.ge)
    refine ⟨k, (show Γ(F, hU.fromSpec ''ᵁ ⊤) from
      TopCat.Presheaf.restrictOpen t _ (hU.fromSpec_image_le ⊤)), ?_⟩
    refine (smul_restrict_fromSpec hU F _ _ x).trans ?_
    change TopCat.Presheaf.restrictOpen (f ^ k) (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
        (hU.fromSpec_image_le _) • x' =
      TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen t (hU.fromSpec ''ᵁ ⊤)
        (hU.fromSpec_image_le ⊤)) (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
        (hU.fromSpec.image_mono le_top)
    apply mres_injective_of_le F hW.ge hW.le
    dsimp only
    rw [mres_smul, ores_res, ores_pow, ← ht, mres_res, mres_res]
  · let x' : Γ(F, hU.fromSpec ''ᵁ ⊤) := x
    have hx' : TopCat.Presheaf.restrictOpen x' (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
        (hU.fromSpec.image_mono le_top) = 0 := hx
    obtain ⟨k, hk⟩ := hzero f (TopCat.Presheaf.restrictOpen x' U hU.le_fromSpec_image_top) (by
      rw [mres_res, ← mres_res F (hU.fromSpec.image_mono le_top) hW.ge, hx', mres_zero])
    refine ⟨k, (smul_restrict_fromSpec hU F _ _ x).trans ?_⟩
    change TopCat.Presheaf.restrictOpen (f ^ k) (hU.fromSpec ''ᵁ ⊤) (hU.fromSpec_image_le _) •
      x' = 0
    apply mres_injective_of_le F hU.le_fromSpec_image_top (hU.fromSpec_image_le ⊤)
    dsimp only
    rw [mres_smul, ores_res, ores_self, mres_zero]
    exact hk

end IsAffineOpen

namespace Scheme.Modules

/-- A presentation of `M.over U` from a presentation of the restriction `M.restrict U.ι`. -/
noncomputable def presentationOver (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation :=
  SheafOfModules.Presentation.ofIsIso
    ((overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm).hom
    (P.map (overEquiv U).inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm)

/-- An `𝒪_X`-module whose restrictions to the members of an open cover admit presentations is
quasi-coherent. -/
theorem isQuasicoherent_of_presentation_restrict (M : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (P : ∀ i, (M.restrict (U i).ι).Presentation) :
    M.IsQuasicoherent :=
  SheafOfModules.QuasicoherentData.isQuasicoherent (M := M)
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff (U := U) _).2 hU
      presentation i := presentationOver M (U i) (P i) }

/-- The presentation of an `𝒪_{Spec R}`-module `N` with `Γ(N)^~ ≅ N` induced by the tautological
presentation of `Γ(N)`. -/
noncomputable def presentationOfIsIsoFromTildeΓ {R : CommRingCat.{u}} (N : (Spec R).Modules)
    [IsIso N.fromTildeΓ] : N.Presentation :=
  SheafOfModules.Presentation.ofIsIso.{u, u, u} (asIso N.fromTildeΓ).hom
    (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _))

/-- A presentation of `M|_U` for an affine open `U` from a presentation of the restriction of `M`
along `U.fromSpec`. -/
noncomputable def presentationRestrictOfFromSpec (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (P : (M.restrict hU.fromSpec).Presentation) :
    (M.restrict U.ι).Presentation :=
  SheafOfModules.Presentation.ofIsIso.{u, u, u}
    (((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M).symm ≪≫
      (restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M).hom
    (presentationRestrict hU.isoSpec.hom P)

section Pushforward

variable {Y' Y : Scheme.{u}} (π : Y' ⟶ Y) (G : Y'.Modules)

/-- The action of `Γ(Y, W)` on the sections of `π_* G` over `W` is the action through `π.app W`
on the sections of `G` over `π ⁻¹ᵁ W`. -/
lemma pushforward_smul_eq {W : Y.Opens} (r : Γ(Y, W))
    (x : Γ((Scheme.Modules.pushforward π).obj G, W)) :
    r • x = (show Γ(G, π ⁻¹ᵁ W) from π.app W r • (show Γ(G, π ⁻¹ᵁ W) from x)) :=
  rfl

/-- Restriction of sections of `π_* G` is restriction of sections of `G` to the preimages. -/
lemma pushforward_restrictOpen_eq {W W' : Y.Opens} (h : W' ≤ W)
    (x : Γ((Scheme.Modules.pushforward π).obj G, W)) :
    TopCat.Presheaf.restrictOpen x W' h = (show Γ(G, π ⁻¹ᵁ W') from
      TopCat.Presheaf.restrictOpen (show Γ(G, π ⁻¹ᵁ W) from x) (π ⁻¹ᵁ W')
        (π.preimage_mono h)) :=
  rfl

private lemma app_restrictOpen' {W W' : Y.Opens} (h : W' ≤ W) (r : Γ(Y, W)) :
    π.app W' (TopCat.Presheaf.restrictOpen r W' h) =
      TopCat.Presheaf.restrictOpen (π.app W r) (π ⁻¹ᵁ W') (π.preimage_mono h) := by
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

variable [G.IsQuasicoherent] {V : Y.Opens} {ι : Type*} [Finite ι] (Wi : ι → Y'.Opens)
  (hW : ⨆ i, Wi i = π ⁻¹ᵁ V) (hWi : ∀ i, IsAffineOpen (Wi i))

include hW hWi in
/-- If `π ⁻¹ᵁ V` is a finite union of affine opens with affine pairwise intersections, sections
of `π_* G` over `D(f) ⊆ V` extend to `V` after multiplication by a power of `f`. -/
theorem exists_restrictOpen_eq_pow_smul_pushforward
    (hWij : ∀ i j, IsAffineOpen (Wi i ⊓ Wi j))
    (f : Γ(Y, V)) (s : Γ((Scheme.Modules.pushforward π).obj G, Y.basicOpen f)) :
    ∃ (k : ℕ) (t : Γ((Scheme.Modules.pushforward π).obj G, V)),
      TopCat.Presheaf.restrictOpen t (Y.basicOpen f) (Y.basicOpen_le f) =
        TopCat.Presheaf.restrictOpen f (Y.basicOpen f) (Y.basicOpen_le f) ^ k • s := by
  have hB : π ⁻¹ᵁ Y.basicOpen f = Y'.basicOpen (π.app V f) := Scheme.preimage_basicOpen π f
  let s' : Γ(G, π ⁻¹ᵁ Y.basicOpen f) := s
  obtain ⟨k, t, ht⟩ := exists_restrictOpen_eq_pow_smul_of_cover G Wi hW hWi hWij (π.app V f)
    (TopCat.Presheaf.restrictOpen s' _ hB.ge)
  refine ⟨k, t, ?_⟩
  rw [pushforward_restrictOpen_eq, pushforward_smul_eq, map_pow, app_restrictOpen']
  apply mres_injective_of_le G hB.ge hB.le
  dsimp only
  rw [mres_res, ht, mres_smul, ores_pow, ores_res]

include hW hWi in
/-- If `π ⁻¹ᵁ V` is a finite union of affine opens, a section of `π_* G` over `V` vanishing on
`D(f)` is killed by a power of `f`. -/
theorem exists_pow_smul_eq_zero_pushforward (f : Γ(Y, V))
    (t : Γ((Scheme.Modules.pushforward π).obj G, V))
    (ht : TopCat.Presheaf.restrictOpen t (Y.basicOpen f) (Y.basicOpen_le f) = 0) :
    ∃ k : ℕ, f ^ k • t = 0 := by
  have hB : π ⁻¹ᵁ Y.basicOpen f = Y'.basicOpen (π.app V f) := Scheme.preimage_basicOpen π f
  let t' : Γ(G, π ⁻¹ᵁ V) := t
  have ht' : TopCat.Presheaf.restrictOpen t' (π ⁻¹ᵁ Y.basicOpen f)
      (π.preimage_mono (Y.basicOpen_le f)) = 0 := ht
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_cover G Wi hW hWi (π.app V f) t' (by
    rw [← mres_res G (π.preimage_mono (Y.basicOpen_le f)) hB.ge, ht', mres_zero])
  refine ⟨k, ?_⟩
  rw [pushforward_smul_eq, map_pow]
  exact hk

/-- **Quasi-coherence of pushforwards.** Let `π : Y' ⟶ Y` be such that the preimage of every
affine open of `Y` is a finite union of affine opens with affine pairwise intersections. Then the
pushforward of a quasi-coherent `𝒪_{Y'}`-module along `π` is quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_cover
    (h : ∀ V : Y.Opens, IsAffineOpen V → ∃ (ι : Type u) (_ : Finite ι) (Wi : ι → Y'.Opens),
      ⨆ i, Wi i = π ⁻¹ᵁ V ∧ (∀ i, IsAffineOpen (Wi i)) ∧ ∀ i j, IsAffineOpen (Wi i ⊓ Wi j)) :
    ((Scheme.Modules.pushforward π).obj G).IsQuasicoherent := by
  choose ι hι Wi hW hWi hWij using h
  refine isQuasicoherent_of_presentation_restrict _ (fun V : Y.affineOpens ↦ (V : Y.Opens))
    (iSup_affineOpens_eq_top Y) fun V ↦ ?_
  have hloc := V.2.isLocalizing_restrict_fromSpec _
    (exists_restrictOpen_eq_pow_smul_pushforward π G _ (hW V V.2) (hWi V V.2) (hWij V V.2))
    (exists_pow_smul_eq_zero_pushforward π G _ (hW V V.2) (hWi V V.2))
  haveI := (isIso_fromTildeΓ_iff_isLocalizing _).2 hloc
  exact presentationRestrictOfFromSpec _ V.2 (presentationOfIsIsoFromTildeΓ _)

end Pushforward

end Scheme.Modules

end AlgebraicGeometry

end
