/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.Tilde
public import Other.Oka.RingTheory.Localization.CechRadical
public import Other.Oka.Topology.Sheaves.Cohomology.Leray

/-!
# Serre's vanishing theorem for quasi-coherent sheaves on affine schemes

For a commutative ring `R` and a quasi-coherent `𝒪_{Spec R}`-module `M` (e.g. `M = N~` for an
`R`-module `N`), the underlying abelian sheaf of `M` has `Hⁿ(Spec R, M) = 0` for `n ≥ 1`. More
generally, for a scheme `X`, an affine open `U ⊆ X` and a quasi-coherent `𝒪_X`-module `F`,
`Hⁿ(U, F|_U) = 0` for `n ≥ 1`.

The proof is Cartan's criterion (`TopCat.Sheaf.cartan_of_isCompact`) for the basis of basic open
subsets: the sections of `M` over `D(f)` are the localisation `Γ(M)_f`, so the Čech complex of `M`
for a finite cover of `D(g)` by basic opens `D(f i)` is the algebraic Čech complex
`LocalizedModule.cechObj Γ(M) f`, which is exact by `LocalizedModule.cechD_exact_of_mem_radical`.

To treat `Spec R` and affine opens of schemes at once, the argument is carried out for an
abstract space `Y` with a homeomorphism `h : Spec A ≃ₜ Y` and an abelian sheaf `G` on `Y` whose
sections over the images `D a` of the basic opens are identified, compatibly with restriction, with
the localisations `N_a` of an `A`-module `N` (`TopCat.Sheaf.H_eq_zero_of_localizing`).

## Main results

* `TopCat.Sheaf.H_eq_zero_of_localizing`, `TopCat.Sheaf.H_restrictOpen_eq_zero_of_localizing`:
  the abstract version.
* `AlgebraicGeometry.Scheme.Modules.H_eq_zero_of_isQuasicoherent`: `Hⁿ(Spec R, M) = 0` for
  `n ≥ 1` and quasi-coherent `M`; `AlgebraicGeometry.H_tilde_eq_zero` for `M = N~`;
  `AlgebraicGeometry.Scheme.Modules.H_restrictOpen_basicOpen_eq_zero` on basic opens.
* `AlgebraicGeometry.Scheme.Modules.H_restrictOpen_eq_zero_of_isAffineOpen`: `Hⁿ(U, F|_U) = 0`
  for `n ≥ 1`, an affine open `U` of a scheme `X` and quasi-coherent `F`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite PrimeSpectrum Submonoid

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- If `D(g) ⊆ ⋃ D(f i)`, then `g ∈ √(f i)`. -/
lemma mem_radical_of_basicOpen_subset {ι : Type*} (f : ι → A) (g : A)
    (h : (basicOpen g : Set (PrimeSpectrum A)) ⊆ ⋃ i, (basicOpen (f i) : Set _)) :
    g ∈ (Ideal.span (Set.range f)).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical, mem_vanishingIdeal]
  intro x hx
  by_contra hg
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (h hg)
  exact hi (hx (Ideal.subset_span ⟨i, rfl⟩))

end PrimeSpectrum

namespace TopCat.Sheaf

section Abstract

variable {Y : TopCat.{u}} {A : Type u} [CommRing A] (h : PrimeSpectrum A ≃ₜ Y)
  (D : A → Opens Y) (hD : ∀ a, (D a : Set Y) = h '' basicOpen a)

include hD

lemma localizing_le_iff (a b : A) : D a ≤ D b ↔ basicOpen a ≤ basicOpen b := by
  rw [← SetLike.coe_subset_coe, hD, hD, Set.image_subset_image_iff h.injective]
  rfl

lemma localizing_mul (a b : A) : D (a * b) = D a ⊓ D b := by
  apply SetLike.coe_injective
  rw [Opens.coe_inf, hD, hD, hD, ← Set.image_inter h.injective, basicOpen_mul]
  rfl

lemma localizing_one : D 1 = ⊤ := by
  apply SetLike.coe_injective
  rw [hD, basicOpen_one, Opens.coe_top, Opens.coe_top, Set.image_univ_of_surjective h.surjective]

lemma localizing_prod (n : ℕ) (g : Fin (n + 1) → A) : D (∏ a, g a) = ⨅ a, D (g a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, localizing_mul h D hD, ih, iInf_fin_succ]

lemma localizing_isBasis : Opens.IsBasis (Set.range D) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  let V' : Opens (PrimeSpectrum A) := ⟨h ⁻¹' V, V.2.preimage h.continuous⟩
  obtain ⟨W, ⟨a, rfl⟩, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.1 isBasis_basic_opens
    (show h.symm x ∈ V' by simpa [V'] using hx)
  refine ⟨D a, ⟨a, rfl⟩, ?_, ?_⟩
  · change x ∈ (D a : Set Y)
    rw [hD]
    exact ⟨h.symm x, hxW, by simp⟩
  · rw [← SetLike.coe_subset_coe, hD]
    rintro _ ⟨y, hy, rfl⟩
    exact hWV hy

lemma localizing_isCompact (a : A) : IsCompact (D a : Set Y) := by
  rw [hD]
  exact (isCompact_basicOpen a).image h.continuous

lemma localizing_dvd_of_le {a b : A} (hab : D b ≤ D a) : ∃ n, a ∣ b ^ n := by
  rw [localizing_le_iff h D hD, basicOpen_le_basicOpen_iff] at hab
  obtain ⟨n, hn⟩ := hab
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

lemma localizing_mem_radical {ι : Type*} (f : ι → A) (g : A) (hfg : ⨆ i, D (f i) = D g) :
    g ∈ (Ideal.span (Set.range f)).radical := by
  apply mem_radical_of_basicOpen_subset
  intro x hx
  have : h x ∈ ((⨆ i, D (f i) : Opens Y) : Set Y) := by
    rw [hfg, hD]
    exact ⟨x, hx, rfl⟩
  rw [Opens.coe_iSup] at this
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
  rw [hD] at hi
  obtain ⟨y, hy, hyx⟩ := hi
  exact Set.mem_iUnion.2 ⟨i, h.injective hyx ▸ hy⟩

variable (N : Type u) [AddCommGroup N] [Module A N] (G : AbSheaf Y)
  (ψ : ∀ a, LocalizedModule (powers a) N ≃+ G.obj.obj (op (D a)))
  (hψ : ∀ (a b : A) (hd : ∃ n, a ∣ b ^ n) (hab : D b ≤ D a) (x : LocalizedModule (powers a) N),
    G.obj.map (homOfLE hab).op (ψ a x) = ψ b (LocalizedModule.awayMap N hd x))

omit hD in
/-- Two composable restriction maps of a presheaf on `Opens Y` compose to the restriction. -/
lemma map_map_apply (P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) {U V W : Opens Y} (i : U ⟶ V)
    (j : V ⟶ W) (k : U ⟶ W) (x : P.obj (op W)) : P.map i.op (P.map j.op x) = P.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

include hψ in
/-- The Čech complex of `G` for a finite cover of `D g` by sets `D (f i)` is exact in positive
degrees. -/
lemma isCechAcyclic_of_localizing {ι : Type u} [Finite ι] (f : ι → A) (g : A)
    (hfg : ⨆ i, D (f i) = D g) : Presheaf.IsCechAcyclic (fun i ↦ D (f i)) G.obj := by
  let U : ι → Opens Y := fun i ↦ D (f i)
  have hprod {n : ℕ} (σ : Fin (n + 1) → ι) : Presheaf.cechOpen U σ = D (∏ a, f (σ a)) :=
    (localizing_prod h D hD n (fun a ↦ f (σ a))).symm
  let e {n : ℕ} (σ : Fin (n + 1) → ι) :
      LocalizedModule (powers (∏ a, f (σ a))) N ≃+ G.obj.obj (op (Presheaf.cechOpen U σ)) :=
    (ψ _).trans (G.obj.mapIso (eqToIso (hprod σ)).op).addCommGroupIsoToAddEquiv
  have he {n : ℕ} (σ : Fin (n + 1) → ι) (y) :
      e σ y = G.obj.map (homOfLE (hprod σ).le).op (ψ _ y) := rfl
  let E (n : ℕ) (x : LocalizedModule.cechObj N f n) : Presheaf.CechCochain U G.obj n :=
    fun σ ↦ e σ (x σ)
  have hE (n : ℕ) (x : LocalizedModule.cechObj N f n) :
      Presheaf.cechD U G.obj n (E n x) = E (n + 1) (LocalizedModule.cechD N f n x) := by
    funext τ
    simp only [E, Presheaf.cechD_apply, LocalizedModule.cechD_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    have hle : D (∏ a, f (τ a)) ≤ D (∏ a, f (τ (j.succAbove a))) := by
      rw [← hprod, ← hprod]
      exact Presheaf.cechOpen_le_comp U τ j.succAbove
    rw [he, he, ← hψ _ _ _ hle]
    exact (map_map_apply _ _ _ (homOfLE ((hprod τ).le.trans hle)) _).trans
      (map_map_apply _ _ _ _ _).symm
  have hEinj (n : ℕ) : Function.Injective (E n) := fun x y hxy ↦
    funext fun σ ↦ (e σ).injective (congrFun hxy σ)
  have hEsurj (n : ℕ) (c : Presheaf.CechCochain U G.obj n) :
      E n (fun σ ↦ (e σ).symm (c σ)) = c :=
    funext fun σ ↦ (e σ).apply_symm_apply (c σ)
  have hE0 (n : ℕ) : E n 0 = 0 := funext fun σ ↦ map_zero (e σ)
  have hex (n : ℕ) : Function.Exact (LocalizedModule.cechD N f n)
      (LocalizedModule.cechD N f (n + 1)) := by
    refine LocalizedModule.cechD_exact_of_mem_radical N f
      (localizing_mem_radical h D hD f g hfg) (fun i ↦ localizing_dvd_of_le h D hD ?_) n
    rw [← hfg]
    exact le_iSup (fun i ↦ D (f i)) i
  rw [Presheaf.isCechAcyclic_iff]
  intro n c hc
  rw [← hEsurj (n + 1) c, hE, ← hE0] at hc
  obtain ⟨y, hy⟩ := ((hex n) _).1 (hEinj _ hc)
  exact ⟨E n y, by rw [hE, hy, hEsurj]⟩

include hψ in
lemma isCechAcyclic_of_localizing' (ι : Type u) (U : ι → Opens Y) [Finite ι]
    (hU : ∀ i, U i ∈ Set.range D) (hsup : ⨆ i, U i ∈ Set.range D) :
    Presheaf.IsCechAcyclic U G.obj := by
  choose f hf using hU
  obtain ⟨g, hg⟩ := hsup
  obtain rfl : U = fun i ↦ D (f i) := funext fun i ↦ (hf i).symm
  exact isCechAcyclic_of_localizing h D hD N G ψ hψ f g hg.symm

/-- The sets `D a` are closed under binary intersections. -/
lemma inf_mem_range {a b : Opens Y} (ha : a ∈ Set.range D) (hb : b ∈ Set.range D) :
    a ⊓ b ∈ Set.range D := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨a * b, localizing_mul h D hD a b⟩

include hψ in
/-- **Serre's vanishing theorem, abstract form.** Let `h : Spec A ≃ₜ Y`, `D a = h(D(a))`, and
let `G` be an abelian sheaf on `Y` whose sections over `D a` are identified with the localisation
`N_a` of an `A`-module `N`, compatibly with restrictions. Then `Hⁿ(B, G|_B) = 0` for `n ≥ 1` and
every `B` of the form `D a`. -/
theorem H_restrictOpen_eq_zero_of_localizing (B : Opens Y) (hB : B ∈ Set.range D) (q : ℕ)
    (x : H ((restrictOpen B).obj G) (q + 1)) : x = 0 :=
  cartan_of_isCompact (Set.range D) (fun _ ha _ hb ↦ inf_mem_range h D hD ha hb)
    (localizing_isBasis h D hD) (by rintro _ ⟨a, rfl⟩; exact localizing_isCompact h D hD a) G
    (fun ι U _ hU hsup ↦ isCechAcyclic_of_localizing' h D hD N G ψ hψ ι U hU hsup) B hB q x

include hψ in
/-- **Serre's vanishing theorem, abstract form.** Under the hypotheses of
`TopCat.Sheaf.H_restrictOpen_eq_zero_of_localizing`, `Hⁿ(Y, G) = 0` for `n ≥ 1`. -/
theorem H_eq_zero_of_localizing (q : ℕ) (x : H G (q + 1)) : x = 0 := by
  let U : PUnit.{u + 1} → Opens Y := fun _ ↦ D 1
  have hU : ∀ i, U i ∈ Set.range D := fun _ ↦ ⟨1, rfl⟩
  exact H_eq_zero_of_isCechAcyclic U (by simp [U, localizing_one h D hD]) G
    (fun n σ q' y ↦ H_restrictOpen_eq_zero_of_localizing h D hD N G ψ hψ _
      (cechOpen_mem (fun _ ha _ hb ↦ inf_mem_range h D hD ha hb) hU σ) q' y)
    (isCechAcyclic_of_localizing' h D hD N G ψ hψ _ U hU ⟨1, by simp [U]⟩) q x

end Abstract

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

open TopCat.Sheaf

section Spec

variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]

/-- For a quasi-coherent `M` on `Spec R`, the sections `Γ(M, D(a))` are the localisation of the
global sections `Γ(M)` at `a`. -/
noncomputable def basicOpenLocalizationEquiv (a : R) :
    LocalizedModule (powers a) ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ≃+
      Γ(M, PrimeSpectrum.basicOpen a) :=
  haveI := isLocalizedModule_away_sectionsToBasicOpen M a
  (IsLocalizedModule.iso (powers a) (sectionsToBasicOpen M a).hom).toAddEquiv

/-- The identifications `Γ(M, D(a)) ≅ Γ(M)_a` are compatible with restriction. -/
lemma map_basicOpenLocalizationEquiv (a b : R) (hd : ∃ n, a ∣ b ^ n)
    (hab : PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a)
    (x : LocalizedModule (powers a) ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤))) :
    M.presheaf.map (homOfLE hab).op (basicOpenLocalizationEquiv M a x) =
      basicOpenLocalizationEquiv M b (LocalizedModule.awayMap _ hd x) := by
  haveI := isLocalizedModule_away_sectionsToBasicOpen M a
  haveI := isLocalizedModule_away_sectionsToBasicOpen M b
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)
  have key : ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hab).op).hom ∘ₗ
      (IsLocalizedModule.iso (powers a) (sectionsToBasicOpen M a).hom).toLinearMap =
      (IsLocalizedModule.iso (powers b) (sectionsToBasicOpen M b).hom).toLinearMap ∘ₗ
        LocalizedModule.awayMap N hd := by
    refine IsLocalizedModule.ext (powers a) (LocalizedModule.mkLinearMap (powers a) N)
      (fun s ↦ ?_) ?_
    · obtain ⟨_, k, rfl⟩ := s
      simp only [map_pow]
      exact (isUnit_algebraMap_end_of_le_basicOpen a hab).pow k
    · have e2 : sectionsToBasicOpen M a ≫ (modulesSpecToSheaf.obj M).presheaf.map (homOfLE hab).op =
          sectionsToBasicOpen M b := by
        rw [← Functor.map_comp]
        rfl
      ext m
      have h1 : IsLocalizedModule.iso (powers a) (sectionsToBasicOpen M a).hom
          (LocalizedModule.mk m 1) = (sectionsToBasicOpen M a).hom m :=
        IsLocalizedModule.iso_mk_one _ _ m
      have h2 : IsLocalizedModule.iso (powers b) (sectionsToBasicOpen M b).hom
          (LocalizedModule.mk m 1) = (sectionsToBasicOpen M b).hom m :=
        IsLocalizedModule.iso_mk_one _ _ m
      change ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hab).op).hom
          (IsLocalizedModule.iso (powers a) (sectionsToBasicOpen M a).hom
            (LocalizedModule.mk m 1)) =
        IsLocalizedModule.iso (powers b) (sectionsToBasicOpen M b).hom
          (LocalizedModule.awayMap N hd (LocalizedModule.mk m 1))
      rw [h1, LocalizedModule.awayMap_mk_one, h2, ← e2]
      rfl
  exact LinearMap.congr_fun key x

/-- **Serre's vanishing theorem.** For a quasi-coherent module `M` on `Spec R`, the cohomology
of the underlying abelian sheaf vanishes in positive degrees: `Hⁿ(Spec R, M) = 0` for `n ≥ 1`. -/
theorem H_eq_zero_of_isQuasicoherent (q : ℕ)
    (x : H ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) (q + 1)) : x = 0 :=
  H_eq_zero_of_localizing (Homeomorph.refl _)
    (fun a ↦ (PrimeSpectrum.basicOpen a : (Spec R).Opens)) (fun _ ↦ (Set.image_id _).symm) _ _
    (basicOpenLocalizationEquiv M)
    (fun a b hd hab x ↦ map_basicOpenLocalizationEquiv M a b hd hab x) q x

/-- **Serre's vanishing theorem on basic opens.** For a quasi-coherent module `M` on `Spec R`,
`Hⁿ(D(a), M|_{D(a)}) = 0` for `n ≥ 1`. -/
theorem H_restrictOpen_basicOpen_eq_zero (a : R) (q : ℕ)
    (x : H ((restrictOpen (PrimeSpectrum.basicOpen a : (Spec R).Opens)).obj
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M)) (q + 1)) : x = 0 :=
  H_restrictOpen_eq_zero_of_localizing (Homeomorph.refl _)
    (fun a ↦ (PrimeSpectrum.basicOpen a : (Spec R).Opens))
    (fun _ ↦ (Set.image_id _).symm) _ ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M)
    (basicOpenLocalizationEquiv M)
    (fun a b hd hab x ↦ map_basicOpenLocalizationEquiv M a b hd hab x)
    (PrimeSpectrum.basicOpen a : (Spec R).Opens) ⟨a, rfl⟩ q x

instance (q : ℕ) :
    Subsingleton (H ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) (q + 1)) :=
  ⟨fun x y ↦ (H_eq_zero_of_isQuasicoherent M q x).trans (H_eq_zero_of_isQuasicoherent M q y).symm⟩

end Spec

section IsAffineOpen

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)

/-- An affine open `U` is homeomorphic to `Spec Γ(X, U)`, via `IsAffineOpen.fromSpec`. -/
noncomputable def _root_.AlgebraicGeometry.IsAffineOpen.primeSpectrumHomeomorph :
    PrimeSpectrum Γ(X, U) ≃ₜ (TopologicalSpace.Opens.toTopCat X).obj U :=
  hU.fromSpec.isOpenEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hU.range_fromSpec)

/-- The open of `U` corresponding to the basic open `D(a) ⊆ Spec Γ(X, U)`. -/
def basicOpenInAffine (a : Γ(X, U)) :
    TopologicalSpace.Opens ((TopologicalSpace.Opens.toTopCat X).obj U) :=
  ⟨hU.primeSpectrumHomeomorph '' PrimeSpectrum.basicOpen a,
    hU.primeSpectrumHomeomorph.isOpenMap _ (PrimeSpectrum.basicOpen a).2⟩

lemma functor_obj_basicOpenInAffine (a : Γ(X, U)) :
    U.isOpenEmbedding.isOpenMap.functor.obj (basicOpenInAffine hU a) =
      hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen a := by
  apply SetLike.coe_injective
  change Subtype.val '' (hU.primeSpectrumHomeomorph '' _) = hU.fromSpec '' _
  rw [Set.image_image]
  rfl

/-- The identification of the sections of `F|_U` over `basicOpenInAffine hU a` with the
localisation at `a` of the global sections of `F` pulled back to `Spec Γ(X, U)`. -/
noncomputable def basicOpenInAffineEquiv (a : Γ(X, U)) :
    LocalizedModule (powers a)
      ((modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).presheaf.obj (op ⊤)) ≃+
      ((restrictOpen U).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)).obj.obj
        (op (basicOpenInAffine hU a)) :=
  (basicOpenLocalizationEquiv (F.restrict hU.fromSpec) a).trans
    (F.presheaf.mapIso (eqToIso (functor_obj_basicOpenInAffine hU a)).op).addCommGroupIsoToAddEquiv

include hU in
/-- **Serre's vanishing theorem for affine opens.** For a quasi-coherent module `F` on a scheme
`X` and an affine open `U ⊆ X`, `Hⁿ(U, F|_U) = 0` for `n ≥ 1`, where `F|_U` is the restriction of
the underlying abelian sheaf of `F`. -/
theorem H_restrictOpen_eq_zero_of_isAffineOpen (q : ℕ)
    (x : H ((restrictOpen U).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)) (q + 1)) :
    x = 0 := by
  refine H_eq_zero_of_localizing hU.primeSpectrumHomeomorph (basicOpenInAffine hU)
    (fun _ ↦ rfl) _ _ (basicOpenInAffineEquiv F hU) (fun a b hd hab y ↦ ?_) q x
  have hab' : PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a :=
    (localizing_le_iff hU.primeSpectrumHomeomorph (basicOpenInAffine hU) (fun _ ↦ rfl) b a).1 hab
  have h := map_basicOpenLocalizationEquiv (F.restrict hU.fromSpec) a b hd hab' y
  have hk : U.isOpenEmbedding.isOpenMap.functor.obj (basicOpenInAffine hU b) ≤
      hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen a :=
    (functor_obj_basicOpenInAffine hU b).le.trans (Scheme.Hom.image_mono _ hab')
  calc _ = F.presheaf.map (homOfLE hk).op
        (basicOpenLocalizationEquiv (F.restrict hU.fromSpec) a y) := map_map_apply _ _ _ _ _
    _ = F.presheaf.map (eqToHom (functor_obj_basicOpenInAffine hU b)).op
        ((F.restrict hU.fromSpec).presheaf.map (homOfLE hab').op
          (basicOpenLocalizationEquiv (F.restrict hU.fromSpec) a y)) :=
      (map_map_apply _ _ _ _ _).symm
    _ = _ := congrArg _ h

include hU in
lemma subsingleton_H_restrictOpen_of_isAffineOpen (q : ℕ) :
    Subsingleton (H ((restrictOpen U).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F))
      (q + 1)) :=
  ⟨fun x y ↦ (H_restrictOpen_eq_zero_of_isAffineOpen F hU q x).trans
    (H_restrictOpen_eq_zero_of_isAffineOpen F hU q y).symm⟩

end IsAffineOpen

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- **Serre's vanishing theorem for `N~`.** For an `R`-module `N`, `Hⁿ(Spec R, N~) = 0` for
`n ≥ 1`. -/
theorem H_tilde_eq_zero {R : CommRingCat.{u}} (N : ModuleCat.{u} R) (q : ℕ)
    (x : TopCat.Sheaf.H ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde N)) (q + 1)) :
    x = 0 :=
  Scheme.Modules.H_eq_zero_of_isQuasicoherent (tilde N) q x

end AlgebraicGeometry

end
