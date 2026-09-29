/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.GraphClosure
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.FromGlobalSections

/-!
# Chow's lemma

Let `Y` be an irreducible scheme, proper over `Spec R`. Then there is a closed immersion
`c : Y' ⟶ Y ×_R ℙₒ(N; R)` from an irreducible scheme `Y'` such that the second projection
`Y' ⟶ ℙₒ(N; R)` is a closed immersion, the first projection `π : Y' ⟶ Y` is an isomorphism over a
nonempty open `U ⊆ Y`, and `π⁻¹ U` is scheme-theoretically dense in `Y'`
(`AlgebraicGeometry.exists_chow_of_irreducibleSpace`). If `Y` is integral, so is `Y'`
(`AlgebraicGeometry.exists_chow`).

## Construction

Cover `Y` by finitely many affine opens `V i` and choose `R`-algebra generators `a i g` of
`Γ(V i)`, and a dense open `U ⊆ ⋂ V i` (`AlgebraicGeometry.Chow.Data`). The coordinates of
`ℙₒ(N; R)` are indexed by the multi-indices `κ : ∀ i, Option (G i)`, and `g : U ⟶ ℙₒ(N; R)` is given
by `X_κ ↦ ∏ᵢ a i (κ i)` (with `a i none = 1`). Then `Y'` is the scheme-theoretic image of the
graph of `g` in `Y ×_R ℙₒ(N; R)`, in which `π⁻¹ U` is scheme-theoretically dense.

- `π` is an isomorphism over `U` since `ℙₒ(N; R)` is separated (`Chow.Data.isIso_π_restrict`).
- If `κ i = none`, the chart coordinates `X_{κ[i ↦ g]} / X_κ` restrict to `a i g` on `U`, so
  on `q⁻¹ D₊(X_κ)` the morphism `π` factors through `V i` and is determined by `q`; hence
  `q⁻¹ D₊(X_κ) ⟶ D₊(X_κ)` is a closed immersion (`Chow.Data.isClosedImmersion_q_restrict`).
- These charts cover the image of `q` (`Chow.Data.exists_chart`), and `q` has closed image since
  `Y` is proper, so `q` is a closed immersion (`Chow.Data.isClosedImmersion_q`).
-/

@[expose] public section

open CategoryTheory Limits HomogeneousLocalization MvPolynomial

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

open scoped ProjectiveSpace

variable {R : Type u} [CommRing R]

/-- The ring map `R → Γ(Z, ⊤)` induced by a morphism `Z ⟶ Spec R`. -/
noncomputable def Scheme.Hom.baseHom {Z : Scheme.{u}} (s : Z ⟶ Spec (.of R)) : R →+* Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop).hom

/-- A morphism `Z ⟶ Spec R` is `Z ⟶ Spec Γ(Z, ⊤) ⟶ Spec R`. -/
lemma Scheme.Hom.toSpecΓ_SpecMap_baseHom {Z : Scheme.{u}} (s : Z ⟶ Spec (.of R)) :
    Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s.baseHom) = s := by
  have h := Scheme.toSpecΓ_naturality s
  rw [← SpecMap_ΓSpecIso_hom] at h
  rw [baseHom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← h, Category.assoc,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- `baseHom` of a composite. -/
lemma Scheme.Hom.baseHom_comp {Z Z' : Scheme.{u}} (h : Z' ⟶ Z) (s : Z ⟶ Spec (.of R)) :
    (h ≫ s).baseHom = h.appTop.hom.comp s.baseHom := by
  simp only [baseHom, CommRingCat.hom_comp, Scheme.Hom.comp_appTop]
  rfl

/-- Global sections of `k ≫ Spec.map f` in terms of those of `k`. -/
lemma appTop_comp_SpecMap_ΓSpecIso_inv {Z : Scheme.{u}} {A B : CommRingCat.{u}}
    (k : Z ⟶ Spec B) (f : A ⟶ B) (x : A) :
    (k ≫ Spec.map f).appTop ((Scheme.ΓSpecIso A).inv x) =
      k.appTop ((Scheme.ΓSpecIso B).inv (f x)) := by
  have := congrArg (fun φ ↦ φ.hom x) (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [Scheme.Hom.comp_appTop]
  exact congrArg (fun z ↦ k.appTop z) this.symm

namespace Chow

open ProjectiveSpace

/-- Input data for Chow's lemma for `sY : Y ⟶ Spec R`: a finite cover of `Y` by affine opens
`V i`, generators `a i` of `Γ(V i)` as `R`-algebras, and a dense open `U` contained in every
`V i`. -/
structure Data {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of R)) where
  /-- The index type of the affine cover. -/
  I : Type u
  [fintype : Fintype I]
  [decEq : DecidableEq I]
  /-- The affine opens covering `Y`. -/
  V : I → Y.Opens
  isAffineOpen_V : ∀ i, IsAffineOpen (V i)
  iSup_V : ⨆ i, V i = ⊤
  /-- The index types of the generators. -/
  G : I → Type u
  [fintypeG : ∀ i, Fintype (G i)]
  /-- The generators of `Γ(V i)`. -/
  a : ∀ i, G i → Γ(V i, ⊤)
  surjective : ∀ i, Function.Surjective (eval₂Hom ((V i).ι ≫ sY).baseHom (a i))
  /-- A dense open contained in every `V i`. -/
  U : Y.Opens
  U_le : ∀ i, U ≤ V i
  dense_U : Dense (U : Set Y)
  quasiCompact_U : QuasiCompact U.ι

attribute [instance] Data.fintype Data.decEq Data.fintypeG Data.quasiCompact_U

variable {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of R)} (d : Data sY)

namespace Data

/-- The multi-indices: a choice of a generator or of `1` on every member of the cover. -/
abbrev K : Type u := ∀ i, Option (d.G i)

/-- The multi-index choosing `1` everywhere. -/
def bot : d.K := fun _ ↦ none

instance : Nonempty d.K := ⟨d.bot⟩

/-- The dimension of the ambient projective space. -/
noncomputable def N : ℕ := Fintype.card d.K - 1

/-- The multi-indices enumerate the coordinates of `ℙₒ(N; R)`. -/
noncomputable def e : d.K ≃ Fin (d.N + 1) :=
  (Fintype.equivFin d.K).trans (finCongr (by
    have : 0 < Fintype.card d.K := Fintype.card_pos
    unfold N; omega))

/-- The generator `v` of `Γ(V i)` restricted to `U`, with `none ↦ 1`. -/
noncomputable def A (i : d.I) : Option (d.G i) → Γ(d.U, ⊤)
  | none => 1
  | some g => (Y.homOfLE (d.U_le i)).appTop (d.a i g)

/-- The monomial `∏ᵢ A i (κ i)` on `U`. -/
noncomputable def mono (κ : d.K) : Γ(d.U, ⊤) := ∏ i, d.A i (κ i)

/-- Replacing the `i`-th entry of `κ` by `v` multiplies the monomial by `A i v / A i (κ i)`. -/
lemma mono_update (κ : d.K) (i : d.I) (v : Option (d.G i)) :
    d.mono (Function.update κ i v) * d.A i (κ i) = d.A i v * d.mono κ := by
  simp only [mono]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j ↦ d.A j (κ j)) (Finset.mem_univ i),
    Function.update_self, Finset.prod_congr rfl (fun j hj ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])]
  ring

/-- The monomial of `bot` is `1`. -/
lemma mono_bot : d.mono d.bot = 1 := by
  simp [mono, bot, A]

/-- The ring map `R[X_κ] → Γ(U)`, `X_κ ↦ ∏ᵢ A i (κ i)`. -/
noncomputable def φ : MvPolynomial (Fin (d.N + 1)) R →+* Γ(d.U, ⊤) :=
  eval₂Hom (d.U.ι ≫ sY).baseHom (fun j ↦ d.mono (d.e.symm j))

@[simp]
lemma φ_X (κ : d.K) : d.φ (X (d.e κ)) = d.mono κ := by
  simp [φ]

@[simp]
lemma φ_C (r : R) : d.φ (C r) = (d.U.ι ≫ sY).baseHom r := by
  simp [φ]

/-- The irrelevant ideal generates the unit ideal in `Γ(U)`, as `X_bot ↦ 1`. -/
lemma map_irrelevant :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (d.N + 1)) R)).toIdeal.map d.φ = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (x := X (d.e d.bot)) ?_)
    (by rw [φ_X, mono_bot]; exact isUnit_one)
  change X _ ∈ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (d.N + 1)) R)
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _ (X_mem_homogeneousSubmodule_one _) one_ne_zero]

/-- The morphism `U ⟶ ℙₒ(N; R)` given by the monomials `X_κ ↦ ∏ᵢ A i (κ i)`. -/
noncomputable def g : d.U.toScheme ⟶ ℙₒ(d.N; R) :=
  Proj.fromOfGlobalSections _ d.φ d.map_irrelevant

/-- `g` is a morphism over `Spec R`. -/
lemma g_toSpec : d.g ≫ ProjectiveSpace.toSpec d.N R = d.U.ι ≫ sY := by
  rw [ProjectiveSpace.toSpec, g, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← (d.U.ι ≫ sY).toSpecΓ_SpecMap_baseHom]
  congr 2
  ext r
  simp [← MvPolynomial.algebraMap_eq]

/-- The homogeneous coordinate ring of `ℙₒ(N; R)`. -/
local notation3 "𝒜" d => homogeneousSubmodule (Fin (Data.N d + 1)) R

/-- The graph `U ⟶ Y ×_R ℙₒ(N; R)` of `g`. -/
noncomputable abbrev Γ : d.U.toScheme ⟶ pullback sY (toSpec d.N R) :=
  graphMap sY (toSpec d.N R) d.U d.g d.g_toSpec

instance : QuasiCompact d.Γ := quasiCompact_graphMap ..

/-- The closure `Y'` of the graph of `g` in `Y ×_R ℙₒ(N; R)`. -/
noncomputable abbrev Y' : Scheme.{u} := d.Γ.image

/-- The closed immersion `Y' ⟶ Y ×_R ℙₒ(N; R)`. -/
noncomputable abbrev c : d.Y' ⟶ pullback sY (toSpec d.N R) := d.Γ.imageι

/-- The projection `Y' ⟶ Y`. -/
noncomputable abbrev π : d.Y' ⟶ Y := d.c ≫ pullback.fst _ _

/-- The projection `Y' ⟶ ℙₒ(N; R)`. -/
noncomputable abbrev q : d.Y' ⟶ ℙₒ(d.N; R) := d.c ≫ pullback.snd _ _

/-- The open immersion `U ⟶ Y'`. -/
noncomputable abbrev j : d.U.toScheme ⟶ d.Y' := d.Γ.toImage

@[reassoc]
lemma j_π : d.j ≫ d.π = d.U.ι := by simp

@[reassoc]
lemma j_q : d.j ≫ d.q = d.g := by simp

instance [IsReduced Y] : IsReduced d.Y' := isReduced_graphClosure ..

/-- `U` is scheme-theoretically dense in `Y'`. -/
instance : IsSchemeTheoreticallyDominant (d.π ⁻¹ᵁ d.U).ι :=
  inferInstanceAs (IsSchemeTheoreticallyDominant (graphClosureFst _ _ d.U d.g d.g_toSpec ⁻¹ᵁ d.U).ι)

/-- The standard open `D₊(X_κ)` of `ℙₒ(N; R)`. -/
noncomputable abbrev W (κ : d.K) : ℙₒ(d.N; R).Opens := Proj.basicOpen (𝒜 d) (X (d.e κ))

/-- The basic open `D(∏ᵢ A i (κ i)) = g⁻¹ D₊(X_κ)` of `U`. -/
noncomputable abbrev D (κ : d.K) : d.U.toScheme.Opens := d.U.toScheme.basicOpen (d.φ (X (d.e κ)))

/-- `g⁻¹ D₊(X_κ) = D(∏ᵢ A i (κ i))`. -/
lemma g_preimage (κ : d.K) : d.g ⁻¹ᵁ d.W κ = d.D κ :=
  Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (X_mem_homogeneousSubmodule_one _)

/-- `(q ∘ j)⁻¹ D₊(X_κ) = D(∏ᵢ A i (κ i))`. -/
lemma j_preimage_q_preimage (κ : d.K) : d.j ⁻¹ᵁ d.q ⁻¹ᵁ d.W κ = d.D κ := by
  rw [← Scheme.Hom.comp_preimage, j_q, g_preimage]

/-- On the part of the chart `D₊(X_κ)` of `Y'` meeting `U`, the chart map of `q` is
`g`'s chart map. -/
lemma restrict_j_q_basicOpenIsoSpec (κ : d.K) (V : d.Y'.Opens) (hV : V ≤ d.q ⁻¹ᵁ d.W κ) :
    d.j ∣_ V ≫ d.Y'.homOfLE hV ≫ d.q ∣_ d.W κ ≫
      (Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one (d.e κ)) one_pos).hom =
    d.U.toScheme.homOfLE (fun _ hx ↦ (d.j_preimage_q_preimage κ).le (hV hx)) ≫
      d.U.toScheme.basicOpenToSpecAway (d.φ (X (d.e κ))) ≫
        Spec.map (CommRingCat.ofHom (Proj.awayToLocalization _ d.φ (X (d.e κ)))) := by
  rw [← Proj.fromOfGlobalSections_resLE_basicOpenIsoSpec_hom _ d.φ d.map_irrelevant one_pos
    (X_mem_homogeneousSubmodule_one (d.e κ))]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (d.W κ).ι]
  rw [Category.assoc, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
    morphismRestrict_ι_assoc, j_q, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
  rfl

section chart

variable (i : d.I)

/-- The closed immersion `V i ⟶ 𝔸^{G i}_R` given by the generators `a i`. -/
noncomputable def ε : (d.V i).toScheme ⟶ Spec (.of (MvPolynomial (d.G i) R)) :=
  (d.V i).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (eval₂Hom ((d.V i).ι ≫ sY).baseHom (d.a i)))

instance : IsClosedImmersion (d.ε i) := by
  have : IsAffine (d.V i) := d.isAffineOpen_V i
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (eval₂Hom ((d.V i).ι ≫ sY).baseHom (d.a i)))) :=
    IsClosedImmersion.spec_of_surjective _ (d.surjective i)
  unfold ε
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance this

/-- `ε` is a morphism over `Spec R`. -/
lemma ε_SpecMap_C :
    d.ε i ≫ Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (d.G i) R)) =
      (d.V i).ι ≫ sY := by
  rw [← Scheme.Hom.toSpecΓ_SpecMap_baseHom ((d.V i).ι ≫ sY), ε, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext r
  exact eval₂_C _ _ _

/-- The generators `a i` restricted to `U`. -/
noncomputable def evalU : MvPolynomial (d.G i) R →+* Γ(d.U, ⊤) :=
  eval₂Hom (d.U.ι ≫ sY).baseHom (fun g ↦ d.A i (some g))

/-- The structure map of `U` factors through that of `V i`. -/
lemma baseHom_U : (d.U.ι ≫ sY).baseHom =
    (Y.homOfLE (d.U_le i)).appTop.hom.comp ((d.V i).ι ≫ sY).baseHom := by
  rw [← Scheme.Hom.baseHom_comp, Scheme.homOfLE_ι_assoc]

/-- `U ⟶ V i ⟶ 𝔸^{G i}_R` is given by the restricted generators. -/
lemma homOfLE_ε : Y.homOfLE (d.U_le i) ≫ d.ε i =
    d.U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (d.evalU i)) := by
  rw [ε, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply MvPolynomial.ringHom_ext
  · intro r
    change (Y.homOfLE (d.U_le i)).appTop (eval₂Hom ((d.V i).ι ≫ sY).baseHom (d.a i) (C r)) =
      d.evalU i (C r)
    rw [eval₂Hom_C, evalU, eval₂Hom_C, d.baseHom_U i]
    rfl
  · intro g
    change (Y.homOfLE (d.U_le i)).appTop (eval₂Hom ((d.V i).ι ≫ sY).baseHom (d.a i) (X g)) =
      d.evalU i (X g)
    rw [eval₂Hom_X', evalU, eval₂Hom_X']
    rfl

variable (κ : d.K)

/-- The ring map `R[x_g] → R[X]_(X_κ)`, `x_g ↦ X_{κ[i ↦ g]} / X_κ`. -/
noncomputable def ρ₀ : MvPolynomial (d.G i) R →+* Away (𝒜 d) (X (d.e κ)) :=
  eval₂Hom (awayXBase R (d.e κ))
    (fun g ↦ awayXDiv R (d.e κ) (d.e (Function.update κ i (some g))))

/-- The morphism `D₊(X_κ) ⟶ 𝔸^{G i}_R`, `x_g ↦ X_{κ[i ↦ g]} / X_κ`. -/
noncomputable def ρ : (d.W κ).toScheme ⟶ Spec (.of (MvPolynomial (d.G i) R)) :=
  (Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one (d.e κ)) one_pos).hom ≫
    Spec.map (CommRingCat.ofHom (d.ρ₀ i κ))

/-- `ρ` is a morphism over `Spec R`. -/
lemma ρ_SpecMap_C :
    d.ρ i κ ≫ Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial (d.G i) R)) =
      (d.W κ).ι ≫ toSpec d.N R := by
  have hC : (d.ρ₀ i κ).comp C = awayXBase R (d.e κ) := by
    ext r
    simp [ρ₀]
  rw [← Iso.hom_inv_id_assoc (Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one (d.e κ))
      one_pos) (d.W κ).ι, Proj.basicOpenIsoSpec_inv_ι, toSpec, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ρ,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  rw [← CommRingCat.ofHom_comp, hC]
  rfl

/-- If `κ i = none`, then on `D(∏ᵢ A i (κ i))` the ratio `X_{κ[i ↦ g]} / X_κ` is `a i g`. -/
lemma awayToLocalization_comp_ρ₀ (hκ : κ i = none) :
    (Proj.awayToLocalization (𝒜 d) d.φ (X (d.e κ))).comp (d.ρ₀ i κ) =
      (algebraMap _ (Localization.Away (d.φ (X (d.e κ))))).comp (d.evalU i) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    have h : ((fromZeroRingHom (𝒜 d) (Submonoid.powers (X (d.e κ)))) (algebraMap R _ r)).val =
        algebraMap (MvPolynomial (Fin (d.N + 1)) R) (Localization.Away (X (d.e κ))) (C r) := by
      rw [← Localization.mk_one_eq_algebraMap]
      rfl
    simp [ρ₀, evalU, awayXBase, Proj.awayToLocalization, h, IsLocalization.map_eq]
  · intro g
    simp only [RingHom.coe_comp, Function.comp_apply, ρ₀, eval₂Hom_X', awayXDiv,
      Proj.awayToLocalization_mk, evalU]
    rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]
    congr 1
    have := d.mono_update κ i (some g)
    simp only [hκ, A, mul_one] at this
    simp only [φ_X, pow_one, this]
    rfl

end chart

section closed

variable [IsSeparated sY] (i : d.I) (κ : d.K) (hκ : κ i = none)

omit [IsSeparated sY] in
include hκ in
/-- If `κ i = none`, then on `U` the map `ρ ∘ q` agrees with `ε`. -/
lemma restrict_j_q_ρ :
    d.j ∣_ (d.q ⁻¹ᵁ d.W κ) ≫ d.q ∣_ d.W κ ≫ d.ρ i κ =
      (d.j ⁻¹ᵁ d.q ⁻¹ᵁ d.W κ).ι ≫ Y.homOfLE (d.U_le i) ≫ d.ε i := by
  have h := d.restrict_j_q_basicOpenIsoSpec κ _ le_rfl
  rw [Scheme.homOfLE_rfl, Category.id_comp] at h
  rw [ρ, reassoc_of% h, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    d.awayToLocalization_comp_ρ₀ i κ hκ, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.basicOpenToSpecAway_SpecMap_assoc, Scheme.homOfLE_ι_assoc, homOfLE_ε]
  rfl

omit [IsSeparated sY] in
include hκ in
/-- If `κ i = none`, then `ρ ∘ q` factors through the closed immersion `ε`. -/
lemma ker_ε_le : (d.ε i).ker ≤ (d.q ∣_ d.W κ ≫ d.ρ i κ).ker :=
  calc (d.ε i).ker ≤ ((d.j ⁻¹ᵁ d.q ⁻¹ᵁ d.W κ).ι ≫ Y.homOfLE (d.U_le i) ≫ d.ε i).ker := by
        rw [← Category.assoc]; exact Scheme.Hom.le_ker_comp _ _
    _ = (d.q ∣_ d.W κ ≫ d.ρ i κ).ker := by
        rw [← d.restrict_j_q_ρ i κ hκ, Scheme.Hom.ker_comp, (d.j ∣_ _).ker_eq_bot,
          Scheme.IdealSheafData.map_bot]

/-- The morphism `q⁻¹ D₊(X_κ) ⟶ V i` which agrees with `π` (`h_ι`), for `κ i = none`. -/
noncomputable def h : (d.q ⁻¹ᵁ d.W κ).toScheme ⟶ (d.V i).toScheme :=
  IsClosedImmersion.lift (d.ε i) _ (d.ker_ε_le i κ hκ)

omit [IsSeparated sY] in
/-- `h` lifts `ρ ∘ q` along `ε`. -/
@[reassoc]
lemma h_ε : d.h i κ hκ ≫ d.ε i = d.q ∣_ d.W κ ≫ d.ρ i κ :=
  IsClosedImmersion.lift_fac ..

omit [IsSeparated sY] in
/-- On `U`, `h` is the inclusion `U ⟶ V i`. -/
lemma j_restrict_h : d.j ∣_ (d.q ⁻¹ᵁ d.W κ) ≫ d.h i κ hκ =
    (d.j ⁻¹ᵁ d.q ⁻¹ᵁ d.W κ).ι ≫ Y.homOfLE (d.U_le i) := by
  rw [← cancel_mono (d.ε i), Category.assoc, h_ε, restrict_j_q_ρ _ i κ hκ, Category.assoc]

/-- On `q⁻¹ D₊(X_κ)`, `π` factors through `h : q⁻¹ D₊(X_κ) ⟶ V i`. -/
lemma h_ι : d.h i κ hκ ≫ (d.V i).ι = (d.q ⁻¹ᵁ d.W κ).ι ≫ d.π := by
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated sY ?_ (d.j ∣_ (d.q ⁻¹ᵁ d.W κ)) ?_
  · rw [Category.assoc, ← ε_SpecMap_C, h_ε_assoc, Category.assoc, ρ_SpecMap_C,
      morphismRestrict_ι_assoc]
    simp [pullback.condition]
  · rw [reassoc_of% j_restrict_h, Scheme.homOfLE_ι, morphismRestrict_ι_assoc, j_π]

include hκ in
/-- **`q` is a closed immersion over the chart `D₊(X_κ)`** when `κ i = none`. -/
theorem isClosedImmersion_q_restrict : IsClosedImmersion (d.q ∣_ d.W κ) := by
  refine isClosedImmersion_morphismRestrict_of_graph d.c (d.W κ)
    (pullback.fst (d.ρ i κ) (d.ε i)) (pullback.snd _ _ ≫ (d.V i).ι) ?_
    (pullback.lift _ (d.h i κ hκ) (d.h_ε i κ hκ).symm) (pullback.lift_fst _ _ _) ?_
  · rw [Category.assoc, ← ε_SpecMap_C, ← pullback.condition_assoc, ρ_SpecMap_C]
  · rw [pullback.lift_snd_assoc, h_ι]

end closed

/-- On `π⁻¹ V i ∩ q⁻¹ D₊(X_λ)` with `λ i = g`, the coordinate `X_{λ[i ↦ none]}` does not vanish:
its ratio with `X_λ` is inverse to the generator `a i g`. -/
lemma mem_W_update (y : d.Y') (i : d.I) (l : d.K) (g : d.G i) (hl : l i = some g)
    (hy₁ : d.π y ∈ d.V i) (hy₂ : d.q y ∈ d.W l) :
    d.q y ∈ d.W (Function.update l i none) := by
  set l' := Function.update l i none
  let V : d.Y'.Opens := d.π ⁻¹ᵁ d.V i ⊓ d.q ⁻¹ᵁ d.W l
  have hV : V ≤ d.q ⁻¹ᵁ d.W l := inf_le_right
  let e := Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one (R := R) (d.e l)) one_pos
  let r : Away (𝒜 d) (X (d.e l)) := Away.isLocalizationElem
    (X_mem_homogeneousSubmodule_one (d.e l)) (X_mem_homogeneousSubmodule_one (d.e l'))
  let m : V.toScheme ⟶ Spec (.of (Away (𝒜 d) (X (d.e l)))) :=
    d.Y'.homOfLE hV ≫ d.q ∣_ d.W l ≫ e.hom
  let n : V.toScheme ⟶ Spec (.of (MvPolynomial (d.G i) R)) :=
    d.Y'.homOfLE inf_le_left ≫ d.π ∣_ d.V i ≫ d.ε i
  have hD : d.j ⁻¹ᵁ V ≤ d.D l := fun _ hx ↦ (d.j_preimage_q_preimage l).le (hV hx)
  let k := d.U.toScheme.homOfLE hD ≫ d.U.toScheme.basicOpenToSpecAway (d.φ (X (d.e l)))
  have hm : d.j ∣_ V ≫ m =
      k ≫ Spec.map (CommRingCat.ofHom (Proj.awayToLocalization (𝒜 d) d.φ (X (d.e l)))) := by
    simp only [m, k, Category.assoc]
    exact d.restrict_j_q_basicOpenIsoSpec l V hV
  have hn : d.j ∣_ V ≫ n = k ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap _ (Localization.Away (d.φ (X (d.e l))))).comp (d.evalU i))) := by
    have : d.j ∣_ V ≫ d.Y'.homOfLE inf_le_left ≫ d.π ∣_ d.V i =
        (d.j ⁻¹ᵁ V).ι ≫ Y.homOfLE (d.U_le i) := by
      rw [← cancel_mono (d.V i).ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
        morphismRestrict_ι_assoc, j_π, Scheme.homOfLE_ι]
    simp only [k, n, Category.assoc]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Scheme.basicOpenToSpecAway_SpecMap_assoc,
      Scheme.homOfLE_ι_assoc, reassoc_of% this, homOfLE_ε]
    rfl
  have hring : Proj.awayToLocalization (𝒜 d) d.φ (X (d.e l)) r *
      algebraMap _ (Localization.Away (d.φ (X (d.e l)))) (d.evalU i (X g)) = 1 := by
    have := d.mono_update l i none
    rw [hl, show d.A i none = 1 from rfl, one_mul] at this
    rw [Proj.awayToLocalization_mk, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
    simp only [pow_one, φ_X, evalU, eval₂Hom_X']
    rw [mul_comm, this]
    exact IsLocalization.mk'_self' (Localization.Away (d.φ (X (d.e l))))
  have hs : IsUnit (m.appTop ((Scheme.ΓSpecIso _).inv r)) := by
    refine IsUnit.of_mul_eq_one (n.appTop ((Scheme.ΓSpecIso _).inv (X g))) ?_
    apply (d.j ∣_ V).app_injective ⊤
    have h₁ : (d.j ∣_ V).appTop (m.appTop ((Scheme.ΓSpecIso _).inv r)) =
        (d.j ∣_ V ≫ m).appTop ((Scheme.ΓSpecIso _).inv r) := rfl
    have h₂ : (d.j ∣_ V).appTop (n.appTop ((Scheme.ΓSpecIso _).inv (X g))) =
        (d.j ∣_ V ≫ n).appTop ((Scheme.ΓSpecIso _).inv (X g)) := rfl
    change (d.j ∣_ V).appTop _ = (d.j ∣_ V).appTop _
    rw [map_mul, map_one, h₁, h₂, hm, hn, appTop_comp_SpecMap_ΓSpecIso_inv,
      appTop_comp_SpecMap_ΓSpecIso_inv, ← map_mul, ← map_mul]
    simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, hring, map_one]
  set y' : V.toScheme := ⟨y, hy₁, hy₂⟩
  have h₂ : y' ∈ m ⁻¹ᵁ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv r) := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hs]
    trivial
  have E : Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos ⁻¹ᵁ d.W l' =
      (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv r) := by
    rw [Proj.awayι_preimage_basicOpen _ _ one_pos (X_mem_homogeneousSubmodule_one (d.e l'))
      one_pos, basicOpen_eq_of_affine]
  have h₃ : y' ∈ m ⁻¹ᵁ Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos ⁻¹ᵁ
      d.W l' := by
    rw [E]
    exact h₂
  have hmι : m ≫ Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos = V.ι ≫ d.q := by
    simp only [m, e, Category.assoc, ← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc,
      morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  have h₄ : (m ≫ Proj.awayι _ _ (X_mem_homogeneousSubmodule_one (d.e l)) one_pos) y' ∈
      d.W l' := h₃
  rwa [hmι] at h₄

/-- Every point of `Y'` maps under `q` to a chart `D₊(X_κ)` with `κ i = none` for some `i`. -/
lemma exists_chart (y : d.Y') : ∃ i κ, κ i = none ∧ d.q y ∈ d.W κ := by
  obtain ⟨i, hi⟩ : ∃ i, d.π y ∈ d.V i :=
    TopologicalSpace.Opens.mem_iSup.mp (d.iSup_V.ge (Set.mem_univ (d.π y)))
  obtain ⟨k, hk⟩ : ∃ k, d.q y ∈ ProjectiveSpace.U d.N R k :=
    TopologicalSpace.Opens.mem_iSup.mp ((iSup_U d.N R).ge (Set.mem_univ (d.q y)))
  have hl : d.q y ∈ d.W (d.e.symm k) := by
    simpa [W, ProjectiveSpace.U] using hk
  cases h : d.e.symm k i with
  | none => exact ⟨i, _, h, hl⟩
  | some g => exact ⟨i, _, Function.update_self .., d.mem_W_update y i _ g h hi hl⟩

/-- **The projection `Y' ⟶ ℙₒ(N; R)` is a closed immersion.** -/
theorem isClosedImmersion_q [IsProper sY] : IsClosedImmersion d.q := by
  refine isClosedImmersion_of_isClosed_range_of_cover d.q d.q.isClosedMap.isClosed_range
    (fun p : {p : d.I × d.K // p.2 p.1 = none} ↦ d.W p.1.2) (fun y ↦ ?_) ?_
  · obtain ⟨i, κ, h, hy⟩ := d.exists_chart y
    exact ⟨⟨(i, κ), h⟩, hy⟩
  · rintro ⟨⟨i, κ⟩, h⟩
    exact d.isClosedImmersion_q_restrict i κ h

/-- **`π : Y' ⟶ Y` is an isomorphism over `U`.** -/
theorem isIso_π_restrict : IsIso (d.π ∣_ d.U) :=
  isIso_graphClosureFst_restrict ..

/-- `Y'` is irreducible if `Y` is. -/
lemma irreducibleSpace_Y' [IrreducibleSpace Y] : IrreducibleSpace d.Y' := by
  have hne : (d.U : Set Y).Nonempty := d.dense_U.nonempty
  have : IrreducibleSpace d.U.toScheme :=
    Subtype.irreducibleSpace ⟨hne, (IrreducibleSpace.isIrreducible_univ Y).2.open_subset
      d.U.isOpen (Set.subset_univ _)⟩
  exact irreducibleSpace_image d.Γ

/-- `Y'` is integral if `Y` is. -/
lemma isIntegral_Y' [IsIntegral Y] : IsIntegral d.Y' :=
  have := d.irreducibleSpace_Y'
  isIntegral_of_irreducibleSpace_of_isReduced _

end Data

/-- A finite type ring map `R → A` admits a surjection `R[x_s] → A` from a polynomial ring on a
finite subset `s ⊆ A`. -/
lemma exists_finset_surjective {A : Type u} [CommRing A] {f : R →+* A} (hf : f.FiniteType) :
    ∃ s : Finset A, Function.Surjective (eval₂Hom f (fun a : s ↦ (a : A))) := by
  letI := f.toAlgebra
  obtain ⟨s, hs⟩ := hf.out
  refine ⟨s, fun b ↦ ?_⟩
  have hb : b ∈ Algebra.adjoin R (Set.range (Subtype.val : s → A)) := by
    rw [Subtype.range_coe, hs]
    trivial
  rw [Algebra.adjoin_range_eq_range_aeval] at hb
  obtain ⟨p, rfl⟩ := hb
  exact ⟨p, (aeval_eq_eval₂Hom _ p).symm⟩

open TopologicalSpace in
/-- **Chow data exist** for an irreducible, quasi-compact, quasi-separated scheme locally of
finite type over `R`. -/
theorem Data.nonempty [IrreducibleSpace Y] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [LocallyOfFiniteType sY] : Nonempty (Data sY) := by
  classical
  have hx (x : Y) : ∃ V : Y.Opens, IsAffineOpen V ∧ x ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set Y))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hgen (x : Y) : ∃ s : Finset Γ(V x, ⊤), Function.Surjective
      (eval₂Hom ((V x).ι ≫ sY).baseHom (fun a : s ↦ (a : Γ(V x, ⊤)))) := by
    have : IsAffine (V x) := hV x
    have hft : ((V x).ι ≫ sY).baseHom.FiniteType := by
      have h := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)
        (f := (V x).ι ≫ sY)).mp inferInstance
      exact h.comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
    exact exists_finset_surjective hft
  choose s hs using hgen
  let η := genericPoint Y
  have hη (x : Y) : η ∈ V x :=
    ((genericPoint_spec Y).mem_open_set_iff (V x).isOpen).mpr ⟨x, trivial, hxV x⟩
  have hS : IsOpen (⋂ x : t, (V x : Set Y)) := isOpen_iInter_of_finite fun x ↦ (V x).isOpen
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, hUS⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 fun (x : t) ↦ hη x) hS
  have : IsAffine U := hU
  exact ⟨{
    I := t
    V := fun x ↦ V x
    isAffineOpen_V := fun x ↦ hV x
    iSup_V := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
      exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy⟩
    G := fun x ↦ s x
    a := fun x a ↦ a
    surjective := fun x ↦ hs x
    U := U
    U_le := fun x ↦ hUS.trans (Set.iInter_subset (fun x : t ↦ (V x : Set Y)) x)
    dense_U := U.isOpen.dense ⟨η, hηU⟩
    quasiCompact_U := inferInstance }⟩

end Chow

/-- **Chow's lemma** (EGA II 5.6.1, integral case). Let `Y` be an integral scheme, proper over
`Spec R`. There are `N`, a closed immersion
`c : Y' ⟶ Y ×_R ℙₒ(N; R)` from an integral scheme `Y'` whose second projection `Y' ⟶ ℙₒ(N; R)` is
a closed immersion, and a nonempty open `U ⊆ Y` over which the first projection `π : Y' ⟶ Y`
restricts to an isomorphism `π⁻¹ U ≅ U`. -/
theorem exists_chow {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of R)) [IsIntegral Y] [IsProper sY] :
    ∃ (N : ℕ) (Y' : Scheme.{u}) (c : Y' ⟶ pullback sY (ProjectiveSpace.toSpec N R))
      (U : Y.Opens), IsClosedImmersion c ∧ IsClosedImmersion (c ≫ pullback.snd _ _) ∧
      (U : Set Y).Nonempty ∧ IsIso ((c ≫ pullback.fst _ _) ∣_ U) ∧ IsIntegral Y' := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated sY
  obtain ⟨d⟩ := Chow.Data.nonempty (sY := sY)
  exact ⟨d.N, d.Y', d.c, d.U, inferInstance, d.isClosedImmersion_q, d.dense_U.nonempty,
    d.isIso_π_restrict, d.isIntegral_Y'⟩

/-- **Chow's lemma** (EGA II 5.6.1, irreducible case). Let `Y` be an irreducible scheme, proper
over `Spec R`. There are `N`, a closed immersion `c : Y' ⟶ Y ×_R ℙₒ(N; R)` from an irreducible
scheme `Y'` whose second projection `Y' ⟶ ℙₒ(N; R)` is a closed immersion, and a nonempty open
`U ⊆ Y` over which the first projection `π : Y' ⟶ Y` restricts to an isomorphism `π⁻¹ U ≅ U`;
moreover `π⁻¹ U` is scheme-theoretically dense in `Y'`. -/
theorem exists_chow_of_irreducibleSpace {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of R)) [IrreducibleSpace Y] [IsProper sY] :
    ∃ (N : ℕ) (Y' : Scheme.{u}) (c : Y' ⟶ pullback sY (ProjectiveSpace.toSpec N R))
      (U : Y.Opens), IsClosedImmersion c ∧ IsClosedImmersion (c ≫ pullback.snd _ _) ∧
      (U : Set Y).Nonempty ∧ IsIso ((c ≫ pullback.fst _ _) ∣_ U) ∧ IrreducibleSpace Y' ∧
      IsSchemeTheoreticallyDominant ((c ≫ pullback.fst _ _) ⁻¹ᵁ U).ι := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated sY
  obtain ⟨d⟩ := Chow.Data.nonempty (sY := sY)
  exact ⟨d.N, d.Y', d.c, d.U, inferInstance, d.isClosedImmersion_q, d.dense_U.nonempty,
    d.isIso_π_restrict, d.irreducibleSpace_Y', inferInstance⟩

end AlgebraicGeometry

end
