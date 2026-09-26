/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Other.Oka.Topology.Sheaves.Cohomology.Basic

/-!
# The Čech complex of an abelian presheaf

Let `U : ι → Opens X` be a family of opens and `P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat` an abelian
presheaf. For `σ : Fin (n + 1) → ι` write `U_σ = U (σ 0) ∩ ⋯ ∩ U (σ n)`
(`TopCat.Presheaf.cechOpen U σ`). The (ordered) Čech complex `Č•(U, P)` has

* degree `n` term `CechCochain U P n = ∀ σ : Fin (n + 1) → ι, P(U_σ)`
  (`TopCat.Presheaf.cechComplex_X`),
* differential `(d c)(τ) = ∑ⱼ (-1)ʲ c(τ ∘ δⱼ)|_{U_τ}` where `δⱼ = Fin.succAbove j`
  (`TopCat.Presheaf.cechD`, `TopCat.Presheaf.cechComplex_d_apply`).

It is defined as the alternating coface complex of a cosimplicial abelian group
(`TopCat.Presheaf.cechCosimplicial`), so that `d ∘ d = 0` comes for free, and it is functorial
in `P` (`TopCat.Presheaf.cechComplexFunctor`). The Čech cohomology is
`(cechComplex U P).homology n`.

## Main results

* `TopCat.Presheaf.exactAt_cechComplex_succ_iff`: exactness in degree `n + 1` in terms of
  cochains; `TopCat.Presheaf.IsCechAcyclic U P` says the complex is exact in all positive degrees.
* `TopCat.Presheaf.cechAugment_injective`, `TopCat.Presheaf.exists_cechAugment_eq`:
  for a sheaf `F` and a family `U` covering `W`, `0 → F(W) → Č⁰ → Č¹` is exact, i.e.
  Čech `H⁰(U, F) = F(W)` (`TopCat.Presheaf.cechAugmentAddEquivKer`).
* `TopCat.Presheaf.cechComplex_shortExact`: a short exact sequence of presheaves which is short
  exact on every finite intersection `U_σ` gives a short exact sequence of Čech complexes, hence
  (via `ShortComplex.ShortExact.homology_exact₁` etc.) the long exact sequence of Čech cohomology;
  `TopCat.Presheaf.cechComplex_shortExact_of_sheaf` is the version for a short exact sequence
  of sheaves, where only surjectivity on the `U_σ` has to be checked.
-/

@[expose] public section

universe w u

open CategoryTheory Limits TopologicalSpace Opposite Simplicial

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X)

/-- The intersection `U_σ = U (σ 0) ∩ ⋯ ∩ U (σ n)`. -/
def cechOpen {n : ℕ} (σ : Fin (n + 1) → ι) : Opens X := ⨅ a, U (σ a)

lemma cechOpen_le_comp {m n : ℕ} (τ : Fin (n + 1) → ι) (θ : Fin (m + 1) → Fin (n + 1)) :
    cechOpen U τ ≤ cechOpen U (τ ∘ θ) :=
  le_iInf fun a => iInf_le _ (θ a)

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- Čech `n`-cochains: families of sections over the `(n+1)`-fold intersections. -/
abbrev CechCochain (n : ℕ) : Type (max w u) := ∀ σ : Fin (n + 1) → ι, P.obj (op (cechOpen U σ))

/-- The map on Čech cochains induced by a map `θ : Fin (m+1) → Fin (n+1)`. -/
def cechMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : CechCochain U P m →+ CechCochain U P n where
  toFun c τ := P.map (homOfLE (cechOpen_le_comp U τ θ)).op (c (τ ∘ θ))
  map_zero' := by ext; simp
  map_add' c c' := by ext; simp

lemma cechMap_apply {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (c : CechCochain U P m) (τ) :
    cechMap U P θ c τ = P.map (homOfLE (cechOpen_le_comp U τ θ)).op (c (τ ∘ θ)) := rfl

lemma cechMap_id {n : ℕ} (c : CechCochain U P n) : cechMap U P id c = c := by
  ext τ
  change (P.map (𝟙 (op (cechOpen U τ)))) (c τ) = c τ
  rw [P.map_id]
  rfl

lemma cechMap_comp {l m n : ℕ} (θ : Fin (l + 1) → Fin (m + 1)) (θ' : Fin (m + 1) → Fin (n + 1))
    (c : CechCochain U P l) : cechMap U P (θ' ∘ θ) c = cechMap U P θ' (cechMap U P θ c) := by
  ext τ
  simp only [cechMap_apply]
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

/-- The Čech cosimplicial object of `P` with respect to `U`. -/
def cechCosimplicial : CosimplicialObject AddCommGrpCat.{max w u} where
  obj Δ := AddCommGrpCat.of (CechCochain U P Δ.len)
  map θ := AddCommGrpCat.ofHom (cechMap U P θ.toOrderHom)
  map_id Δ := by ext c : 2; exact cechMap_id U P c
  map_comp θ θ' := by
    ext c : 2
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
      Function.comp_apply]
    rw [← cechMap_comp]
    rfl

variable {P} in
/-- The map on Čech cochains induced by a morphism of presheaves. -/
def cechCochainMap {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (n : ℕ) :
    CechCochain U P n →+ CechCochain U Q n where
  toFun c σ := φ.app _ (c σ)
  map_zero' := by ext; simp
  map_add' c c' := by ext; simp

/-- The Čech cosimplicial object, as a functor of the presheaf. -/
def cechCosimplicialFunctor :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CosimplicialObject AddCommGrpCat.{max w u} where
  obj P := cechCosimplicial U P
  map φ :=
    { app Δ := AddCommGrpCat.ofHom (cechCochainMap U φ Δ.len)
      naturality Δ Δ' θ := by
        ext c : 2
        funext τ
        exact ConcreteCategory.congr_hom (φ.naturality _) _ }

/-- The Čech complex functor: `P ↦ Č•(U, P)`, the alternating coface complex of the Čech
cosimplicial object. -/
def cechComplexFunctor :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{max w u} ℕ :=
  cechCosimplicialFunctor U ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

/-- The Čech complex `Č•(U, P)`. -/
abbrev cechComplex : CochainComplex AddCommGrpCat.{max w u} ℕ := (cechComplexFunctor U).obj P

lemma cechComplex_X (n : ℕ) : (cechComplex U P).X n = AddCommGrpCat.of (CechCochain U P n) := rfl

/-- The Čech differential `Čⁿ → Čⁿ⁺¹`, `d = ∑ⱼ (-1)ʲ δʲ`. -/
def cechD (n : ℕ) : CechCochain U P n →+ CechCochain U P (n + 1) :=
  ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • cechMap U P j.succAbove

/-- `(d c)(τ) = ∑ⱼ (-1)ʲ c(τ ∘ δⱼ)|_{U_τ}`. -/
lemma cechD_apply (n : ℕ) (c : CechCochain U P n) (τ : Fin (n + 2) → ι) :
    cechD U P n c τ = ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      P.map (homOfLE (cechOpen_le_comp U τ j.succAbove)).op (c (τ ∘ j.succAbove)) := by
  simp [cechD, Finset.sum_apply, cechMap_apply]

lemma cechComplex_d (n : ℕ) :
    (cechComplex U P).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial U P) n :=
  CochainComplex.of_d (V := AddCommGrpCat.{max w u}) _
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial U P)) n

lemma _root_.AddCommGrpCat.finsetSum_apply {M N : AddCommGrpCat.{w}} {α : Type*} (s : Finset α)
    (f : α → (M ⟶ N)) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma cechComplex_d_apply (n : ℕ) (c : (cechComplex U P).X n) (τ : Fin (n + 2) → ι) :
    ((cechComplex U P).d n (n + 1) c : CechCochain U P (n + 1)) τ =
      cechD U P n c τ := by
  rw [cechComplex_d, AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  erw [AddCommGrpCat.finsetSum_apply]
  simp only [cechD, CosimplicialObject.δ, cechCosimplicial]
  erw [Finset.sum_apply, AddMonoidHom.finsetSum_apply, Finset.sum_apply]
  rfl

lemma cechComplexFunctor_map_f_apply {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (n : ℕ)
    (c : (cechComplex U P).X n) (σ : Fin (n + 1) → ι) :
    (((cechComplexFunctor U).map φ).f n c : CechCochain U Q n) σ =
      φ.app _ ((c : CechCochain U P n) σ) := rfl

/-- Restriction maps compose. -/
lemma map_homOfLE_map_homOfLE {A B C : Opens X} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : P.obj (op C)) :
    P.map (homOfLE h₁).op (P.map (homOfLE h₂).op x) = P.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

/-- Restricting a component of a cochain only depends on the index up to equality. -/
lemma map_homOfLE_congr {n : ℕ} (c : CechCochain U P n) {σ σ' : Fin (n + 1) → ι} (h : σ = σ')
    {W : Opens X} (hW : W ≤ cechOpen U σ) (hW' : W ≤ cechOpen U σ') :
    P.map (homOfLE hW).op (c σ) = P.map (homOfLE hW').op (c σ') := by
  subst h
  rfl

/-- The Čech complex is exact in all positive degrees. -/
def IsCechAcyclic : Prop := ∀ n : ℕ, (cechComplex U P).ExactAt (n + 1)

/-- Exactness of the Čech complex in degree `n + 1`, in terms of cochains. -/
lemma exactAt_cechComplex_succ_iff (n : ℕ) :
    (cechComplex U P).ExactAt (n + 1) ↔ ∀ c : CechCochain U P (n + 1),
      cechD U P (n + 1) c = 0 → ∃ b : CechCochain U P n, cechD U P n b = c := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  have h₁ : ∀ b : (cechComplex U P).X n,
      ((cechComplex U P).d n (n + 1) b : CechCochain U P (n + 1)) = cechD U P n b :=
    fun b => funext fun τ => cechComplex_d_apply U P n b τ
  have h₂ : ∀ c : (cechComplex U P).X (n + 1),
      ((cechComplex U P).d (n + 1) (n + 2) c : CechCochain U P (n + 2)) = cechD U P (n + 1) c :=
    fun c => funext fun τ => cechComplex_d_apply U P (n + 1) c τ
  constructor
  · intro H c hc
    obtain ⟨b, hb⟩ := H c ((h₂ c).trans hc)
    exact ⟨b, (h₁ b).symm.trans hb⟩
  · intro H c hc
    obtain ⟨b, hb⟩ := H c ((h₂ c).symm.trans hc)
    exact ⟨b, (h₁ b).trans hb⟩

lemma isCechAcyclic_iff : IsCechAcyclic U P ↔ ∀ (n : ℕ) (c : CechCochain U P (n + 1)),
    cechD U P (n + 1) c = 0 → ∃ b : CechCochain U P n, cechD U P n b = c :=
  forall_congr' fun n => exactAt_cechComplex_succ_iff U P n

section Augmentation

variable {W : Opens X} (hW : ∀ i, U i ≤ W)

include hW in
lemma cechOpen_le {n : ℕ} (σ : Fin (n + 1) → ι) : cechOpen U σ ≤ W :=
  (iInf_le _ 0).trans (hW _)

/-- The augmentation `P(W) → Č⁰(U, P)`, `s ↦ (s|_{U_i})ᵢ`, for a family `U` of opens of `W`. -/
def cechAugment : P.obj (op W) →+ CechCochain U P 0 where
  toFun s σ := P.map (homOfLE (cechOpen_le U hW σ)).op s
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

lemma cechAugment_apply (s : P.obj (op W)) (σ : Fin 1 → ι) :
    cechAugment U P hW s σ = P.map (homOfLE (cechOpen_le U hW σ)).op s := rfl

lemma cechD_cechAugment (s : P.obj (op W)) : cechD U P 0 (cechAugment U P hW s) = 0 := by
  ext τ
  rw [cechD_apply, Fin.sum_univ_two]
  simp only [cechAugment_apply, map_homOfLE_map_homOfLE, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, Pi.zero_apply]
  exact add_neg_eq_zero.2 rfl

lemma fin_one_eq_const (σ : Fin 1 → ι) : σ = fun _ => σ 0 :=
  funext fun a => by rw [Subsingleton.elim a 0]

/-- The open `U i`, seen as the intersection `U_σ` for the constant `σ : Fin 1 → ι`. -/
lemma cechOpen_const (i : ι) : cechOpen U (fun _ : Fin 1 => i) = U i := by
  simp [cechOpen]

omit hW in
/-- The cocycle condition for a Čech `0`-cochain: the components agree on overlaps. -/
lemma cocycle_zero_compat (c : CechCochain U P 0) (hc : cechD U P 0 c = 0) (i j : ι)
    {W' : Opens X} (hi : W' ≤ cechOpen U (fun _ : Fin 1 => i))
    (hj : W' ≤ cechOpen U (fun _ : Fin 1 => j)) :
    P.map (homOfLE hi).op (c (fun _ => i)) = P.map (homOfLE hj).op (c (fun _ => j)) := by
  let τ : Fin 2 → ι := ![i, j]
  have hτ : W' ≤ cechOpen U τ := by
    refine le_iInf fun a => ?_
    fin_cases a
    · exact hi.trans (iInf_le _ 0)
    · exact hj.trans (iInf_le _ 0)
  have h := congrFun hc τ
  rw [cechD_apply, Fin.sum_univ_two] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Pi.zero_apply] at h
  have h' := congrArg (P.map (homOfLE hτ).op) (add_neg_eq_zero.1 h)
  simp only [map_homOfLE_map_homOfLE] at h'
  have e₀ : τ ∘ Fin.succAbove 0 = fun _ => j := funext fun a => by fin_cases a; rfl
  have e₁ : τ ∘ Fin.succAbove 1 = fun _ => i := funext fun a => by fin_cases a; rfl
  rw [map_homOfLE_congr U P c e₀ _ hj, map_homOfLE_congr U P c e₁ _ hi] at h'
  exact h'.symm

variable (F : TopCat.AbSheaf X) (hcov : W ≤ ⨆ i, U i)

include hcov in
/-- For a sheaf, `F(W) → Č⁰(U, F)` is injective if `U` covers `W`. -/
lemma cechAugment_injective : Function.Injective (cechAugment U F.obj hW) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Sheaf.eq_of_locally_eq' (F := (F : X.Sheaf AddCommGrpCat.{u}))
    (fun i => cechOpen U (fun _ : Fin 1 => i)) W (fun i => homOfLE (cechOpen_le U hW _)) ?_ s 0
    fun i => ?_
  · exact hcov.trans (iSup_mono fun i => (cechOpen_const U i).ge)
  · rw [map_zero]
    exact congrFun hs (fun _ => i)

include hcov in
/-- For a sheaf, a Čech `0`-cocycle comes from a section over `W` if `U` covers `W`. -/
lemma exists_cechAugment_eq (c : CechCochain U F.obj 0) (hc : cechD U F.obj 0 c = 0) :
    ∃ s : F.obj.obj (op W), cechAugment U F.obj hW s = c := by
  let V : ι → Opens X := fun i => cechOpen U (fun _ : Fin 1 => i)
  have hcompat : TopCat.Presheaf.IsCompatible (F : X.Sheaf AddCommGrpCat.{u}).1 V
      (fun i => c (fun _ => i)) := fun i j =>
    cocycle_zero_compat U F.obj c hc i j _ _
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := (F : X.Sheaf AddCommGrpCat.{u}))
    V W
    (fun i => homOfLE (cechOpen_le U hW _))
    (hcov.trans (iSup_mono fun i => (cechOpen_const U i).ge)) _ hcompat
  refine ⟨s, funext fun σ => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, σ = fun _ => i := ⟨σ 0, fin_one_eq_const σ⟩
  exact hs i

/-- Čech `H⁰(U, F) = F(W)` for a sheaf `F` and a family `U` covering `W`: the augmentation is an
isomorphism of `F(W)` onto the Čech `0`-cocycles. -/
noncomputable def cechAugmentAddEquivKer : F.obj.obj (op W) ≃+ (cechD U F.obj 0).ker :=
  AddEquiv.ofBijective
    ((cechAugment U F.obj hW).codRestrict _ fun s => cechD_cechAugment U F.obj hW s)
    ⟨fun _ _ h => cechAugment_injective U hW F hcov (congrArg Subtype.val h), fun c => by
      obtain ⟨s, hs⟩ := exists_cechAugment_eq U hW F hcov c.1 c.2
      exact ⟨s, Subtype.ext hs⟩⟩

@[simp]
lemma cechAugmentAddEquivKer_apply_coe (s : F.obj.obj (op W)) :
    (cechAugmentAddEquivKer U hW F hcov s : CechCochain U F.obj 0) = cechAugment U F.obj hW s :=
  rfl

end Augmentation

instance : (cechComplexFunctor.{w} U).Additive where
  map_add {P Q} φ ψ := by
    ext n c : 3
    rfl

section ShortExact

variable {U}

/-- A short exact sequence of presheaves which is short exact on every finite intersection
`U_σ` induces a short exact sequence of Čech complexes. -/
lemma cechComplex_shortExact {S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})}
    (hS : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
      (S.map ((evaluation _ _).obj (op (cechOpen U σ)))).ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  have hinj : ∀ σ : Fin (n + 1) → ι, Function.Injective (S.f.app (op (cechOpen U σ))) :=
    fun σ => (AddCommGrpCat.mono_iff_injective _).1 (hS n σ).mono_f
  have hsurj : ∀ σ : Fin (n + 1) → ι, Function.Surjective (S.g.app (op (cechOpen U σ))) :=
    fun σ => (AddCommGrpCat.epi_iff_surjective _).1 (hS n σ).epi_g
  have hex : ∀ σ : Fin (n + 1) → ι, ∀ y, S.g.app (op (cechOpen U σ)) y = 0 →
      ∃ x, S.f.app (op (cechOpen U σ)) x = y :=
    fun σ => (ShortComplex.ab_exact_iff _).1 (hS n σ).exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    intro y hy
    choose x hx using fun σ => hex σ (y σ) (congrFun hy σ)
    exact ⟨x, funext hx⟩
  · rw [AddCommGrpCat.mono_iff_injective]
    intro x x' h
    exact funext fun σ => hinj σ (congrFun h σ)
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    choose x hx using fun σ => hsurj σ (y σ)
    exact ⟨x, funext hx⟩

/-- Sections of a short exact sequence of sheaves form a left exact sequence. -/
lemma sections_exact {S : ShortComplex (TopCat.AbSheaf X)} (hS : S.ShortExact) (V : Opens X) :
    Function.Injective (S.f.hom.app (op V)) ∧
      ∀ y, S.g.hom.app (op V) y = 0 → ∃ x, S.f.hom.app (op V) x = y := by
  let G : TopCat.AbSheaf X ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)
  have : Mono (G.map S.f) := by have := hS.mono_f; infer_instance
  have hex : (S.map G).Exact := hS.exact.map_of_mono_of_preservesKernel G hS.mono_f inferInstance
  exact ⟨(AddCommGrpCat.mono_iff_injective _).1 this, (ShortComplex.ab_exact_iff _).1 hex⟩

/-- A short exact sequence of sheaves which is surjective on sections over every finite
intersection `U_σ` induces a short exact sequence of Čech complexes. -/
lemma cechComplex_shortExact_of_sheaf {S : ShortComplex (TopCat.AbSheaf X)} (hS : S.ShortExact)
    (hsurj : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
      Function.Surjective (S.g.hom.app (op (cechOpen U σ)))) :
    ((S.map (sheafToPresheaf _ _)).map (cechComplexFunctor U)).ShortExact := by
  refine cechComplex_shortExact fun n σ => ?_
  obtain ⟨hinj, hex⟩ := sections_exact hS (cechOpen U σ)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (ShortComplex.ab_exact_iff _).2 hex
  · exact (AddCommGrpCat.mono_iff_injective _).2 hinj
  · exact (AddCommGrpCat.epi_iff_surjective _).2 (hsurj n σ)

end ShortExact

end TopCat.Presheaf

end
