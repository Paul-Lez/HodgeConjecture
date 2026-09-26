/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
public import Other.Oka.Topology.Sheaves.Cohomology.Restrict

/-!
# Cohomology of opens and the Mayer–Vietoris sequence

Mathlib defines the cohomology of an abelian sheaf `F` on an open `U` as
`CategoryTheory.Sheaf.H' F n U = Extⁿ(ℤ[U], F)`, where `ℤ[U]` is the free abelian sheaf on the
representable presheaf `yoneda U` (`TopCat.Sheaf.freeYoneda U`), and proves the Mayer–Vietoris
sequence for it. We identify it with the cohomology of the restricted sheaf:

* `TopCat.Sheaf.H'AddEquiv U F n : H' F n U ≃+ Hⁿ(U, F|_U)`;
* `TopCat.Sheaf.H'TopAddEquiv F n : H' F n ⊤ ≃+ Hⁿ(X, F)`;
* `TopCat.Sheaf.mayerVietorisSequence U V F n₀ n₁ h` and `TopCat.Sheaf.mayerVietorisSequence_exact`:
  the Mayer–Vietoris long exact sequence
  `H'ⁿ(U ∪ V) → H'ⁿ(U) ⊞ H'ⁿ(V) → H'ⁿ(U ∩ V) → H'ⁿ⁺¹(U ∪ V) → ⋯`.

The comparison is a general dimension shifting statement
(`CategoryTheory.extComparison_bijective`): for an exact functor `R` preserving injectives and
`η : A ⟶ R Z` such that `x ↦ η ≫ R x` is bijective on morphisms, `x ↦ η ∘ R(x)` is bijective on
all `Ext`-groups. It is applied to the restriction `R = (-)|_U` (which preserves injectives,
`TopCat.Sheaf.preservesInjectiveObjects_restrictAb`) and the canonical `ℤ_U ⟶ ℤ[U]|_U`: both
`Hom(ℤ[U], B)` and `Hom(ℤ_U, B|_U)` are `B(U)`.

The compatibility of these identifications with the restriction maps of `H'` (which appear in the
Mayer–Vietoris sequence) and with `TopCat.Sheaf.H.restrict` is not proved here.
-/

@[expose] public section

universe w w' v v' u u'

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [R.PreservesInjectiveObjects] {Z : C} {A : D} (η : A ⟶ R.obj Z)

/-- The comparison map `Ext(Z, B) → Ext(A, R B)`, `x ↦ η ∘ R(x)`. -/
noncomputable def extComparison (B : C) (n : ℕ) : Ext Z B n →+ Ext A (R.obj B) n :=
  ((Ext.mk₀ η).precomp (R.obj B) (zero_add n)).comp (R.mapExtAddHom Z B n)

omit [EnoughInjectives C] [R.PreservesInjectiveObjects] in
lemma extComparison_apply {B : C} {n : ℕ} (x : Ext Z B n) :
    extComparison R η B n x = (Ext.mk₀ η).comp (x.mapExactFunctor R) (zero_add n) := rfl

attribute [local instance] Ext.subsingleton_of_injective in
/-- If `x ↦ η ≫ R.map x` is bijective on morphisms, then the comparison map is bijective on all
`Ext` groups (dimension shifting). -/
theorem extComparison_bijective
    (h₀ : ∀ B : C, Function.Bijective (fun x : Z ⟶ B => η ≫ R.map x)) (B : C) (n : ℕ) :
    Function.Bijective (extComparison R η B n) := by
  induction n generalizing B with
  | zero =>
    have e : ∀ x : Z ⟶ B, extComparison R η B 0 (Ext.mk₀ x) = Ext.mk₀ (η ≫ R.map x) := by
      intro x
      rw [extComparison_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    constructor
    · intro x y hxy
      obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective Z B).2 x
      obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective Z B).2 y
      rw [e, e] at hxy
      rw [(h₀ B).1 ((Ext.mk₀_bijective _ _).1 hxy)]
    · intro z
      obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective A (R.obj B)).2 z
      obtain ⟨x, rfl⟩ := (h₀ B).2 z
      exact ⟨Ext.mk₀ x, e x⟩
  | succ n hn =>
    let I : InjectivePresentation B := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map R).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extComparison R η S.X₂ n) (extComparison R η S.X₃ n) (extComparison R η S.X₁ (n + 1))
      (by
        ext x
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, extComparison_apply,
          AddCommGrpCat.hom_ofHom, Ext.postcomp, AddMonoidHom.flip_apply,
          Ext.bilinearComp_apply_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
        erw [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply]
        exact Ext.comp_assoc_of_third_deg_zero _ _ _ _)
      (by
        ext x
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, extComparison_apply,
          AddCommGrpCat.hom_ofHom, Ext.postcomp, AddMonoidHom.flip_apply,
          Ext.bilinearComp_apply_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
        erw [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply]
        exact Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' Z hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map R) y₁ (by subsingleton) rfl)

end CategoryTheory

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)

/-- The free abelian sheaf `ℤ[U]` on the representable `yoneda U`. -/
noncomputable abbrev freeYoneda : AbSheaf X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- Morphisms out of `ℤ[U]` are sections over `U`. -/
noncomputable def freeYonedaHomEquiv (B : AbSheaf X) :
    (freeYoneda U ⟶ B) ≃ B.obj.obj (op U) :=
  ((sheafificationAdjunction _ _).homEquiv _ B).trans <|
    ((AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj U) B.obj).trans yonedaEquiv

lemma freeYonedaHomEquiv_comp {B B' : AbSheaf X} (x : freeYoneda U ⟶ B) (g : B ⟶ B') :
    freeYonedaHomEquiv U B' (x ≫ g) = g.hom.app (op U) (freeYonedaHomEquiv U B x) := by
  simp only [freeYonedaHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]


/-- Morphisms out of `ℤ_Y` are global sections. -/
noncomputable def constZHomEquiv {Y : TopCat.{u}} (G : AbSheaf Y) :
    (constZ Y ⟶ G) ≃ G.obj.obj (op ⊤) :=
  ((constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).homEquiv _ G).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

lemma constZHomEquiv_comp {Y : TopCat.{u}} {G G' : AbSheaf Y} (x : constZ Y ⟶ G) (g : G ⟶ G') :
    constZHomEquiv G' (x ≫ g) = g.hom.app (op ⊤) (constZHomEquiv G x) := by
  simp only [constZHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right]
  rfl

lemma restrictOpenGlobalSectionsIso_inv_naturality {F G : AbSheaf X} (φ : F ⟶ G)
    (s : F.obj.obj (op U)) :
    ((restrictOpen U).map φ).hom.app (op ⊤) ((restrictOpenGlobalSectionsIso U F).inv s) =
      (restrictOpenGlobalSectionsIso U G).inv (φ.hom.app (op U) s) := by
  simp only [restrictOpenGlobalSectionsIso, Functor.mapIso_inv]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  congr 2
  exact φ.hom.naturality _

/-- The canonical map `ℤ_U ⟶ ℤ[U]|_U`, corresponding to the section `1 ∈ ℤ[U](U)`. -/
noncomputable def freeYonedaUnit :
    constZ ((Opens.toTopCat X).obj U) ⟶ (restrictOpen U).obj (freeYoneda U) :=
  (constZHomEquiv _).symm
    ((restrictOpenGlobalSectionsIso U _).inv (freeYonedaHomEquiv U _ (𝟙 _)))

lemma freeYonedaUnit_comp_bijective (B : AbSheaf X) :
    Function.Bijective (fun x : freeYoneda U ⟶ B => freeYonedaUnit U ≫ (restrictOpen U).map x) := by
  have : (fun x : freeYoneda U ⟶ B => freeYonedaUnit U ≫ (restrictOpen U).map x) =
      (constZHomEquiv _).symm ∘ (restrictOpenGlobalSectionsIso U B).addCommGroupIsoToAddEquiv.symm ∘
        freeYonedaHomEquiv U B := by
    funext x
    apply (constZHomEquiv _).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, constZHomEquiv_comp, freeYonedaUnit]
    rw [restrictOpenGlobalSectionsIso_inv_naturality, ← freeYonedaHomEquiv_comp, Category.id_comp]
    rfl
  rw [this]
  exact (constZHomEquiv _).symm.bijective.comp
    ((restrictOpenGlobalSectionsIso U B).addCommGroupIsoToAddEquiv.symm.bijective.comp
      (freeYonedaHomEquiv U B).bijective)

/-- **Cohomology of an open.** Mathlib's `Hⁿ(U, F) = Extⁿ(ℤ[U], F)` (`CategoryTheory.Sheaf.H'`)
is the cohomology of the restriction `F|_U` of `F` to the subspace `U`. -/
noncomputable def H'AddEquiv (F : AbSheaf X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{u} F n U ≃+ H ((restrictOpen U).obj F) n :=
  AddEquiv.ofBijective (extComparison (restrictOpen U) (freeYonedaUnit U) F n)
    (extComparison_bijective _ _ (freeYonedaUnit_comp_bijective U) F n)

instance : (𝟭 (AbSheaf X)).PreservesInjectiveObjects := ⟨fun h => h⟩

/-- The canonical map `ℤ_X ⟶ ℤ[X]`, corresponding to `1 ∈ ℤ[X](X)`. -/
noncomputable def freeYonedaTopUnit : constZ X ⟶ freeYoneda (⊤ : Opens X) :=
  (constZHomEquiv _).symm (freeYonedaHomEquiv ⊤ _ (𝟙 _))

lemma freeYonedaTopUnit_comp_bijective (B : AbSheaf X) :
    Function.Bijective (fun x : freeYoneda (⊤ : Opens X) ⟶ B =>
      freeYonedaTopUnit ≫ (𝟭 (AbSheaf X)).map x) := by
  have : (fun x : freeYoneda (⊤ : Opens X) ⟶ B => freeYonedaTopUnit ≫ (𝟭 (AbSheaf X)).map x) =
      (constZHomEquiv _).symm ∘ freeYonedaHomEquiv ⊤ B := by
    funext x
    apply (constZHomEquiv _).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Functor.id_map, constZHomEquiv_comp,
      freeYonedaTopUnit]
    rw [← freeYonedaHomEquiv_comp, Category.id_comp]
    exact ((constZHomEquiv B).apply_symm_apply _).symm
  rw [this]
  exact (constZHomEquiv _).symm.bijective.comp (freeYonedaHomEquiv ⊤ B).bijective

/-- Mathlib's `Hⁿ(⊤, F) = Extⁿ(ℤ[X], F)` is the cohomology `Hⁿ(X, F)`. -/
noncomputable def H'TopAddEquiv (F : AbSheaf X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{u} F n (⊤ : Opens X) ≃+ H F n :=
  AddEquiv.ofBijective (extComparison (𝟭 (AbSheaf X)) freeYonedaTopUnit F n)
    (extComparison_bijective _ _ freeYonedaTopUnit_comp_bijective F n)

variable (V : Opens X) (F : AbSheaf X)

/-- The **Mayer–Vietoris sequence** of two opens `U`, `V`:
`H'ⁿ⁰(U ∪ V) → H'ⁿ⁰(U) ⊞ H'ⁿ⁰(V) → H'ⁿ⁰(U ∩ V) → H'ⁿ¹(U ∪ V) → H'ⁿ¹(U) ⊞ H'ⁿ¹(V) →
H'ⁿ¹(U ∩ V)`, where `H'ⁿ(W) = CategoryTheory.Sheaf.H' F n W ≃+ Hⁿ(W, F|_W)` (`H'AddEquiv`). -/
noncomputable abbrev mayerVietorisSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (Opens.mayerVietorisSquare U V).sequence F n₀ n₁ h

lemma mayerVietorisSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (mayerVietorisSequence U V F n₀ n₁ h).Exact :=
  (Opens.mayerVietorisSquare U V).sequence_exact F n₀ n₁ h

end TopCat.Sheaf

end
