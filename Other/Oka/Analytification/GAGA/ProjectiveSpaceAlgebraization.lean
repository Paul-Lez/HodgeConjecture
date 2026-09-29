/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveGAGAHom
public import Other.Oka.Analytification.GAGA.SheafAnalytificationIsCoherent
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkSurjective

/-!
# Algebraisation of coherent analytic sheaves on `ℙⁿ_an` from algebraic generation

A sheaf of modules `M` on `ℙⁿ_an` is *algebraically generated at `y`*
(`ComplexAnalytic.projectiveSpaceAn.IsAlgGeneratedAt`) if some `F^an ⟶ M`, `F` coherent on `ℙⁿ`,
is surjective on the stalk at `y`.

- `exists_epi_of_forall_isAlgGeneratedAt`: if `M` is of finite type and algebraically generated at
  every point, then `M` is a quotient of `(𝒪^J(-m))^an` for a finite `J`. Surjectivity on stalks
  spreads to neighbourhoods, `ℙⁿ_an` is compact, and by Serre's theorem A each of the finitely
  many `F` is a quotient of some `𝒪^I(-m)` with a common `m`.
- `exists_iso_of_forall_exists_epi` (Serre): if every coherent analytic sheaf is a quotient of the
  analytification of a coherent algebraic sheaf, then every coherent analytic sheaf is algebraic.
  Choose `p₀ : F₀^an ↠ M`; its kernel is coherent (Oka), so choose `p₁ : F₁^an ↠ ker p₀`. By GAGA-2
  the composite `F₁^an ⟶ F₀^an` is `φ^an`, and `M ≅ coker (φ^an) ≅ (coker φ)^an` because
  analytification is right exact.
- `exists_iso_of_forall_isAlgGeneratedAt`: the combination of the two.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic.projectiveSpaceAn

variable {n : ℕ}

/-- **Algebraisation from algebraic generation**: if every coherent analytic sheaf on `ℙⁿ_an` is
a quotient of the analytification of a coherent algebraic sheaf, then every coherent analytic
sheaf on `ℙⁿ_an` is isomorphic to the analytification of a coherent algebraic sheaf. -/
theorem exists_iso_of_forall_exists_epi
    (h : ∀ M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf,
      M.IsCoherent → ∃ (F : SheafOfModules.{u}
        (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) (_ : F.IsCoherent)
        (p : (analytificationModules (projectiveSpace.{u} n)).obj F ⟶ M), Epi p)
    (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    (hM : M.IsCoherent) :
    ∃ F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules (projectiveSpace.{u} n)).obj F ≅ M) := by
  obtain ⟨F₀, hF₀, p₀, hp₀⟩ := h M hM
  haveI := hF₀
  haveI := isCoherent_analytificationModules (projectiveSpace.{u} n) F₀
  haveI := hM
  obtain ⟨F₁, hF₁, p₁, hp₁⟩ := h (kernel p₀) (SheafOfModules.IsCoherent.kernel p₀)
  haveI := hF₁
  obtain ⟨φ, hφ⟩ := (gaga₂_projectiveSpace n F₁ F₀).2 (p₁ ≫ kernel.ι p₀)
  refine ⟨cokernel φ, SheafOfModules.IsCoherent.cokernel φ, ⟨?_⟩⟩
  refine PreservesCokernel.iso (analytificationModules (projectiveSpace.{u} n)) φ ≪≫
    cokernelIsoOfEq hφ ≪≫ cokernelEpiComp _ _ ≪≫ ?_
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p₀))

/-- A composite of surjective module maps is surjective. -/
private lemma surjective_comp {R : Type u} [Ring R] {A B C : ModuleCat.{u} R} (f : A ⟶ B)
    (g : B ⟶ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (f ≫ g) :=
  hg.comp hf

/-- If a composite of module maps is surjective, so is the second map. -/
private lemma surjective_of_comp {R : Type u} [Ring R] {A B C : ModuleCat.{u} R} (f : A ⟶ B)
    (g : B ⟶ C) (h : Function.Surjective (f ≫ g)) : Function.Surjective g :=
  Function.Surjective.of_comp (g := f) h

/-- A sheaf of modules `M` on `ℙⁿ_an` is **algebraically generated at `y`** if there is a coherent
algebraic sheaf `F` on `ℙⁿ` and a morphism `F^an ⟶ M` which is surjective on the stalk at `y`. -/
def IsAlgGeneratedAt
    (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    (y : projectiveSpaceAn.{u} n) : Prop :=
  ∃ (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    (_ : F.IsCoherent) (f : (analytificationModules (projectiveSpace.{u} n)).obj F ⟶ M),
    Function.Surjective (((projectiveSpaceAn.{u} n).toLocallyRingedSpace.stalkFunctor y).map f)

/-- `𝒪^{Σ I}(m)^an ≅ ∐ₖ 𝒪^{I k}(m)^an` on `ℙⁿ`. -/
def analytificationTwistFreeSigmaIso {κ : Type u} (I : κ → Type u) (m : ℤ) :
    (analytificationModules (projectiveSpace.{u} n)).obj
        (ProjectiveSpace.twist (SheafOfModules.free (Σ k, I k)) m) ≅
      ∐ fun k ↦ (analytificationModules (projectiveSpace.{u} n)).obj
        (ProjectiveSpace.twist (SheafOfModules.free (I k)) m) :=
  (analytificationModules (projectiveSpace.{u} n)).mapIso
      ((ProjectiveSpace.twistFunctor n (ULift.{u} ℂ) m).mapIso
        (sigmaSigmaIso I (fun _ _ ↦ SheafOfModules.unit _)).symm ≪≫
      PreservesCoproduct.iso (ProjectiveSpace.twistFunctor n (ULift.{u} ℂ) m) _) ≪≫
    PreservesCoproduct.iso (analytificationModules (projectiveSpace.{u} n)) _

/-- **From local to global algebraic generation**: if a sheaf of finite type on `ℙⁿ_an` is
algebraically generated at every point, then it is a quotient of `(𝒪^J(-m))^an` for a finite `J`
and some `m`. Uses compactness of `ℙⁿ_an` and Serre's theorem A on `ℙⁿ`. -/
theorem exists_epi_of_forall_isAlgGeneratedAt
    (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    [M.IsFiniteType] (h : ∀ y, IsAlgGeneratedAt M y) :
    ∃ (m : ℕ) (J : Type u) (_ : Finite J)
      (p : (analytificationModules (projectiveSpace.{u} n)).obj
        (ProjectiveSpace.twist (SheafOfModules.free J) (-(m : ℤ))) ⟶ M), Epi p := by
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  choose F hF f hf using h
  choose U hyU hU using fun y ↦ LocallyRingedSpace.exists_nhds_surjective_stalk (f y) y (hf y)
  obtain ⟨t, ht⟩ := (isCompact_univ (X := projectiveSpaceAn.{u} n)).elim_finite_subcover
    (fun y ↦ (U y).carrier)
    (fun y ↦ (U y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, by exact hyU y⟩)
  choose m₀ hm₀ using fun y ↦
    @ProjectiveSpace.exists_epi_twist_free_isCoherent_kernel n (ULift.{u} ℂ) _ (F y) _ (hF y)
  let m : ℕ := t.sup m₀
  choose I hI π hπ _ _ using fun k : t ↦ hm₀ k.1 m (Finset.le_sup k.2)
  let g : ∀ k : t, (analytificationModules (projectiveSpace.{u} n)).obj
      (ProjectiveSpace.twist (SheafOfModules.free (I k)) (-(m : ℤ))) ⟶ M := fun k ↦
    (analytificationModules (projectiveSpace.{u} n)).map (π k) ≫ f k.1
  refine ⟨m, Σ k, I k, inferInstance,
    (analytificationTwistFreeSigmaIso I _).hom ≫ Sigma.desc g, ?_⟩
  refine LocallyRingedSpace.epi_of_forall_surjective_stalk _ fun w ↦ ?_
  obtain ⟨k, hk, hw⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  have hg : Function.Surjective
      (((projectiveSpaceAn.{u} n).toLocallyRingedSpace.stalkFunctor w).map (g ⟨k, hk⟩)) := by
    haveI : Epi (C := SheafOfModules.{u}
        (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) (π ⟨k, hk⟩) := hπ _
    haveI : Epi ((analytificationModules (projectiveSpace.{u} n)).map (π ⟨k, hk⟩)) :=
      (analytificationModules (projectiveSpace.{u} n)).map_epi _
    rw [Functor.map_comp]
    exact surjective_comp _ _ (LocallyRingedSpace.surjective_stalk_of_epi _ w) (hU k w hw)
  rw [Functor.map_comp]
  refine surjective_comp _ _ (LocallyRingedSpace.surjective_stalk_of_epi _ w) ?_
  rw [← Sigma.ι_desc g ⟨k, hk⟩, Functor.map_comp] at hg
  exact surjective_of_comp _ _ hg

/-- **GAGA-3 on `ℙⁿ` from local algebraic generation**: if every coherent analytic sheaf on
`ℙⁿ_an` is algebraically generated at every point, then every coherent analytic sheaf on `ℙⁿ_an`
is isomorphic to the analytification of a coherent algebraic sheaf. -/
theorem exists_iso_of_forall_isAlgGeneratedAt
    (h : ∀ M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf,
      M.IsCoherent → ∀ y, IsAlgGeneratedAt M y)
    (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    (hM : M.IsCoherent) :
    ∃ F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules (projectiveSpace.{u} n)).obj F ≅ M) := by
  refine exists_iso_of_forall_exists_epi (fun N hN ↦ ?_) M hM
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  haveI : IsLocallyNoetherian ℙₒ(n; ULift.{u} ℂ) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveSpace.toSpec n (ULift.{u} ℂ))
  haveI := hN
  obtain ⟨m, J, hJ, p, hp⟩ := exists_epi_of_forall_isAlgGeneratedAt N (h N hN)
  haveI := Scheme.isCoherent_free (X := ℙₒ(n; ULift.{u} ℂ)) J
  exact ⟨_, ProjectiveSpace.isCoherent_twist (SheafOfModules.free J : ℙₒ(n; ULift.{u} ℂ).Modules)
    (-(m : ℤ)), p, hp⟩

end ComplexAnalytic.projectiveSpaceAn

end
