/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.TildeExact
public import Other.Oka.AlgebraicGeometry.Modules.Coherent
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwist
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerreMorphism
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.RestrictModulesOver

/-!
# Coherence of quasi-coherent sheaves with finite sections

Let `X` be a locally noetherian scheme and `M` a quasi-coherent `𝒪_X`-module. If every point of
`X` has an affine open neighbourhood `V` such that `Γ(V, M)` is a finite `Γ(X, V)`-module, then
`M` is coherent (`AlgebraicGeometry.Scheme.Modules.isCoherent_of_module_finite`).

On `Spec R` with `R` noetherian, a quasi-coherent sheaf with finite global sections has finitely
presented global sections, hence a finite global presentation, hence is the cokernel of a
morphism between finite free sheaves
(`AlgebraicGeometry.Scheme.Modules.isCoherent_of_module_finite_moduleSpecΓFunctor_obj`). The
general case follows by restricting to affine opens.

We also show that twisting by a cocycle on an open cover preserves coherence
(`AlgebraicGeometry.Scheme.Modules.isCoherent_twist`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules

/-- On `Spec R` with `R` noetherian, a quasi-coherent sheaf whose global sections form a finite
`R`-module is coherent. -/
theorem isCoherent_of_module_finite_moduleSpecΓFunctor_obj {R : CommRingCat.{u}}
    [IsNoetherianRing R] (N : (Spec R).Modules) [N.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj N : Type u)] : N.IsCoherent := by
  haveI : Module.FinitePresentation R (moduleSpecΓFunctor.obj N : Type u) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨P, hP⟩ := exists_isFinite_presentation N
  haveI : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  haveI : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  haveI := (Spec R).isCoherent_free P.generators.I
  haveI := (Spec R).isCoherent_free P.relations.I
  let f := (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π
  haveI : (cokernel f).IsCoherent := SheafOfModules.IsCoherent.cokernel f
  exact SheafOfModules.IsCoherent.of_iso.{u} (M := cokernel f)
    ((cokernelIsCokernel f).coconePointUniqueUpToIso P.isColimit)

/-- On a noetherian affine scheme `V`, a quasi-coherent sheaf whose global sections form a finite
`Γ(V, ⊤)`-module is coherent. -/
theorem isCoherent_of_isAffine_of_module_finite {V : Scheme.{u}} [IsAffine V]
    [IsLocallyNoetherian V] (N : V.Modules) [N.IsQuasicoherent]
    [Module.Finite Γ(V, ⊤) Γ(N, ⊤)] : N.IsCoherent := by
  haveI : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  have he : (V.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(V, ⊤)).Opens) : V.Opens) = ⊤ := by simp
  haveI : Module.Finite Γ(V, V.isoSpec.inv ''ᵁ ⊤) Γ(N, V.isoSpec.inv ''ᵁ ⊤) := by
    rw [he]
    infer_instance
  haveI h₁ : Module.Finite Γ(Spec Γ(V, ⊤), ⊤) Γ(N.restrict V.isoSpec.inv, ⊤) :=
    module_finite_restrict_sections V.isoSpec.inv N ⊤
  letI : Module Γ(V, ⊤) Γ(N.restrict V.isoSpec.inv, ⊤) :=
    inferInstanceAs
      (Module Γ(V, ⊤) (moduleSpecΓFunctor.obj (N.restrict V.isoSpec.inv) : Type u))
  haveI : Module.Finite Γ(V, ⊤) Γ(N.restrict V.isoSpec.inv, ⊤) :=
    Module.Finite.of_ringEquiv (Scheme.ΓSpecIso Γ(V, ⊤)).commRingCatIsoToRingEquiv
      fun s m ↦ by
        have h : ∀ r : Γ(V, ⊤), ((Scheme.ΓSpecIso Γ(V, ⊤)).inv r) • m = r • m := fun _ ↦ rfl
        have := h ((Scheme.ΓSpecIso Γ(V, ⊤)).hom s)
        rwa [Iso.hom_inv_id_apply] at this
  haveI : Module.Finite Γ(V, ⊤)
      (moduleSpecΓFunctor.obj (N.restrict V.isoSpec.inv) : Type u) := ‹_›
  haveI : (N.restrict V.isoSpec.inv).IsCoherent :=
    isCoherent_of_module_finite_moduleSpecΓFunctor_obj _
  haveI := isCoherent_restrict V.isoSpec.hom (N.restrict V.isoSpec.inv)
  exact SheafOfModules.IsCoherent.of_iso.{u}
    (M := (N.restrict V.isoSpec.inv).restrict V.isoSpec.hom)
    ((restrictFunctorEquivOfIso V.isoSpec.symm).unitIso.app N).symm

/-- **Coherence is local**: if every point of `X` has an open neighbourhood `V` such that the
restriction of `M` to `V` is coherent, then `M` is coherent. -/
theorem isCoherent_of_isCoherent_restrict {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ (M.restrict V.ι).IsCoherent) : M.IsCoherent := by
  haveI : SheafOfModules.IsCoherent (R := X.toLocallyRingedSpace.ringSheaf) M :=
    LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules _ M fun x ↦ by
      obtain ⟨V, hxV, hV⟩ := h x
      refine ⟨V, hxV, ?_⟩
      haveI : SheafOfModules.IsCoherent (R := V.toScheme.toLocallyRingedSpace.ringSheaf)
        (M.restrict V.ι) := hV
      exact SheafOfModules.IsCoherent.of_iso.{u} (M := M.restrict V.ι)
        ((restrictFunctorIsoPullbackModules V.ι).app M)
  exact ‹_›

/-- **Quasi-coherent sheaves with finite sections are coherent.** Let `X` be locally noetherian
and `M` quasi-coherent. If every point of `X` has an affine open neighbourhood `V` such that
`Γ(V, M)` is a finite `Γ(X, V)`-module, then `M` is coherent. -/
theorem isCoherent_of_module_finite {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules)
    [M.IsQuasicoherent]
    (h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Module.Finite Γ(X, V) Γ(M, V)) :
    M.IsCoherent := by
  refine isCoherent_of_isCoherent_restrict M fun x ↦ ?_
  obtain ⟨V, hV, hx, hfin⟩ := h x
  refine ⟨V, hx, ?_⟩
  haveI : IsAffine V := hV
  haveI : Module.Finite Γ(X, V.ι ''ᵁ ⊤) Γ(M, V.ι ''ᵁ ⊤) := V.ι_image_top.symm ▸ hfin
  haveI := module_finite_restrict_sections V.ι M ⊤
  exact isCoherent_of_isAffine_of_module_finite _

section Twist

variable {X : Scheme.{u}} {ι : Type} {U : ι → X.Opens}

/-- **Twisting preserves coherence**, for a cocycle on an open cover of a locally noetherian
scheme. -/
theorem isCoherent_twist [IsLocallyNoetherian X] (hU : ⨆ i, U i = ⊤) (F : X.Modules)
    [F.IsCoherent] (c : Cocycle U) : (twist F c).IsCoherent := by
  refine isCoherent_of_isCoherent_restrict _ fun x ↦ ?_
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  refine ⟨U i, hi, ?_⟩
  haveI := isCoherent_restrict (U i).ι F
  exact SheafOfModules.IsCoherent.of_iso.{u} (twistRestrictIso F c i).symm

end Twist

end AlgebraicGeometry.Scheme.Modules

end
