/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Basic
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Criterion
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.LocallySurjective
public import Other.Oka.CategoryTheory.Limits.Shapes.KernelBiprod

/-!
# Stability properties of coherent sheaves of modules

We prove the basic stability results for coherent sheaves of modules on a small
site `(C, J)` where `C` has pullbacks:

- `SheafOfModules.IsCoherent.of_mono`: a finite type subsheaf of a coherent sheaf
  is coherent.
- `SheafOfModules.isFiniteType_kernel_of_isCoherent`: the kernel of a morphism from
  a finite type sheaf to a coherent sheaf is of finite type.
- `SheafOfModules.IsCoherent.image_of_isFiniteType`: the image of a morphism from a finite
  type sheaf to a coherent sheaf is coherent.
- `SheafOfModules.IsCoherent.cokernel`: the cokernel of a morphism from a finite type sheaf to
  a coherent sheaf is coherent; the third leg of two-out-of-three.
- `SheafOfModules.IsCoherent.biprod`: the biproduct of two coherent sheaves is coherent, given
  that it is of finite type.

We work over small sites since the sheafification and local bijectivity instances
for the involved sites (and their iterated slice sites) are then available; this
covers in particular sheaves on the site of opens of a topological space.

## References

- [Jean-Pierre Serre, *Faisceaux algébriques cohérents*][serre1955], §2
- https://stacks.math.columbia.edu/tag/01BY

-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- If `π` is an epimorphism, the square

```
F --π ≫ φ--> M
|            ‖
π            𝟙
v            v
N ----φ----> M
```

is a pushout square. -/
lemma CategoryTheory.IsPushout.of_epi_comp_id {A : Type*} [Category A] {F N M : A}
    (π : F ⟶ N) (φ : N ⟶ M) [Epi π] : IsPushout (π ≫ φ) π (𝟙 M) φ :=
  IsPushout.of_isColimit (c := PushoutCocone.mk (𝟙 M) φ (by simp)) <|
    PushoutCocone.IsColimit.mk _ (fun s ↦ s.inl)
      (fun s ↦ by simp)
      (fun s ↦ by rw [← cancel_epi π]; simpa using s.condition)
      (fun s m h₁ h₂ ↦ by simpa using h₁)

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

omit [HasPullbacks C] in
/-- A finite type subsheaf of a coherent sheaf of modules is coherent. -/
lemma IsCoherent.of_mono {N M : SheafOfModules.{u} R} (i : N ⟶ M) [Mono i]
    [N.IsFiniteType] [M.IsCoherent] : N.IsCoherent where
  isFiniteType := inferInstance
  hasFiniteTypeRelations X := by
    intro I _ φ
    haveI : Mono (i.over X) := inferInstance
    haveI : (kernel (φ ≫ i.over X)).IsFiniteType :=
      IsCoherent.isFiniteType_kernel (φ ≫ i.over X)
    exact IsFiniteType.of_iso (M := kernel (φ ≫ i.over X)) (kernelCompMono φ (i.over X))

/-- Auxiliary statement for `SheafOfModules.isFiniteType_kernel_of_isCoherent`: if the
restriction of `N` to `X` admits finitely many generating sections and `M` is coherent,
then the restriction of `kernel φ` to `X` is of finite type. -/
lemma isFiniteType_over_kernel_of_isCoherent {N M : SheafOfModules.{u} R} (φ : N ⟶ M)
    [M.IsCoherent] {X : C} (σ : (N.over X).GeneratingSections) [σ.IsFiniteType] :
    IsFiniteType (R := R.over X) ((kernel φ).over X) := by
  haveI : HasBinaryProducts (Over X) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : (kernel (σ.π ≫ φ.over X)).IsFiniteType :=
    IsCoherent.isFiniteType_kernel (σ.π ≫ φ.over X)
  let κ : kernel (σ.π ≫ φ.over X) ⟶ kernel (φ.over X) :=
    kernel.map (σ.π ≫ φ.over X) (φ.over X) σ.π (𝟙 _) (by simp)
  haveI : Epi κ :=
    Abelian.epi_kernel_map_of_isPushout (.of_epi_comp_id σ.π (φ.over X))
  haveI : (kernel (φ.over X)).IsFiniteType :=
    IsFiniteType.of_epi (N := kernel (φ.over X)) κ
  exact IsFiniteType.of_iso (M := kernel (φ.over X)) (overKernelIso φ X).symm

/-- The kernel of a morphism from a finite type sheaf of modules to a coherent sheaf
of modules is of finite type. -/
lemma isFiniteType_kernel_of_isCoherent {N M : SheafOfModules.{u} R} (φ : N ⟶ M)
    [N.IsFiniteType] [M.IsCoherent] : (kernel φ).IsFiniteType := by
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData N
  haveI (i : σ.I) : IsFiniteType (R := R.over (σ.X i)) ((kernel φ).over (σ.X i)) :=
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i
    isFiniteType_over_kernel_of_isCoherent φ (σ.generators i)
  exact IsFiniteType.of_coversTop (kernel φ) σ.X σ.coversTop

/-- The kernel of a morphism of coherent sheaves of modules is coherent. -/
lemma IsCoherent.kernel {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [M.IsCoherent] [N.IsCoherent] : (Limits.kernel φ).IsCoherent :=
  haveI : (Limits.kernel φ).IsFiniteType := isFiniteType_kernel_of_isCoherent φ
  .of_mono (Limits.kernel.ι φ)

omit [HasPullbacks C] in
/-- The cokernel of a morphism into a finite type sheaf of modules is of finite type. -/
lemma isFiniteType_cokernel [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [N.IsFiniteType] : (cokernel φ).IsFiniteType :=
  IsFiniteType.of_epi (N := cokernel φ) (cokernel.π φ)

omit [HasPullbacks C] in
/-- The image of a morphism from a finite type sheaf of modules to a coherent sheaf of modules
is coherent.

Only the *source* being of finite type is used: the image is a quotient of the source, hence of
finite type, and a finite type subsheaf of a coherent sheaf is coherent. This is the form needed
to see that the ideal sheaf generated by finitely many sections is coherent, where the source is
a finite free sheaf and no coherence of it is available. -/
lemma IsCoherent.image_of_isFiniteType [HasBinaryProducts C] {M N : SheafOfModules.{u} R}
    (φ : M ⟶ N) [M.IsFiniteType] [N.IsCoherent] : (Abelian.image φ).IsCoherent :=
  haveI : (Abelian.image φ).IsFiniteType :=
    IsFiniteType.of_epi (N := Abelian.image φ) (Abelian.factorThruImage φ)
  .of_mono (Abelian.image.ι φ)

omit [HasPullbacks C] in
/-- The image of a morphism of coherent sheaves of modules is coherent. -/
lemma IsCoherent.image [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [M.IsCoherent] [N.IsCoherent] : (Abelian.image φ).IsCoherent :=
  .image_of_isFiniteType φ

section Cokernel

variable [HasBinaryProducts C]

/-- **The sheaf of relations between finitely many sections of a quotient is of finite type.**

This is the whole content of `SheafOfModules.IsCoherent.cokernel`, and unlike the kernel and
image cases it cannot be got by transporting coherence along a mono or an epi.

Write `Q` for `cokernel φ` and `p : N ⟶ Q` for the projection, and form the pullback
`P := free I ×_Q N` of `ψ` along `p`. Its two projections have, by
`CategoryTheory.Limits.isIso_kernel_map_of_isPullback` applied to the square and to its flip,
the same kernels as the maps they are base changes of: `kernel (fst) ≅ kernel p =
Abelian.image φ`, which is of finite type because `M` is and `N` is coherent, and
`kernel (snd) ≅ kernel ψ`, which is what we are after. Since `p` is an epimorphism so is `fst`,
so `P` is an extension of `free I` by a sheaf of finite type and therefore of finite type
(`SheafOfModules.IsFiniteType.of_epi_free`; this is where local surjectivity of an
epimorphism enters). Finally `snd` maps the finite type sheaf `P` into the coherent sheaf `N`,
so its kernel is of finite type. -/
lemma isFiniteType_kernel_free_to_cokernel {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [M.IsFiniteType] [N.IsCoherent] {I : Type u} [Finite I]
    (ψ : free (R := R) I ⟶ Limits.cokernel φ) : (Limits.kernel ψ).IsFiniteType := by
  have sq : IsPullback (pullback.fst ψ (cokernel.π φ)) (pullback.snd ψ (cokernel.π φ)) ψ
      (cokernel.π φ) := IsPullback.of_hasPullback _ _
  haveI : Epi (pullback.fst ψ (cokernel.π φ)) := Abelian.epi_pullback_of_epi_g _ _
  haveI : (Abelian.image φ).IsCoherent := IsCoherent.image_of_isFiniteType φ
  haveI := isIso_kernel_map_of_isPullback sq
  haveI : (kernel (pullback.fst ψ (cokernel.π φ))).IsFiniteType :=
    IsFiniteType.of_iso (M := kernel (cokernel.π φ)) (asIso (kernel.map _ _ _ _ sq.w)).symm
  haveI : (Limits.pullback ψ (cokernel.π φ)).IsFiniteType :=
    IsFiniteType.of_epi_free (pullback.fst ψ (cokernel.π φ))
  haveI : (kernel (pullback.snd ψ (cokernel.π φ))).IsFiniteType :=
    isFiniteType_kernel_of_isCoherent (pullback.snd ψ (cokernel.π φ))
  haveI := isIso_kernel_map_of_isPullback sq.flip
  exact IsFiniteType.of_iso (M := kernel (pullback.snd ψ (cokernel.π φ)))
    (asIso (kernel.map _ _ _ _ sq.flip.w))

/-- **The cokernel of a morphism from a finite type sheaf of modules to a coherent sheaf of
modules is coherent.**

With `SheafOfModules.IsCoherent.kernel` and `SheafOfModules.IsCoherent.image` this completes
two-out-of-three for coherence. Only the *source* being of finite type is needed, which is what
the application to ideal sheaves requires: there the source is a finite free sheaf, of which no
coherence is available a priori. The apparently stronger statement with `[M.IsCoherent]` is the
same theorem, since `cokernel φ ≅ cokernel (Abelian.image.ι φ)`. -/
lemma IsCoherent.cokernel {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [M.IsFiniteType] [N.IsCoherent] : (Limits.cokernel φ).IsCoherent where
  isFiniteType := isFiniteType_cokernel φ
  hasFiniteTypeRelations X := by
    intro I _ ψ
    haveI : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
    haveI : (M.over X).IsFiniteType := IsFiniteType.over M X
    haveI : (N.over X).IsCoherent := IsCoherent.over N X
    -- `kernel` alone resolves to `SheafOfModules.IsCoherent.kernel` here: declaring a lemma
    -- named `IsCoherent.cokernel` opens `SheafOfModules.IsCoherent` in its own body.
    haveI : (Limits.kernel (ψ ≫ (PreservesCokernel.iso (overFunctor R X) φ).hom)).IsFiniteType :=
      isFiniteType_kernel_free_to_cokernel (M := M.over X) (N := N.over X) (φ.over X)
        (ψ ≫ (PreservesCokernel.iso (overFunctor R X) φ).hom)
    exact IsFiniteType.of_iso
      (M := Limits.kernel (ψ ≫ (PreservesCokernel.iso (overFunctor R X) φ).hom))
      (kernelCompMono ψ (PreservesCokernel.iso (overFunctor R X) φ).hom)

end Cokernel

section Biprod

variable [HasBinaryProducts C]

/-- **The relations between finitely many sections of a biproduct of coherent sheaves of modules
are of finite type.**

This is the whole content of `SheafOfModules.IsCoherent.biprod`. A morphism `φ : free I ⟶ A ⊞ B`
is the pair of its two components `p` and `q`, and its kernel is `ker p ∩ ker q`. That
intersection is not the kernel of anything with a single target, but it *is* an iterated kernel
; `CategoryTheory.Limits.kernelBiprodLiftIso`; so
`SheafOfModules.isFiniteType_kernel_of_isCoherent` applies to it twice: once to `q`, whose target
`B` is coherent and whose source `free I` is of finite type, and then to the restriction of `p`
to `ker q`, whose target `A` is coherent and whose source is of finite type by the first step.

Restriction to `Over X` is dealt with as in `SheafOfModules.IsCoherent.cokernel`: coherence
restricts (`SheafOfModules.IsCoherent.over`) and restriction commutes with the biproduct
(`SheafOfModules.overBiprodIso`), which is where the biproduct rather than the product is
convenient. -/
lemma hasFiniteTypeRelations_biprod {A B : SheafOfModules.{u} R} [A.IsCoherent] [B.IsCoherent]
    (X : C) : (A ⊞ B).HasFiniteTypeRelations X := by
  intro I _ φ
  haveI : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : (A.over X).IsCoherent := IsCoherent.over A X
  haveI : (B.over X).IsCoherent := IsCoherent.over B X
  haveI : (free (R := R.over X) I).IsFiniteType := isFiniteType_free I
  have key : φ ≫ (overBiprodIso A B X).hom =
      Limits.biprod.lift (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.fst)
        (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.snd) :=
    Limits.biprod.hom_ext _ _ (by simp) (by simp)
  haveI : (kernel (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.snd)).IsFiniteType :=
    isFiniteType_kernel_of_isCoherent _
  haveI : (kernel (kernel.ι (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.snd) ≫
      (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.fst))).IsFiniteType :=
    isFiniteType_kernel_of_isCoherent _
  haveI : (kernel (Limits.biprod.lift (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.fst)
      (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.snd))).IsFiniteType :=
    IsFiniteType.of_iso
      (M := kernel (kernel.ι (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.snd) ≫
        (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.fst)))
      (kernelBiprodLiftIso _ _)
  haveI : (kernel (φ ≫ (overBiprodIso A B X).hom)).IsFiniteType :=
    IsFiniteType.of_iso
      (M := kernel (Limits.biprod.lift (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.fst)
        (φ ≫ (overBiprodIso A B X).hom ≫ Limits.biprod.snd)))
      (kernelIsoOfEq key).symm
  exact IsFiniteType.of_iso (M := kernel (φ ≫ (overBiprodIso A B X).hom))
    (kernelCompMono φ (overBiprodIso A B X).hom)

/-- **The biproduct of two coherent sheaves of modules is coherent**, given that it is of finite
type.

The finite type hypothesis is not removable with what is available here, and that is not an
oversight: `A` and `B` are each generated by finitely many sections on *their own* cover, and
producing a single cover on which both are would need a refinement of two coverings, which the
`CoversTop` API in this development does not provide. Every consumer has the hypothesis for free
; `SheafOfModules.isFiniteType_free` for a biproduct of frees,
`SheafOfModules.isFiniteType_free_biprod` when one factor is free, and
`SheafOfModules.IsFiniteType.of_iso` whenever the biproduct is being recognised as something
already known to be of finite type. -/
lemma IsCoherent.biprod {A B : SheafOfModules.{u} R} [A.IsCoherent] [B.IsCoherent]
    [(A ⊞ B).IsFiniteType] : (A ⊞ B).IsCoherent where
  isFiniteType := inferInstance
  hasFiniteTypeRelations X := hasFiniteTypeRelations_biprod X

end Biprod

end SheafOfModules
