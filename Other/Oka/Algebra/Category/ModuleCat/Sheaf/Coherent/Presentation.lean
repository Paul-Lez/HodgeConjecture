/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# A coherent sheaf of modules is locally finitely presented

`SheafOfModules.IsCoherent` says that `M` is of finite type and that every finite family of
sections of `M` over every object has a sheaf of relations which is again of finite type.
`SheafOfModules.IsFinitePresentation` ; Mathlib's ; says that `M` is, on a covering of the
terminal object, the cokernel of a morphism between finite free sheaves. This file proves the
implication:

`SheafOfModules.IsCoherent.isFinitePresentation`: **a coherent sheaf of modules is of finite
presentation**, hence quasicoherent.

## Why this is the missing link and not a restatement

The two conditions differ in *where the finiteness is asserted*. Coherence gives generators of
`M` on a cover, and then relations of those generators on a **further** cover, because
`SheafOfModules.IsFiniteType` of the kernel is itself a local statement. A
`SheafOfModules.Presentation` is global: one family of generators and one family of relations,
both over the same object. So the content is the refinement of the cover ; pass from the
`X i` on which `M` is generated to the objects on which the relations are generated too ; and
nothing else. There is no local-to-global step and no hypothesis on the site beyond the ones
`SheafOfModules.IsCoherent.of_coversTop` already needs.

`CategoryTheory.GrothendieckTopology.CoversTop.over` is the transitivity that makes the refined
family a cover, and `SheafOfModules.QuasicoherentData.bind` is Mathlib's assembly of the
presentations over it; the finiteness that assembly preserves is
`SheafOfModules.QuasicoherentData.isFinitePresentation_bind`, in the mirror tree.

## The consequence this exists for

On `Spec R` Mathlib's `AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ` turns
quasicoherence into `M ≅ (Γ M)^~`, so a coherent sheaf on an affine scheme is the sheaf
associated with its own global sections. That is the affine dictionary, and this file is the half
of it that is about coherence rather than about `Spec`.

## Main definitions

- `SheafOfModules.GeneratingSections.presentationOver`: **generators of `N`, together with
  generators of their relations over `Y`, present `N.over Y`.**
- `SheafOfModules.GeneratingSections.quasicoherentDataOver`: the same over a whole cover.

## Main results

- `SheafOfModules.IsCoherent.isFinitePresentation`
- `SheafOfModules.IsCoherent.isQuasicoherent`
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {N : SheafOfModules.{u} R}

/-- **The relations of the restricted generating sections are the restriction of the
relations.**

`SheafOfModules.GeneratingSections.map_π_eq` writes the structure morphism of the restricted
generators as an isomorphism of free sheaves followed by the restriction of the original one, so
its kernel is the kernel of that restriction, which is the restriction of the kernel because
restriction preserves kernels (`SheafOfModules.overKernelIso`). Stated because it is what lets
generators of the relations *over `Y`* be read as relations of the restricted generators, which
is the whole of `SheafOfModules.GeneratingSections.presentationOver`. -/
noncomputable def GeneratingSections.overKernelπIso (G : N.GeneratingSections) (Y : C) :
    (kernel G.π).over Y ≅ kernel ((G.map (overFunctor R Y) (Iso.refl _)).π) :=
  overKernelIso G.π Y ≪≫ (kernelIsIsoComp _ _).symm ≪≫
    (kernelIsoOfEq (G.map_π_eq (overFunctor R Y) (Iso.refl _))).symm

/-- **Generators of `N`, together with generators of their relations over `Y`, present
`N.over Y`.**

This is the shape coherence produces and a `SheafOfModules.Presentation` consumes: the
generators come from an object on which `N` is generated, the relations from an object below it
on which the sheaf of relations is generated in turn, and the presentation lives on the lower
one. -/
noncomputable def GeneratingSections.presentationOver (G : N.GeneratingSections) (Y : C)
    (H : ((kernel G.π).over Y).GeneratingSections) : (N.over Y).Presentation where
  generators := G.map (overFunctor R Y) (Iso.refl _)
  relations := H.ofEpi (G.overKernelπIso Y).hom

instance GeneratingSections.isFinite_presentationOver (G : N.GeneratingSections) [G.IsFiniteType]
    (Y : C) (H : ((kernel G.π).over Y).GeneratingSections) [H.IsFiniteType] :
    (G.presentationOver Y H).IsFinite where
  isFiniteType_generators := inferInstanceAs (G.map (overFunctor R Y) (Iso.refl _)).IsFiniteType
  isFiniteType_relations := inferInstanceAs (H.ofEpi (G.overKernelπIso Y).hom).IsFiniteType

/-- **Generators of `N` and a covering on which their relations are generated give quasicoherent
data of `N`**, one presentation over each member of that covering. -/
noncomputable def GeneratingSections.quasicoherentDataOver (G : N.GeneratingSections)
    (τ : (kernel G.π).LocalGeneratorsData.{u}) : N.QuasicoherentData where
  I := τ.I
  X := τ.X
  coversTop := τ.coversTop
  presentation k := G.presentationOver (τ.X k) (τ.generators k)

instance GeneratingSections.isFinitePresentation_quasicoherentDataOver
    (G : N.GeneratingSections) [G.IsFiniteType] (τ : (kernel G.π).LocalGeneratorsData.{u})
    [τ.IsFiniteType] : (G.quasicoherentDataOver τ).IsFinitePresentation where
  isFinite_presentation k := by
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := τ) k
    exact inferInstanceAs (G.presentationOver (τ.X k) (τ.generators k)).IsFinite

omit [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A coherent sheaf of modules is of finite presentation.**

Finite type gives a covering `σ.X` and finitely many generators of `M` over each member;
coherence gives that the kernel of those generators is again of finite type, so it is generated
over a covering `τ i` of `σ.X i` by finitely many sections; and over `(τ i).X k` both families
are present at once, which is a finite presentation. The two coverings are composed by
`CategoryTheory.GrothendieckTopology.CoversTop.over` inside
`SheafOfModules.QuasicoherentData.bind`.

Not an instance: `SheafOfModules.IsCoherent` is not a class instance search should be running
from, and Mathlib already turns `SheafOfModules.IsFinitePresentation` into
`SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`. -/
theorem IsCoherent.isFinitePresentation (M : SheafOfModules.{u} R) [M.IsCoherent] :
    M.IsFinitePresentation where
  exists_quasicoherentData := by
    obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData.{u, u} M
    haveI (i : σ.I) : (σ.generators i).IsFiniteType := hσ.isFiniteType i
    haveI (i : σ.I) : (kernel (σ.generators i).π).IsFiniteType :=
      IsCoherent.isFiniteType_kernel_π (σ.generators i)
    choose τ hτ using fun i : σ.I ↦
      IsFiniteType.exists_localGeneratorsData.{u, u} (kernel (σ.generators i).π)
    haveI (i : σ.I) := hτ i
    haveI (i : σ.I) : HasBinaryProducts (Over (σ.X i)) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    exact ⟨QuasicoherentData.bind M σ.X σ.coversTop
      (fun i ↦ (σ.generators i).quasicoherentDataOver (τ i)), inferInstance⟩

omit [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A coherent sheaf of modules is quasicoherent.** -/
theorem IsCoherent.isQuasicoherent (M : SheafOfModules.{u} R) [M.IsCoherent] :
    M.IsQuasicoherent :=
  haveI := IsCoherent.isFinitePresentation M
  inferInstance

end SheafOfModules
