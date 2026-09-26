/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Free
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Generators
public import Other.Oka.CategoryTheory.Abelian.Basic
public import Other.Oka.CategoryTheory.Sites.CoversTop.Basic
public import Other.Oka.Algebra.Category.Grp.Sheaf.LocallySurjective

/-!
# An epimorphism of sheaves of modules is locally surjective

An epimorphism of sheaves is not surjective on sections; it is only *locally* surjective, and
that is the form in which it is used. Mathlib proves the equivalence for sheaves of types
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`) and, given a functorial
surjective–injective factorisation, for sheaves valued in a concrete category
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`). Neither applies to `SheafOfModules R`,
which is not a category of the form `Sheaf J A`.

The bridge is `Other/Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean`: `SheafOfModules.toSheaf R`
preserves epimorphisms, so an epimorphism of sheaves of modules becomes an epimorphism of
sheaves of abelian groups, where
`CategoryTheory.Sheaf.isLocallySurjective_of_epi_addCommGrp` applies.

**The import block is not in alphabetical order and must not be sorted.**
`Other.Oka.Algebra.Category.Grp.Sheaf.LocallySurjective` is last deliberately: with it first,
`SheafOfModules.exists_free_app_eq_of_epi` below fails to elaborate with
`failed to solve universe constraint max u' v' =?= u`, which names nothing that would lead a
reader back to the import block. Measured by moving the single line and rebuilding, in both
directions.

## The section-level form

`SheafOfModules.exists_app_eq_of_epi` is the statement a caller wants, and it is deliberately
phrased in the same shape as `SheafOfModules.LocallyGeneratesKernel`
(`Other/Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Criterion.lean`): a covering sieve `S ∈ J Z`
such that every arrow of `S` restricts the given section into the image. Together with
`SheafOfModules.exists_forall_app_eq_of_epi`, which does the same for a finite family of
sections at once by intersecting the sieves, this is what is needed to lift a map out of a
finite free sheaf along an epimorphism, locally: that last statement is
`SheafOfModules.exists_free_app_eq_of_epi`, which says that on a covering sieve *every* section
in the image of `ψ : free L ⟶ N` is in the image of the epimorphism, not merely the images of
the `L` generators. It is stated on sections rather than as a factorisation `free L ⟶ M` of
sheaves, because a factorisation would have to be a morphism over each `W` of the sieve and so
would drag in the over-site restriction of `free L`; the consumers; `LocallyGeneratesKernel`
and its users; work with sections throughout.

## Main results

- `SheafOfModules.isLocallySurjective_toSheaf_map_iff_epi`
- `SheafOfModules.isLocallySurjective_toSheaf_map_of_epi`
- `SheafOfModules.exists_app_eq_of_epi`
- `SheafOfModules.exists_forall_app_eq_of_epi`
- `SheafOfModules.exists_free_app_eq_of_epi`
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits Opposite

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {M N : SheafOfModules.{v} R}

/-- **A morphism of sheaves of modules is an epimorphism exactly when the underlying morphism of
sheaves of abelian groups is locally surjective.**

The direction that is not formal is `epi → locally surjective`; it rests on
`SheafOfModules.preservesEpimorphisms_toSheaf`. The converse is Mathlib's
`CategoryTheory.Sheaf.epi_of_isLocallySurjective` followed by the reflection of epimorphisms
along the faithful functor `SheafOfModules.toSheaf R`. -/
theorem isLocallySurjective_toSheaf_map_iff_epi (f : M ⟶ N) :
    Sheaf.IsLocallySurjective ((toSheaf R).map f) ↔ Epi f := by
  refine ⟨fun _ ↦ (toSheaf R).epi_of_epi_map ?_, fun _ ↦ ?_⟩
  · exact Sheaf.epi_of_isLocallySurjective _
  · exact Sheaf.isLocallySurjective_of_epi_addCommGrp ((toSheaf R).map f)

/-- The underlying morphism of sheaves of abelian groups of an epimorphism of sheaves of
modules is locally surjective. -/
theorem isLocallySurjective_toSheaf_map_of_epi (f : M ⟶ N) [Epi f] :
    Sheaf.IsLocallySurjective ((toSheaf R).map f) :=
  (isLocallySurjective_toSheaf_map_iff_epi f).2 ‹_›

/-- **A section of the target of an epimorphism of sheaves of modules lifts on a covering
sieve.**

This is `SheafOfModules.isLocallySurjective_toSheaf_map_of_epi` read on sections, in the shape
`SheafOfModules.LocallyGeneratesKernel` uses. -/
theorem exists_app_eq_of_epi (f : M ⟶ N) [Epi f] (Z : C) (b : N.val.obj (op Z)) :
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃W : C⦄ (g : W ⟶ Z), S g →
      ∃ a, f.val.app (op W) a = N.val.map g.op b := by
  have := isLocallySurjective_toSheaf_map_of_epi f
  exact ⟨Presheaf.imageSieve ((toSheaf R).map f).hom b,
    Presheaf.imageSieve_mem J ((toSheaf R).map f).hom b, fun _ _ hg ↦ hg⟩

/-- A *finite family* of sections of the target of an epimorphism of sheaves of modules lifts
on a single covering sieve: intersect the finitely many sieves given by
`SheafOfModules.exists_app_eq_of_epi`.

This is the form every caller wants, because what has to be lifted along an epimorphism is
usually a morphism out of a finite free sheaf, i.e. finitely many sections at once. -/
theorem exists_forall_app_eq_of_epi {I : Type*} [Finite I] (f : M ⟶ N) [Epi f] (Z : C)
    (b : I → N.val.obj (op Z)) :
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃W : C⦄ (g : W ⟶ Z), S g →
      ∀ i, ∃ a, f.val.app (op W) a = N.val.map g.op (b i) := by
  classical
  cases nonempty_fintype I
  have := isLocallySurjective_toSheaf_map_of_epi f
  let T : I → J.Cover Z := fun i ↦
    ⟨Presheaf.imageSieve ((toSheaf R).map f).hom (b i),
      Presheaf.imageSieve_mem J ((toSheaf R).map f).hom (b i)⟩
  refine ⟨(Finset.univ.inf T : J.Cover Z).1, (Finset.univ.inf T : J.Cover Z).2,
    fun W g hg i ↦ ?_⟩
  have hle : (Finset.univ.inf T : J.Cover Z) ≤ T i := Finset.inf_le (Finset.mem_univ i)
  exact hle g hg

section Free

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- **A morphism out of a finite free sheaf of modules lifts along an epimorphism on a covering
sieve.**

Over each object of the sieve, *every* section of `free L` is sent by `ψ` into the image of `f`,
not merely the `L` generators: the generators lift by
`SheafOfModules.exists_forall_app_eq_of_epi`, and an arbitrary section is an `R`-linear
combination of them by `SheafOfModules.val_app_eq_sum`. -/
theorem exists_free_app_eq_of_epi {L : Type u} [Finite L] (f : M ⟶ N) [Epi f]
    (ψ : free (R := R) L ⟶ N) (Z : C) :
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃W : C⦄ (g : W ⟶ Z), S g →
      ∀ c : (free (R := R) L).val.obj (op W),
        ∃ a, f.val.app (op W) a = ψ.val.app (op W) c := by
  classical
  cases nonempty_fintype L
  obtain ⟨S, hS, hlift⟩ := exists_forall_app_eq_of_epi f Z
    (fun l ↦ PresheafOfModules.sections.eval (N.freeHomEquiv ψ l) (op Z))
  refine ⟨S, hS, fun W g hg c ↦ ?_⟩
  choose a ha using hlift g hg
  refine ⟨∑ l : L, freeEval (op W) c l • a l, ?_⟩
  rw [map_sum, val_app_eq_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_smul, ha l, PresheafOfModules.sections_property]

end Free

section Extension

variable {C : Type u} [SmallCategory C] [HasPullbacks C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Auxiliary statement for `SheafOfModules.IsFiniteType.of_epi_free`: over an object on which
`π` is surjective on sections, the source is of finite type. -/
lemma isFiniteType_over_of_surjective_val_app {P : SheafOfModules.{u} R} {I : Type u} [Finite I]
    (π : P ⟶ free (R := R) I) [Epi π] [(kernel π).IsFiniteType] {W : C}
    (hsurj : Function.Surjective ((π.over W).val.app (op (Over.mk (𝟙 W))))) :
    IsFiniteType (R := R.over W) (P.over W) := by
  haveI : HasBinaryProducts (Over W) := Over.ConstructProducts.over_binaryProduct_of_pullback
  have hT : IsTerminal (Over.mk (𝟙 W)) := Over.mkIdTerminal
  choose a ha using fun i ↦ hsurj (PresheafOfModules.sections.eval
    (((free (R := R) I).over W).freeHomEquiv (overFreeIso I W).hom i) (op (Over.mk (𝟙 W))))
  have huv : (P.over W).freeHomEquiv.symm (fun i ↦ sectionOfTerminal hT (P.over W) (a i)) ≫
      π.over W = (overFreeIso I W).hom := by
    rw [freeHomEquiv_symm_comp]
    refine Equiv.symm_apply_eq _ |>.2 ?_
    funext i
    rw [sectionsMap_sectionOfTerminal hT (π.over W) (a i), ha i, sectionOfTerminal_eval]
  haveI : Epi ((P.over W).freeHomEquiv.symm
      (fun i ↦ sectionOfTerminal hT (P.over W) (a i)) ≫ π.over W) := by
    rw [huv]; infer_instance
  haveI : IsFiniteType (R := R.over W) ((kernel π).over W) := IsFiniteType.over (kernel π) W
  haveI : IsFiniteType (R := R.over W) (kernel (π.over W)) :=
    IsFiniteType.of_iso (M := (kernel π).over W) (overKernelIso π W)
  haveI : IsFiniteType (R := R.over W) ((free (R := R.over W) I) ⊞ kernel (π.over W)) :=
    isFiniteType_free_biprod _
  haveI := Abelian.epi_biprod_desc_kernel_ι (π.over W)
    ((P.over W).freeHomEquiv.symm (fun i ↦ sectionOfTerminal hT (P.over W) (a i))) ‹_›
  exact IsFiniteType.of_epi (N := P.over W) (biprod.desc
    ((P.over W).freeHomEquiv.symm (fun i ↦ sectionOfTerminal hT (P.over W) (a i)))
    (kernel.ι (π.over W)))

/-- **An extension of a finite free sheaf of modules by a sheaf of finite type is of finite
type.**

This is the one place where local surjectivity of an epimorphism is genuinely needed: a free
sheaf is not projective, so the tautological sections of `free I` lift along `π` only on a
cover. On each member of that cover the lift and the kernel jointly generate
(`CategoryTheory.Abelian.epi_biprod_desc_kernel_ι`), and being of finite type is local. -/
lemma IsFiniteType.of_epi_free {P : SheafOfModules.{u} R} {I : Type u} [Finite I]
    (π : P ⟶ free (R := R) I) [Epi π] [(kernel π).IsFiniteType] : P.IsFiniteType := by
  choose S hS hlift using fun Z ↦ exists_free_app_eq_of_epi π (𝟙 (free (R := R) I)) Z
  refine IsFiniteType.of_coversTop_of_forall P _
    (GrothendieckTopology.coversTop_of_sieves J S hS) (fun t ↦ ?_)
  obtain ⟨Z, W, g, hg⟩ := t
  exact isFiniteType_over_of_surjective_val_app π (fun c ↦ hlift Z g hg c)

end Extension

end SheafOfModules
