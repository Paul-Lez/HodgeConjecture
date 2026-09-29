/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Cohomology
public import Other.Oka.Topology.Sheaves.Cohomology.OpenEmbedding

/-!
# Cohomology of the structure sheaf along open immersions

For an open immersion `f : Y ⟶ X` of locally ringed spaces the restriction of the structure sheaf
`𝒪_X` along the open embedding `f` is the structure sheaf `𝒪_Y`, as abelian sheaves
(`AlgebraicGeometry.LocallyRingedSpace.restrictAbStructureSheafAbIso`). Consequently the
cohomology of `𝒪_X` on the image `f(V)` of an open `V` of `Y` is the cohomology of `𝒪_Y` on `V`
(`AlgebraicGeometry.LocallyRingedSpace.structureSheafAbImageAddEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The structure sheaf `𝒪_Y` of a locally ringed space, as an abelian sheaf: the underlying
abelian sheaf of the unit sheaf of modules. -/
noncomputable abbrev structureSheafAb (Y : LocallyRingedSpace.{u}) :
    TopCat.AbSheaf Y.toPresheafedSpace :=
  (modulesToAb Y).obj (SheafOfModules.unit Y.ringSheaf)

variable {Y X : LocallyRingedSpace.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (hf : IsOpenEmbedding f.base)

/-- For an open immersion `f : Y ⟶ X`, the restriction of `𝒪_X` along `f` is `𝒪_Y`, as abelian
sheaves: on `V`, it is the inverse of `invApp f V : 𝒪_Y(V) ⟶ 𝒪_X(f(V))`. -/
noncomputable def restrictAbStructureSheafAbIso :
    (TopCat.Sheaf.restrictAb hf).obj X.structureSheafAb ≅ Y.structureSheafAb :=
  ((sheafToPresheaf _ _).preimageIso <| NatIso.ofComponents
    (fun V => (RingEquiv.toAddEquiv
      (asIso (PresheafedSpace.IsOpenImmersion.invApp f.toHom V.unop)).commRingCatIsoToRingEquiv
      ).toAddCommGrpIso)
    (by
      intro V W i
      ext s
      exact congrArg (fun g => g s) (congrArg CommRingCat.Hom.hom
        (PresheafedSpace.IsOpenImmersion.inv_naturality f.toHom i)))).symm

/-- For an open immersion `f : Y ⟶ X` and `V : Opens Y`, the cohomology of `𝒪_X` on `f(V)` is the
cohomology of `𝒪_Y` on `V`. -/
noncomputable def structureSheafAbImageAddEquiv (V : Opens Y) (q : ℕ) :
    TopCat.Sheaf.H
        ((TopCat.Sheaf.restrictOpen (hf.isOpenMap.functor.obj V)).obj X.structureSheafAb) q ≃+
      TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen V).obj Y.structureSheafAb) q :=
  (TopCat.Sheaf.H.restrictOpenImageAddEquiv hf V _ q).trans
    (TopCat.Sheaf.H.restrictOpenAddEquivOfIso V (restrictAbStructureSheafAbIso f hf) q)

/-- For an open immersion `f : Y ⟶ X`, `V : Opens Y` and `W : Opens X` with `f(V) = W`, the
cohomology of `𝒪_X` on `W` is the cohomology of `𝒪_Y` on `V`. -/
noncomputable def structureSheafAbAddEquivOfEq (V : Opens Y) {W : Opens X}
    (hW : hf.isOpenMap.functor.obj V = W) (q : ℕ) :
    TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj X.structureSheafAb) q ≃+
      TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen V).obj Y.structureSheafAb) q := by
  subst hW
  exact structureSheafAbImageAddEquiv f hf V q

/-- Acyclicity of `𝒪` transfers along open immersions: if `f(V) = W` (as sets) and
`Hᵠ(V, 𝒪_Y) = 0`, then `Hᵠ(W, 𝒪_X) = 0`. -/
lemma subsingleton_H_structureSheafAb_of_image_eq (V : Opens Y) {W : Opens X}
    (hW : f.base '' (V : Set Y) = (W : Set X)) (q : ℕ)
    (h : Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen V).obj Y.structureSheafAb) q)) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj X.structureSheafAb) q) :=
  (structureSheafAbAddEquivOfEq f (PresheafedSpace.IsOpenImmersion.base_open (f := f.toHom)) V
    (Opens.ext hW) q).subsingleton_congr.2 h

end AlgebraicGeometry.LocallyRingedSpace

end
