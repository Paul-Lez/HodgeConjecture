/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Cohomology

/-!
# Cohomology of sheaves of modules as a module over global sections

Let `Y` be a locally ringed space and `M` a sheaf of `𝒪_Y`-modules. A global section
`r ∈ Γ(Y, 𝒪_Y)` acts on `M` by the endomorphism `m ↦ r|_U • m` on sections over `U`
(`AlgebraicGeometry.LocallyRingedSpace.modulesSMul`), which is `𝒪_Y`-linear because `𝒪_Y` is
commutative. Applying `Hᵠ(Y, -)` gives an action of `Γ(Y, 𝒪_Y)` on `Hᵠ(Y, M)`; the module axioms
follow from functoriality and additivity of `Hᵠ(Y, -)`.

## Main definitions and results

* `AlgebraicGeometry.LocallyRingedSpace.modulesSMul M r : M ⟶ M`, central in the sense of
  `AlgebraicGeometry.LocallyRingedSpace.modulesSMul_naturality`.
* `instance : Module Γ(Y, 𝒪_Y) (H M q)`, with `r • x = H.map (modulesSMul M r) q x`
  (`AlgebraicGeometry.LocallyRingedSpace.H.smul_def`).
* `AlgebraicGeometry.LocallyRingedSpace.H.map_smul` and `H.mapₗ`: maps induced by morphisms of
  sheaves of modules are linear; `H.δ_smul`: so are the connecting homomorphisms.
* `AlgebraicGeometry.LocallyRingedSpace.Hom.cohomologyMap_smul`: for `f : X ⟶ Y` the comparison
  map `Hᵠ(Y, M) → Hᵠ(X, f^* M)` is semilinear along `Γ(f) : Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`.

For a ring `R` with a ring map `α : R →+* Γ(Y, 𝒪_Y)` (for instance `ℂ` on a complex analytic
space) the `R`-module structure is `Module.compHom _ α`, and all of the above is `R`-linear.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

/-- The restriction of a global section `r` of `𝒪_Y` to `U`, as an element of the ring over
which the sections of a sheaf of `𝒪_Y`-modules over `U` form a module. -/
noncomputable def restrictGlobal (r : Y.presheaf.obj (op ⊤)) (U : (Opens Y)ᵒᵖ) :
    Y.ringSheaf.obj.obj U :=
  Y.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op r

lemma restrictGlobal_map (r : Y.presheaf.obj (op ⊤)) {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V) :
    Y.ringSheaf.obj.map f (restrictGlobal r U) = restrictGlobal r V := by
  change Y.presheaf.map f (Y.presheaf.map _ r) = _
  rw [← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp]
  rfl

@[simp]
lemma restrictGlobal_one (U : (Opens Y)ᵒᵖ) : restrictGlobal (1 : Y.presheaf.obj (op ⊤)) U = 1 :=
  map_one (Y.presheaf.map _).hom

lemma restrictGlobal_mul (r s : Y.presheaf.obj (op ⊤)) (U : (Opens Y)ᵒᵖ) :
    restrictGlobal (r * s) U = restrictGlobal r U * restrictGlobal s U :=
  map_mul (Y.presheaf.map _).hom r s

lemma restrictGlobal_add (r s : Y.presheaf.obj (op ⊤)) (U : (Opens Y)ᵒᵖ) :
    restrictGlobal (r + s) U = restrictGlobal r U + restrictGlobal s U :=
  map_add (Y.presheaf.map _).hom r s

@[simp]
lemma restrictGlobal_zero (U : (Opens Y)ᵒᵖ) : restrictGlobal (0 : Y.presheaf.obj (op ⊤)) U = 0 :=
  map_zero (Y.presheaf.map _).hom

lemma mul_comm_ringSheaf {U : (Opens Y)ᵒᵖ} (a b : Y.ringSheaf.obj.obj U) : a * b = b * a :=
  @mul_comm (Y.presheaf.obj U) _ a b

/-- **Multiplication by a global section** `r` of `𝒪_Y` on a sheaf of `𝒪_Y`-modules. -/
noncomputable def modulesSMul (M : SheafOfModules.{u} Y.ringSheaf) (r : Y.presheaf.obj (op ⊤)) :
    M ⟶ M where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ (restrictGlobal r U))
      naturality {U V} f := by
        ext m
        change restrictGlobal r V • M.val.map f m = M.val.map f (restrictGlobal r U • m)
        exact (congrArg (· • M.val.map f m) (restrictGlobal_map r f)).symm.trans
          (M.val.map_smul f _ m).symm }
    fun U s m => by
      change restrictGlobal r U • s • m = s • restrictGlobal r U • m
      rw [smul_smul, smul_smul, mul_comm_ringSheaf]

@[simp]
lemma modulesSMul_val_app_apply (M : SheafOfModules.{u} Y.ringSheaf) (r : Y.presheaf.obj (op ⊤))
    (U : (Opens Y)ᵒᵖ) (m : M.val.obj U) :
    (modulesSMul M r).val.app U m = restrictGlobal r U • m :=
  rfl

variable (M : SheafOfModules.{u} Y.ringSheaf)

lemma modulesSMul_one : modulesSMul M 1 = 𝟙 M := by
  ext U m
  simp

lemma modulesSMul_mul (r s : Y.presheaf.obj (op ⊤)) :
    modulesSMul M (r * s) = modulesSMul M s ≫ modulesSMul M r := by
  ext U m
  simp only [modulesSMul_val_app_apply, restrictGlobal_mul, mul_smul]
  rfl

lemma modulesSMul_add (r s : Y.presheaf.obj (op ⊤)) :
    modulesSMul M (r + s) = modulesSMul M r + modulesSMul M s := by
  ext U m
  simp [restrictGlobal_add, add_smul]

lemma modulesSMul_zero : modulesSMul M 0 = 0 := by
  ext U m
  simp only [modulesSMul_val_app_apply, restrictGlobal_zero, zero_smul]
  rfl

variable {M} in
/-- Multiplication by a global section commutes with morphisms of sheaves of modules. -/
@[reassoc]
lemma modulesSMul_naturality {N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N)
    (r : Y.presheaf.obj (op ⊤)) : φ ≫ modulesSMul N r = modulesSMul M r ≫ φ := by
  ext U m
  simp

namespace H

/-- **`Hᵠ(Y, M)` is a module over `Γ(Y, 𝒪_Y)`**: `r` acts by the map induced by multiplication
by `r` on `M`. -/
noncomputable instance module (q : ℕ) : Module (Y.presheaf.obj (op ⊤)) (H M q) where
  smul r x := map (modulesSMul M r) q x
  one_smul x := by
    change map _ q x = x
    rw [modulesSMul_one, map_id_apply]
  mul_smul r s x := by
    change map _ q x = map _ q (map _ q x)
    rw [modulesSMul_mul, map_comp_apply]
  smul_zero r := map_zero _
  smul_add r x y := map_add _ x y
  add_smul r s x := by
    change map _ q x = map _ q x + map _ q x
    rw [modulesSMul_add, map, Functor.map_add, TopCat.Sheaf.H.map_add_apply]
    rfl
  zero_smul x := by
    change map _ q x = 0
    rw [modulesSMul_zero, map, Functor.map_zero, TopCat.Sheaf.H.map_zero_apply]

lemma smul_def {q : ℕ} (r : Y.presheaf.obj (op ⊤)) (x : H M q) :
    r • x = map (modulesSMul M r) q x :=
  rfl

variable {M}

/-- Maps induced by morphisms of sheaves of modules are `Γ(Y, 𝒪_Y)`-linear. -/
lemma map_smul {N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N) {q : ℕ}
    (r : Y.presheaf.obj (op ⊤)) (x : H M q) : map φ q (r • x) = r • map φ q x := by
  rw [smul_def, smul_def, ← map_comp_apply, ← map_comp_apply, modulesSMul_naturality]

/-- The map `Hᵠ(Y, M) → Hᵠ(Y, N)` induced by a morphism of sheaves of modules, as a
`Γ(Y, 𝒪_Y)`-linear map. -/
noncomputable def mapₗ {N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N) (q : ℕ) :
    H M q →ₗ[Y.presheaf.obj (op ⊤)] H N q where
  toFun := map φ q
  map_add' := map_add _
  map_smul' := map_smul φ

@[simp]
lemma mapₗ_apply {N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N) {q : ℕ} (x : H M q) :
    mapₗ φ q x = map φ q x :=
  rfl

/-- Multiplication by a global section, as an endomorphism of a short complex of sheaves of
modules. -/
@[simps]
noncomputable def shortComplexSMul (S : ShortComplex (SheafOfModules.{u} Y.ringSheaf))
    (r : Y.presheaf.obj (op ⊤)) : S ⟶ S where
  τ₁ := modulesSMul S.X₁ r
  τ₂ := modulesSMul S.X₂ r
  τ₃ := modulesSMul S.X₃ r
  comm₁₂ := (modulesSMul_naturality S.f r).symm
  comm₂₃ := (modulesSMul_naturality S.g r).symm

/-- The connecting homomorphisms are `Γ(Y, 𝒪_Y)`-linear. -/
lemma δ_smul {S : ShortComplex (SheafOfModules.{u} Y.ringSheaf)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (r : Y.presheaf.obj (op ⊤)) (x : H S.X₃ n₀) :
    δ hS n₀ n₁ h (r • x) = r • δ hS n₀ n₁ h x :=
  TopCat.Sheaf.H.δ_naturality (shortExact_map_modulesToAb hS) (shortExact_map_modulesToAb hS)
    ((modulesToAb Y).mapShortComplex.map (shortComplexSMul S r)) h x

/-- The connecting homomorphism as a `Γ(Y, 𝒪_Y)`-linear map. -/
noncomputable def δₗ {S : ShortComplex (SheafOfModules.{u} Y.ringSheaf)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : H S.X₃ n₀ →ₗ[Y.presheaf.obj (op ⊤)] H S.X₁ n₁ where
  toFun := δ hS n₀ n₁ h
  map_add' := map_add _
  map_smul' := δ_smul hS h

end H

section Comparison

variable {X : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- The ring map `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)` on global sections induced by `f : X ⟶ Y`. -/
noncomputable abbrev Hom.globalSectionsRingHom :
    Y.presheaf.obj (op ⊤) →+* X.presheaf.obj (op ⊤) :=
  (Γ.map f.op).hom

/-- The pushforward of multiplication by `Γ(f) r` is multiplication by `r`. -/
lemma pushforward_map_modulesSMul (N : SheafOfModules.{u} X.ringSheaf)
    (r : Y.presheaf.obj (op ⊤)) :
    (SheafOfModules.pushforward.{u} f.toRingSheafHom).map
        (modulesSMul N (f.globalSectionsRingHom r)) =
      modulesSMul ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj N) r := by
  ext U m
  let U' : (Opens X)ᵒᵖ := op ((Opens.map f.base).obj U.unop)
  let a : X.ringSheaf.obj.obj U' := f.c.app U (restrictGlobal r U)
  have key : restrictGlobal (f.globalSectionsRingHom r) U' = a :=
    (ConcreteCategory.congr_hom (f.c.naturality (homOfLE le_top : U.unop ⟶ ⊤).op) r).symm
  let m' : N.val.obj U' := m
  have : restrictGlobal (f.globalSectionsRingHom r) U' • m' = a • m' := by
    rw [key]
  exact this

/-- Pullback of multiplication by `r` is multiplication by `Γ(f) r`. -/
lemma pullbackModules_map_modulesSMul (r : Y.presheaf.obj (op ⊤)) :
    f.pullbackModules.map (modulesSMul M r) =
      modulesSMul (f.pullbackModules.obj M) (f.globalSectionsRingHom r) := by
  apply (f.pullbackModulesAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_modulesSMul]
  exact (f.pullbackModulesAdj.unit.naturality (modulesSMul M r)).symm.trans
    (modulesSMul_naturality (f.pullbackModulesAdj.unit.app M) r).symm

/-- **The comparison map `Hᵠ(Y, M) → Hᵠ(X, f^* M)` is semilinear** along
`Γ(f) : Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. -/
lemma Hom.cohomologyMap_smul {q : ℕ} (r : Y.presheaf.obj (op ⊤)) (x : H M q) :
    f.cohomologyMap M q (r • x) = f.globalSectionsRingHom r • f.cohomologyMap M q x := by
  rw [H.smul_def, Hom.cohomologyMap_map, pullbackModules_map_modulesSMul, H.smul_def]

/-- The comparison map `Hᵠ(Y, M) → Hᵠ(X, f^* M)` as a semilinear map. -/
noncomputable def Hom.cohomologyMapₛₗ (q : ℕ) :
    H M q →ₛₗ[f.globalSectionsRingHom] H (f.pullbackModules.obj M) q where
  toFun := f.cohomologyMap M q
  map_add' := map_add _
  map_smul' := f.cohomologyMap_smul M

end Comparison

end AlgebraicGeometry.LocallyRingedSpace

end
