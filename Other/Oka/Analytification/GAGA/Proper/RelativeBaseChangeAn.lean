/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.RelativeSerreAn

/-!
# Holomorphic functions on the base acting on sections over `D × ℙᴺ`

Let `P = ℙₒ(N; A)`, `A = ℂ[y₀, …, y_{m-1}]`, and `D ⊆ ℂᵐ` open. Holomorphic functions on `D` pull
back along `P^an ⟶ ℂᵐ` to sections of `𝒪_{P^an}` over `tube D = D × ℙᴺ`
(`ComplexAnalytic.relProjectiveSpaceAn.baseRingHom D`), with value `f(y)` at `[v; y]`
(`secFun_baseRingHom`). Polynomials in `y` are holomorphic functions
(`ComplexAnalytic.relProjectiveSpaceAn.polyToOka D : A →+* 𝒪(D)`), and the pullback to `P^an`
of the constant `a ∈ A = Γ(Spec A, 𝒪)` of `P`, restricted to `tube D`, is the pullback of the
holomorphic function `a` on `D` (`restrict_πc_constRingHom`): both have value `a(y)` at
`[v; y]`.

Hence `Γ(tube D, G^an)` is a module over `𝒪(D)` and the map `Γ(P, G) → Γ(tube D, G^an)` (the
unit of the analytification, restricted to `tube D`) is `A`-linear
(`ComplexAnalytic.relProjectiveSpaceAn.algSec`); it extends to the canonical `𝒪(D)`-linear map
`𝒪(D) ⊗_A Γ(P, G) → Γ(tube D, G^an)` (`ComplexAnalytic.relProjectiveSpaceAn.canMap`), natural in
`G` (`canMap_naturality`).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology MvPolynomial
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic.relProjectiveSpaceAn

open AnalyticSpace ProjectiveSpace HomogeneousLocalization

variable {m N : ℕ}

/-! ### Holomorphic functions on the base -/

/-- The open `D ⊆ ℂᵐ`, as an open of `AnalyticSpace.complexAffineSpace m`. -/
def baseOpens (D : Opens (Fin m → ℂ)) : Opens (ULift.{u} (Fin m) → ℂ) :=
  ⟨projectiveSpaceAn.toFin ⁻¹' (D : Set (Fin m → ℂ)),
    D.isOpen.preimage (continuous_pi fun k ↦ continuous_apply (ULift.up k))⟩

lemma analyticAt_toFin (z : ULift.{u} (Fin m) → ℂ) :
    AnalyticAt ℂ (fun w : ULift.{u} (Fin m) → ℂ ↦ projectiveSpaceAn.toFin.{u} w) z :=
  analyticAt_pi_iff.2 fun k ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin m) ↦ ℂ) ⟨k⟩).analyticAt z

/-- Holomorphic functions on `D ⊆ ℂᵐ` as holomorphic functions on the corresponding open of
`ℂᵐ = AnalyticSpace.complexAffineSpace m` (coordinates indexed by `ULift (Fin m)`). -/
noncomputable def okaToFin (D : Opens (Fin m → ℂ)) :
    OkaRing D →+* OkaRing (baseOpens.{u} D) where
  toFun f := OkaRing.mk (fun z ↦ f.toFun _ ⟨projectiveSpaceAn.toFin z.1, z.2⟩) (by
    have key : OkaAnalytic (fun z : baseOpens.{u} D ↦
        (f.toGlobalFun _ ∘ projectiveSpaceAn.toFin.{u}) z.1) :=
      okaAnalytic_restrict fun z hz ↦ ((okaAnalytic_iff _).1 f.2 _ hz).comp (analyticAt_toFin z)
    have heq : (fun z : baseOpens.{u} D ↦ (f.toGlobalFun _ ∘ projectiveSpaceAn.toFin.{u}) z.1) =
        fun z ↦ f.toFun _ ⟨projectiveSpaceAn.toFin z.1, z.2⟩ :=
      funext fun z ↦ OkaRing.toGlobalFun_apply f z.2
    exact heq ▸ key)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (N) in
/-- **Holomorphic functions on `D` as sections of `𝒪_{P^an}` over `D × ℙᴺ`**: the pullback along
`P^an ⟶ ℂᵐ`. -/
noncomputable def baseRingHom (D : Opens (Fin m → ℂ)) :
    OkaRing D →+* (relProjectiveSpaceAn.{u} m N).presheaf.obj (op (tube D)) :=
  ((relProjectiveSpaceAnBase.{u} m N).toLRSHom.c.app (op (baseOpens D))).hom.comp (okaToFin D)

lemma eval_baseRingHom (D : Opens (Fin m → ℂ)) (f : OkaRing D)
    {x : relProjectiveSpaceAn.{u} m N} (hx : x ∈ tube.{u} (N := N) D) :
    (relProjectiveSpaceAn.{u} m N).eval x hx (baseRingHom N D f) = f.toGlobalFun _ (baseY x) := by
  refine (eval_c_app _ (relProjectiveSpaceAnBase.{u} m N).isCLinear (U := baseOpens D) x hx
    (okaToFin D f)).trans ?_
  rw [eval_complexAffineSpace_of _ hx, OkaRing.evalHom_apply, OkaRing.toGlobalFun_apply _ hx]
  rfl

lemma secFun_baseRingHom (D : Opens (Fin m → ℂ)) (f : OkaRing D)
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∈ vecCone.{u} (tube.{u} (N := N) D)) :
    secFun (baseRingHom.{u} N D f) p = f.toGlobalFun _ p.2 := by
  refine (secFun_of_mem _ hp.1 hp.2).trans ?_
  rw [eval_baseRingHom, baseY_pointOfVec]

/-- The coordinate function `y ↦ yⱼ` on `D`. -/
noncomputable def coordOka (D : Opens (Fin m → ℂ)) (j : Fin m) : OkaRing D :=
  OkaRing.ofDifferentiableOn (fun y ↦ y j) (differentiable_apply j).differentiableOn

/-- **Polynomials in `y` as holomorphic functions on `D`.** -/
noncomputable def polyToOka (D : Opens (Fin m → ℂ)) : RelBase.{u} m →+* OkaRing D :=
  eval₂Hom ((algebraMap ℂ (OkaRing D)).comp projectiveSpaceAn.φ.{u}) (coordOka D)

lemma toGlobalFun_polyToOka (D : Opens (Fin m → ℂ)) (a : RelBase.{u} m) {y : Fin m → ℂ}
    (hy : y ∈ D) : (polyToOka.{u} D a).toGlobalFun _ y = evalBase.{u} y a := by
  rw [OkaRing.toGlobalFun_apply _ hy]
  change OkaRing.evalHom hy (polyToOka.{u} D a) = evalBase y a
  refine congrArg (fun F : RelBase.{u} m →+* ℂ ↦ F a) (MvPolynomial.ringHom_ext (fun c ↦ ?_)
    (fun j ↦ ?_) : (OkaRing.evalHom hy).comp (polyToOka.{u} D) = evalBase y)
  · simp only [RingHom.coe_comp, Function.comp_apply, polyToOka, eval₂Hom_C, evalBase]
    exact OkaRing.evalHom_algebraMap hy _
  · simp only [RingHom.coe_comp, Function.comp_apply, polyToOka, eval₂Hom_X', evalBase]
    rfl

variable (N) in
/-- The constants `A → Γ(P, 𝒪)`, pulled back along `P ⟶ Spec A`. -/
noncomputable def constRingHom : RelBase.{u} m →+* Γ(ℙₒ(N; RelBase.{u} m), ⊤) :=
  (ProjectiveSpace.toSpec N (RelBase.{u} m)).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (RelBase.{u} m))).inv.hom

/-- **The value at `[v; y]` of the pullback of a constant `a ∈ A` is `a(y)`.** -/
lemma evπ_constRingHom (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ)
    (a : RelBase.{u} m) :
    evπ.{u} (W := ⊤) v hv y trivial (constRingHom.{u} N a) = evalBase y a := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [← evπ_restrictOpen le_top v hv y (π_pointOfVec_mem_U v hv y i hi)]
  have hres : TopCat.Presheaf.restrictOpen (constRingHom.{u} N a) (U N (RelBase.{u} m) i)
      le_top = Proj.awayToSection _ (X i) (awayXBase _ i a) :=
    restrict_toSpec_appTop (X_mem_homogeneousSubmodule_one i) Nat.one_pos a
  rw [hres]
  exact (eval_π_awayToSection v hv y i hi _).trans (awayEval_awayXBase _ v i _ a)

/-- **The pullback to `D × ℙᴺ` of a constant `a ∈ A` of `P` is the pullback of the polynomial
function `a` on `D`.** -/
theorem restrict_πc_constRingHom (D : Opens (Fin m → ℂ)) (a : RelBase.{u} m) :
    TopCat.Presheaf.restrictOpen (F := (relProjectiveSpaceAn.{u} m N).presheaf)
      ((analytificationπLRS (relProjectiveSpace.{u} m N)).c.app (op ⊤) (constRingHom.{u} N a))
      (tube D) le_top = baseRingHom N D (polyToOka.{u} D a) := by
  refine eq_of_secFun fun p hp ↦ ?_
  rw [secFun_baseRingHom D _ hp, toGlobalFun_polyToOka D a (baseY_mem_of_mem_vecCone hp),
    secFun_restrictOpen, Set.indicator_of_mem hp, secFun_of_mem
      (W := (Opens.map (analytificationπLRS (relProjectiveSpace.{u} m N)).base).obj ⊤) _ hp.1
      trivial]
  exact evπ_constRingHom p.1 hp.1 p.2 a

/-! ### The canonical map `𝒪(D) ⊗_A Γ(P, G) → Γ(D × ℙᴺ, G^an)` -/

open LocallyRingedSpace
open scoped TensorProduct

noncomputable section

/-- `Γ(P, G)`, an `A`-module through the constants `A → Γ(P, 𝒪)`. -/
def AlgSec (G : ℙₒ(N; RelBase.{u} m).Modules) : Type u :=
  Γ(G, ⊤)

instance (G : ℙₒ(N; RelBase.{u} m).Modules) : AddCommGroup (AlgSec G) :=
  inferInstanceAs (AddCommGroup Γ(G, ⊤))

instance (G : ℙₒ(N; RelBase.{u} m).Modules) : Module Γ(ℙₒ(N; RelBase.{u} m), ⊤) (AlgSec G) :=
  inferInstanceAs (Module Γ(ℙₒ(N; RelBase.{u} m), ⊤) Γ(G, ⊤))

instance (G : ℙₒ(N; RelBase.{u} m).Modules) : Module (RelBase.{u} m) (AlgSec G) :=
  Module.compHom _ (constRingHom.{u} N)

lemma smul_algSec_def {G : ℙₒ(N; RelBase.{u} m).Modules} (a : RelBase.{u} m) (s : AlgSec G) :
    a • s = constRingHom.{u} N a • s :=
  rfl

/-- `Γ(D × ℙᴺ, G^an)`, a module over `Γ(tube D, 𝒪_{P^an})` and over `𝒪(D)`. -/
def AnSec (D : Opens (Fin m → ℂ)) (G : ℙₒ(N; RelBase.{u} m).Modules) : Type u :=
  ((analytificationModules (relProjectiveSpace.{u} m N)).obj G).val.obj (op (tube D))

variable (D : Opens (Fin m → ℂ)) (G : ℙₒ(N; RelBase.{u} m).Modules)

instance : AddCommGroup (AnSec D G) :=
  inferInstanceAs (AddCommGroup
    (((analytificationModules (relProjectiveSpace.{u} m N)).obj G).val.obj (op (tube D))))

instance : Module ((relProjectiveSpaceAn.{u} m N).presheaf.obj (op (tube D))) (AnSec D G) :=
  inferInstanceAs (Module ((relProjectiveSpaceAn.{u} m N).presheaf.obj (op (tube D)))
    (((analytificationModules (relProjectiveSpace.{u} m N)).obj G).val.obj (op (tube D))))

instance : Module (OkaRing D) (AnSec D G) :=
  Module.compHom _ (baseRingHom.{u} N D)

instance : Algebra (RelBase.{u} m) (OkaRing D) :=
  (polyToOka.{u} D).toAlgebra

instance : Module (RelBase.{u} m) (AnSec D G) :=
  Module.compHom _ ((baseRingHom.{u} N D).comp (polyToOka.{u} D))

variable {D G}

lemma smul_anSec_def (f : OkaRing D) (x : AnSec D G) : f • x = baseRingHom.{u} N D f • x :=
  rfl

lemma algebraMap_okaRing (a : RelBase.{u} m) :
    algebraMap (RelBase.{u} m) (OkaRing D) a = polyToOka.{u} D a :=
  rfl

instance : IsScalarTower (RelBase.{u} m) (OkaRing D) (AnSec D G) :=
  ⟨fun a f x ↦ by
    change baseRingHom.{u} N D (polyToOka.{u} D a * f) • x =
      baseRingHom.{u} N D (polyToOka.{u} D a) • baseRingHom.{u} N D f • x
    rw [map_mul, mul_smul]⟩

variable (D G)

/-- The unit `Γ(P, G) → Γ(P^an, G^an)` of the analytification. -/
noncomputable def unitSec : AlgSec G →+
    ((analytificationModules (relProjectiveSpace.{u} m N)).obj G).val.obj (op ⊤) :=
  ((analytificationModulesAdj (relProjectiveSpace.{u} m N)).unit.app G).val.app (op ⊤) |>.hom
    |>.toAddMonoidHom

/-- **The map `Γ(P, G) → Γ(D × ℙᴺ, G^an)`**: the unit of the analytification, restricted to
`tube D`. It is `A`-linear for the action of `A` on `Γ(D × ℙᴺ, G^an)` through `𝒪(D)`. -/
noncomputable def algSec : AlgSec G →ₗ[RelBase.{u} m] AnSec D G where
  toFun s := modRes (unitSec G s) (tube D) le_top
  map_add' s t := by
    rw [map_add]
    exact modRes_add _ _ _
  map_smul' a s := by
    change modRes (unitSec G (constRingHom.{u} N a • s)) (tube D) le_top =
      baseRingHom.{u} N D (polyToOka.{u} D a) • modRes (unitSec G s) (tube D) le_top
    rw [← restrict_πc_constRingHom D a]
    refine Eq.trans ?_ (modRes_smul le_top _ _)
    congr 1
    exact ((analytificationModulesAdj (relProjectiveSpace.{u} m N)).unit.app G).val.app
      (op ⊤) |>.hom.map_smul _ s

lemma algSec_apply (s : AlgSec G) :
    algSec D G s = modRes (unitSec G s) (tube D) le_top :=
  rfl

/-- **The canonical map `𝒪(D) ⊗_A Γ(P, G) → Γ(D × ℙᴺ, G^an)`**, `f ⊗ s ↦ f · s^an|_{D × ℙᴺ}`. -/
noncomputable def canMap : OkaRing D ⊗[RelBase.{u} m] AlgSec G →ₗ[OkaRing D] AnSec D G :=
  (algSec D G).liftBaseChange (OkaRing D)

lemma canMap_tmul (f : OkaRing D) (s : AlgSec G) :
    canMap D G (f ⊗ₜ s) = f • algSec D G s :=
  rfl

/-! ### Naturality -/

variable {D G} {G' : ℙₒ(N; RelBase.{u} m).Modules} (φ : G ⟶ G')

/-- A morphism of sheaves on `P`, on global sections, as an `A`-linear map. -/
noncomputable def algSecMap : AlgSec G →ₗ[RelBase.{u} m] AlgSec G' where
  toFun s := φ.app ⊤ s
  map_add' s t := map_add _ s t
  map_smul' a s := Scheme.Modules.Hom.app_smul φ (constRingHom.{u} N a) s

variable (D) in
/-- The analytification of a morphism of sheaves on `P`, on sections over `D × ℙᴺ`, as an
`𝒪(D)`-linear map. -/
noncomputable def anSecMap : AnSec D G →ₗ[OkaRing D] AnSec D G' where
  toFun x := ((analytificationModules (relProjectiveSpace.{u} m N)).map φ).val.app
    (op (tube D)) x
  map_add' x y := map_add _ x y
  map_smul' f x := modHom_smul _ (baseRingHom.{u} N D f) x

lemma unitSec_naturality (s : AlgSec G) :
    unitSec G' (algSecMap φ s) =
      ((analytificationModules (relProjectiveSpace.{u} m N)).map φ).val.app (op ⊤)
        (unitSec G s) := by
  have h := (analytificationModulesAdj (relProjectiveSpace.{u} m N)).unit.naturality φ
  exact congr((($h).val.app (op ⊤)).hom s)

lemma algSec_naturality (s : AlgSec G) :
    algSec D G' (algSecMap φ s) = anSecMap D φ (algSec D G s) := by
  rw [algSec_apply, algSec_apply, unitSec_naturality]
  exact (modHom_modRes _ le_top _).symm

/-- **The canonical map is natural in `G`.** -/
lemma canMap_naturality (x : OkaRing D ⊗[RelBase.{u} m] AlgSec G) :
    canMap D G' ((algSecMap φ).lTensor (OkaRing D) x) = anSecMap D φ (canMap D G x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f s =>
    rw [LinearMap.lTensor_tmul, canMap_tmul, canMap_tmul, algSec_naturality]
    exact ((anSecMap D φ).map_smul f _).symm
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, (canMap D G).map_add]
    exact ((anSecMap D φ).map_add _ _).symm

lemma algSecMap_id : algSecMap (𝟙 G) = LinearMap.id :=
  rfl

lemma algSecMap_comp {G'' : ℙₒ(N; RelBase.{u} m).Modules} (ψ : G' ⟶ G'') :
    algSecMap (φ ≫ ψ) = algSecMap ψ ∘ₗ algSecMap φ :=
  rfl

lemma algSecMap_add (ψ : G ⟶ G') : algSecMap (φ + ψ) = algSecMap φ + algSecMap ψ :=
  rfl

instance : (analytificationModules (relProjectiveSpace.{u} m N)).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (D G) in
lemma anSecMap_id : anSecMap D (𝟙 G) = LinearMap.id := by
  ext x
  have h := (analytificationModules (relProjectiveSpace.{u} m N)).map_id G
  exact congr((($h).val.app (op (tube D))).hom x)

lemma anSecMap_comp {G'' : ℙₒ(N; RelBase.{u} m).Modules} (ψ : G' ⟶ G'') :
    anSecMap D (φ ≫ ψ) = anSecMap D ψ ∘ₗ anSecMap D φ := by
  ext x
  have h := (analytificationModules (relProjectiveSpace.{u} m N)).map_comp φ ψ
  exact congr((($h).val.app (op (tube D))).hom x)

lemma anSecMap_add (ψ : G ⟶ G') : anSecMap D (φ + ψ) = anSecMap D φ + anSecMap D ψ := by
  ext x
  have h := (analytificationModules (relProjectiveSpace.{u} m N)).map_add (f := φ) (g := ψ)
  exact congr((($h).val.app (op (tube D))).hom x)

/-! ### Bijectivity of the canonical map along isomorphisms and finite sums -/

/-- Bijectivity of the canonical map is invariant under isomorphisms. -/
lemma bijective_canMap_of_iso (e : G ≅ G') (h : Function.Bijective (canMap D G)) :
    Function.Bijective (canMap D G') := by
  have hl : ∀ x, (algSecMap e.inv).lTensor (OkaRing D) ((algSecMap e.hom).lTensor (OkaRing D) x)
      = x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← algSecMap_comp, e.hom_inv_id,
      algSecMap_id, LinearMap.lTensor_id, LinearMap.id_apply]
  have hr : ∀ x, (algSecMap e.hom).lTensor (OkaRing D) ((algSecMap e.inv).lTensor (OkaRing D) x)
      = x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← algSecMap_comp, e.inv_hom_id,
      algSecMap_id, LinearMap.lTensor_id, LinearMap.id_apply]
  have al : ∀ y, anSecMap D e.inv (anSecMap D e.hom y) = y := fun y ↦ by
    have h1 := congrArg (fun F ↦ F y) (anSecMap_comp (D := D) e.hom e.inv)
    simp only [e.hom_inv_id, anSecMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h1
    exact h1.symm
  have ar : ∀ y, anSecMap D e.hom (anSecMap D e.inv y) = y := fun y ↦ by
    have h1 := congrArg (fun F ↦ F y) (anSecMap_comp (D := D) e.inv e.hom)
    simp only [e.inv_hom_id, anSecMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h1
    exact h1.symm
  have key : ∀ z, canMap D G' z =
      anSecMap D e.hom (canMap D G ((algSecMap e.inv).lTensor (OkaRing D) z)) := fun z ↦ by
    rw [← canMap_naturality, hr]
  refine ⟨fun x x' hxx' ↦ ?_, fun y ↦ ?_⟩
  · rw [key, key] at hxx'
    have := congrArg (anSecMap D e.inv) hxx'
    rw [al, al] at this
    rw [← hr x, ← hr x', h.1 this]
  · obtain ⟨x, hx⟩ := h.2 (anSecMap D e.inv y)
    exact ⟨(algSecMap e.hom).lTensor (OkaRing D) x, by rw [canMap_naturality, hx, ar]⟩

lemma algSecMap_zero : algSecMap (0 : G ⟶ G') = 0 :=
  rfl

lemma anSecMap_zero : anSecMap D (0 : G ⟶ G') = 0 := by
  ext x
  have h := (analytificationModules (relProjectiveSpace.{u} m N)).map_zero G G'
  exact congr((($h).val.app (op (tube D))).hom x)

/-- Bijectivity of the canonical map for a retract-sum decomposition `𝟙 = ∑ pᵢ ≫ ιᵢ`. -/
lemma bijective_canMap_of_sum {ι : Type*} (s : Finset ι) (X : ℙₒ(N; RelBase.{u} m).Modules)
    (Y : ι → ℙₒ(N; RelBase.{u} m).Modules) (p : ∀ i, X ⟶ Y i) (j : ∀ i, Y i ⟶ X)
    (hpj : ∑ i ∈ s, p i ≫ j i = 𝟙 X) (h : ∀ i ∈ s, Function.Bijective (canMap D (Y i))) :
    Function.Bijective (canMap D X) := by
  have halg' : ∀ (t : Finset ι) (x : OkaRing D ⊗[RelBase.{u} m] AlgSec X),
      (algSecMap (∑ i ∈ t, p i ≫ j i)).lTensor (OkaRing D) x =
        ∑ i ∈ t, (algSecMap (j i)).lTensor (OkaRing D) ((algSecMap (p i)).lTensor _ x) := by
    intro t x
    induction t using Finset.cons_induction with
    | empty => simp [algSecMap_zero]
    | cons a t ha ih =>
      rw [Finset.sum_cons, algSecMap_add, LinearMap.lTensor_add, LinearMap.add_apply, ih,
        Finset.sum_cons, algSecMap_comp, LinearMap.lTensor_comp, LinearMap.comp_apply]
  have halg : ∀ x : OkaRing D ⊗[RelBase.{u} m] AlgSec X,
      x = ∑ i ∈ s, (algSecMap (j i)).lTensor (OkaRing D) ((algSecMap (p i)).lTensor _ x) :=
    fun x ↦ by rw [← halg', hpj, algSecMap_id, LinearMap.lTensor_id, LinearMap.id_apply]
  have han' : ∀ (t : Finset ι) (y : AnSec D X),
      anSecMap D (∑ i ∈ t, p i ≫ j i) y = ∑ i ∈ t, anSecMap D (j i) (anSecMap D (p i) y) := by
    intro t y
    induction t using Finset.cons_induction with
    | empty => simp [anSecMap_zero]
    | cons a t ha ih =>
      rw [Finset.sum_cons, anSecMap_add, LinearMap.add_apply, ih, Finset.sum_cons,
        anSecMap_comp, LinearMap.comp_apply]
  have han : ∀ y : AnSec D X, y = ∑ i ∈ s, anSecMap D (j i) (anSecMap D (p i) y) :=
    fun y ↦ by rw [← han', hpj, anSecMap_id, LinearMap.id_apply]
  refine ⟨fun x x' hxx' ↦ ?_, fun y ↦ ?_⟩
  · rw [halg x, halg x']
    refine Finset.sum_congr rfl fun i hi ↦ congrArg _ ((h i hi).1 ?_)
    rw [canMap_naturality, canMap_naturality, hxx']
  · choose! x hx using fun i hi ↦ (h i hi).2 (anSecMap D (p i) y)
    refine ⟨∑ i ∈ s, (algSecMap (j i)).lTensor (OkaRing D) (x i), ?_⟩
    rw [map_sum, han y]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [canMap_naturality, hx i hi]

open Limits in
/-- Bijectivity of the canonical map for finite coproducts. -/
lemma bijective_canMap_sigma {I : Type u} [Finite I] (Y : I → ℙₒ(N; RelBase.{u} m).Modules)
    (h : ∀ i, Function.Bijective (canMap D (Y i))) : Function.Bijective (canMap D (∐ Y)) := by
  have := Fintype.ofFinite I
  have := HasBiproduct.of_hasCoproduct Y
  refine bijective_canMap_of_iso (biproduct.isoCoproduct Y) ?_
  exact bijective_canMap_of_sum Finset.univ (⨁ Y) Y (biproduct.π Y) (biproduct.ι Y)
    (IsBilimit.total (biproduct.isBilimit Y)) fun i _ ↦ h i

/-! ### Exact sequences of sections -/

section Exact

open Limits

variable {X : TopCat.{u}} {S : ShortComplex (TopCat.AbSheaf X)} (hS : S.ShortExact)
include hS

/-- Sections over an open are left exact. -/
lemma exact_app_of_shortExact (V : Opens X) :
    Function.Exact (S.f.hom.app (op V)) (S.g.hom.app (op V)) := by
  have hS' := TopCat.Sheaf.shortExact_restrictOpen V hS
  have h : Function.Exact (TopCat.Sheaf.H.map ((TopCat.Sheaf.restrictOpen V).map S.f) 0)
      (TopCat.Sheaf.H.map ((TopCat.Sheaf.restrictOpen V).map S.g) 0) :=
    TopCat.Sheaf.H.exact₂ hS' 0
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (h ((TopCat.Sheaf.H.restrictOpenEquiv₀ V S.X₂).symm y)).1 (by
      apply (TopCat.Sheaf.H.restrictOpenEquiv₀ V S.X₃).injective
      rw [TopCat.Sheaf.H.restrictOpenEquiv₀_map, AddEquiv.apply_symm_apply, hy, map_zero])
    refine ⟨TopCat.Sheaf.H.restrictOpenEquiv₀ V S.X₁ x, ?_⟩
    rw [← TopCat.Sheaf.H.restrictOpenEquiv₀_map, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact congr(($S.zero).hom.app (op V) x)

/-- Sections over an open preserve monomorphisms. -/
lemma injective_app_of_shortExact (V : Opens X) : Function.Injective (S.f.hom.app (op V)) := by
  have hS' := TopCat.Sheaf.shortExact_restrictOpen V hS
  have h := TopCat.Sheaf.H.map_f_injective_zero hS'
  simp only [ShortComplex.map_f] at h
  intro x x' hxx'
  have key : TopCat.Sheaf.H.map ((TopCat.Sheaf.restrictOpen V).map S.f) 0
      ((TopCat.Sheaf.H.restrictOpenEquiv₀ V S.X₁).symm x) =
      TopCat.Sheaf.H.map ((TopCat.Sheaf.restrictOpen V).map S.f) 0
        ((TopCat.Sheaf.H.restrictOpenEquiv₀ V S.X₁).symm x') := by
    apply (TopCat.Sheaf.H.restrictOpenEquiv₀ V S.X₂).injective
    rw [TopCat.Sheaf.H.restrictOpenEquiv₀_map, TopCat.Sheaf.H.restrictOpenEquiv₀_map,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hxx']
  have := h key
  simpa using congrArg (TopCat.Sheaf.H.restrictOpenEquiv₀ V S.X₁) this

end Exact

variable {S : ShortComplex ℙₒ(N; RelBase.{u} m).Modules} (hS : S.ShortExact)
include hS

lemma exact_algSecMap : Function.Exact (algSecMap S.f) (algSecMap S.g) :=
  exact_app_of_shortExact (hS.map_of_exact (Scheme.Modules.toAbFunctor ℙₒ(N; RelBase.{u} m))) ⊤

lemma surjective_algSecMap
    (h : ∀ x : TopCat.Sheaf.H ((SheafOfModules.toSheaf ℙₒ(N; RelBase.{u} m).ringCatSheaf).obj S.X₁)
      1, x = 0) : Function.Surjective (algSecMap S.g) :=
  TopCat.Sheaf.surjective_of_H_one (hS.map_of_exact (Scheme.Modules.toAbFunctor _)) h

variable (D) in
lemma exact_anSecMap : Function.Exact (anSecMap D S.f) (anSecMap D S.g) :=
  exact_app_of_shortExact ((shortExact_map_analytificationModules
    (X := relProjectiveSpace.{u} m N) hS).map_of_exact (modulesToAb _)) (tube D)

variable (D) in
lemma surjective_anSecMap
    (h : ∀ x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := N) D)).obj
      ((analytificationModules (relProjectiveSpace.{u} m N)).obj S.X₁).toAb) 1, x = 0) :
    Function.Surjective (anSecMap D S.g) :=
  TopCat.Sheaf.surjective_of_H_one_restrictOpen (tube D)
    ((shortExact_map_analytificationModules (X := relProjectiveSpace.{u} m N) hS).map_of_exact
      (modulesToAb _)) h

omit hS

/-! ### The canonical map for `G(n)`, `n ≫ 0` -/

variable
  (hO : ∀ (e : ℕ) (D : Opens (Fin m → ℂ)),
    Function.Bijective (canMap D (twistingSheaf N (RelBase.{u} m) e)))

include hO in
/-- The canonical map is bijective for `𝒪^I(e)`, `I` finite and `e ≥ 0`, given it is for
`𝒪(e)`. -/
lemma bijective_canMap_twist_free {I : Type u} [Finite I] (e : ℕ) :
    Function.Bijective (canMap D (twist (SheafOfModules.free I : ℙₒ(N; RelBase.{u} m).Modules)
      e)) :=
  bijective_canMap_of_iso (twistFreeIso (n := N) (R := RelBase.{u} m) I e).symm
    (bijective_canMap_sigma _ fun _ ↦ hO e D)

open Limits in
include hO in
/-- **Surjectivity of the canonical map for `G(n)`, `n ≫ 0`, uniformly in the box.** -/
theorem exists_surjective_canMap (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ (a b : Fin m → ℂ) (B : Opens (Fin m → ℂ)),
      (B : Set (Fin m → ℂ)) = Complex.openBox a b →
        Function.Surjective (canMap B (twist G n)) := by
  obtain ⟨m₁, hm₁⟩ := exists_epi_twist_free_isCoherent_kernel G
  obtain ⟨I, _, π, _, -, hK⟩ := hm₁ m₁ le_rfl
  obtain ⟨nK, hnK⟩ := exists_H_tube_twist_eq_zero (kernel π)
  refine ⟨max nK m₁, fun n hn a b B hB y ↦ ?_⟩
  let S : ShortComplex ℙₒ(N; RelBase.{u} m).Modules :=
    ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
      inferInstance inferInstance
  have hSn := hS.map_of_exact (twistFunctor N (RelBase.{u} m) n)
  obtain ⟨z, rfl⟩ := surjective_anSecMap B hSn (fun x ↦ hnK n (le_of_max_le_left hn) a b B hB 0 x) y
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = -(m₁ : ℤ) + n := ⟨(-(m₁ : ℤ) + n).toNat,
    Int.toNat_of_nonneg (by omega)⟩
  have hE : Function.Bijective (canMap B (twist (twist (SheafOfModules.free I :
      ℙₒ(N; RelBase.{u} m).Modules) (-(m₁ : ℤ))) n)) := by
    refine bijective_canMap_of_iso (twistTwistIso _ (-(m₁ : ℤ)) n).symm ?_
    rw [← he]
    exact bijective_canMap_twist_free hO e
  obtain ⟨w, rfl⟩ := hE.2 z
  exact ⟨(algSecMap (S.map (twistFunctor N (RelBase.{u} m) n)).g).lTensor (OkaRing B) w,
    canMap_naturality _ w⟩

open Limits in
include hO in
/-- **Relative base change for sections over boxes**: for coherent `G` on `P` there is `n₀`,
depending only on `G`, such that the canonical map `𝒪(B) ⊗_A Γ(P, G(n)) → Γ(B × ℙᴺ, G(n)^an)`
is bijective for all `n ≥ n₀` and all open boxes `B`, given that it is for the sheaves `𝒪(e)`,
`e ≥ 0` (hypothesis `hO`). -/
theorem exists_bijective_canMap_of_twistingSheaf (G : ℙₒ(N; RelBase.{u} m).Modules)
    [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ (a b : Fin m → ℂ) (B : Opens (Fin m → ℂ)),
      (B : Set (Fin m → ℂ)) = Complex.openBox a b →
        Function.Bijective (canMap B (twist G n)) := by
  obtain ⟨m₁, hm₁⟩ := exists_epi_twist_free_isCoherent_kernel G
  obtain ⟨I, _, π, _, -, hK⟩ := hm₁ m₁ le_rfl
  obtain ⟨nS, hnS⟩ := exists_surjective_canMap hO (kernel π)
  obtain ⟨nA, hnA⟩ := ProjectiveSpace.exists_H_twist_eq_zero (kernel π)
  obtain ⟨nG, hnG⟩ := exists_surjective_canMap hO G
  refine ⟨max (max nS nA) (max nG m₁), fun n hn a b B hB ↦ ⟨fun x x' hxx' ↦ ?_,
    hnG n (by omega) a b B hB⟩⟩
  let S : ShortComplex ℙₒ(N; RelBase.{u} m).Modules :=
    ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
      inferInstance inferInstance
  have hSn := hS.map_of_exact (twistFunctor N (RelBase.{u} m) n)
  set Sn := S.map (twistFunctor N (RelBase.{u} m) n)
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = -(m₁ : ℤ) + n := ⟨(-(m₁ : ℤ) + n).toNat,
    Int.toNat_of_nonneg (by omega)⟩
  have hE : Function.Bijective (canMap B Sn.X₂) := by
    refine bijective_canMap_of_iso (twistTwistIso _ (-(m₁ : ℤ)) n).symm ?_
    rw [← he]
    exact bijective_canMap_twist_free hO e
  have hgs := surjective_algSecMap hSn (fun x ↦ hnA n (by omega) 0 x)
  have hT := lTensor_exact (OkaRing B) (exact_algSecMap hSn) hgs
  have hTs := LinearMap.lTensor_surjective (OkaRing B) hgs
  have hAn := exact_anSecMap B hSn
  have hKs := hnS n (by omega) a b B hB
  -- `x - x'` maps to zero; lift it along `𝒪(B) ⊗ Γ(E(n)) → 𝒪(B) ⊗ Γ(G(n))`
  suffices h0 : ∀ z, canMap B Sn.X₃ z = 0 → z = 0 by
    have h := (canMap B (twist G n)).map_sub x x'
    rw [hxx', sub_self] at h
    exact sub_eq_zero.1 (h0 _ h)
  intro z hz
  obtain ⟨w, rfl⟩ := hTs z
  have h1 : anSecMap B Sn.g (canMap B Sn.X₂ w) = 0 := by
    rw [← canMap_naturality]
    exact hz
  obtain ⟨k, hk⟩ := (hAn _).1 h1
  obtain ⟨k', rfl⟩ := hKs k
  have h2 : (algSecMap Sn.f).lTensor (OkaRing B) k' = w := by
    apply hE.1
    rw [canMap_naturality]
    exact hk
  rw [← h2]
  exact (hT _).2 ⟨k', rfl⟩

end

end ComplexAnalytic.relProjectiveSpaceAn

end
