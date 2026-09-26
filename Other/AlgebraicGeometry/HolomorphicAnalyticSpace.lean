/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLocallyRingedSpace
public import Other.Oka.AnalyticSpace.Coherent
public import Other.Oka.Geometry.RingedSpace.OpenImmersion

/-! Comparison data needed to view the complex-point space as an Oka analytic space. -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Topology
open scoped ContDiff Manifold

universe u

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

private def IsCLinearSheafedHom {Y Z : SheafedSpace CommRingCat} (f : Y ⟶ Z)
    (α : ℂ →+* Y.presheaf.obj (op ⊤)) (β : ℂ →+* Z.presheaf.obj (op ⊤)) : Prop :=
  ∀ c, f.hom.c.app (op ⊤) (β c) = α c

private theorem IsCLinearSheafedHom.id {Y : SheafedSpace CommRingCat}
    (α : ℂ →+* Y.presheaf.obj (op ⊤)) :
    IsCLinearSheafedHom (𝟙 Y) α α := fun _ ↦ rfl

private theorem IsCLinearSheafedHom.comp {Y Z W : SheafedSpace CommRingCat}
    {f : Y ⟶ Z} {g : Z ⟶ W} {α : ℂ →+* Y.presheaf.obj (op ⊤)}
    {β : ℂ →+* Z.presheaf.obj (op ⊤)} {γ : ℂ →+* W.presheaf.obj (op ⊤)}
    (hf : IsCLinearSheafedHom f α β) (hg : IsCLinearSheafedHom g β γ) :
    IsCLinearSheafedHom (f ≫ g) α γ := fun c ↦ by
  change f.hom.c.app (op ⊤) (g.hom.c.app (op ⊤) (γ c)) = α c
  rw [hg c, hf c]

private theorem IsCLinearSheafedHom.of_comp {P Q A : SheafedSpace CommRingCat}
    {g : P ⟶ Q} {q : Q ⟶ A} {p : P ⟶ A} (hfac : g ≫ q = p)
    {αP : ℂ →+* P.presheaf.obj (op ⊤)} {αQ : ℂ →+* Q.presheaf.obj (op ⊤)}
    {α : ℂ →+* A.presheaf.obj (op ⊤)} (hp : IsCLinearSheafedHom p αP α)
    (hq : IsCLinearSheafedHom q αQ α) : IsCLinearSheafedHom g αP αQ := fun c ↦ by
  subst p
  rw [← hp c]
  change g.hom.c.app (op ⊤) (αQ c) =
    g.hom.c.app (op ⊤) (q.hom.c.app (op ⊤) (α c))
  rw [hq c]

private theorem IsCLinearSheafedHom.iso_inv {Y Z : SheafedSpace CommRingCat}
    (e : Y ≅ Z) {α : ℂ →+* Y.presheaf.obj (op ⊤)} {β : ℂ →+* Z.presheaf.obj (op ⊤)}
    (h : IsCLinearSheafedHom e.hom α β) : IsCLinearSheafedHom e.inv β α :=
  IsCLinearSheafedHom.of_comp e.inv_hom_id (IsCLinearSheafedHom.id β) h

private def sheafedResAlgMap (Y : SheafedSpace CommRingCat)
    (α : ℂ →+* Y.presheaf.obj (op ⊤)) (U : Opens Y) :
    ℂ →+* (Y.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp α

private theorem isCLinearSheafedHom_ofRestrict (Y : SheafedSpace CommRingCat)
    (α : ℂ →+* Y.presheaf.obj (op ⊤)) (U : Opens Y) :
    IsCLinearSheafedHom (Y.ofRestrict U.isOpenEmbedding) (sheafedResAlgMap Y α U) α := by
  intro c
  change (Y.presheaf.map _).hom (α c) = (Y.presheaf.map _).hom (α c)
  congr 2

private theorem isoOfSheafedSpaceIso_isCLinear {Y Z : LocallyRingedSpace}
    (e : Y.toSheafedSpace ≅ Z.toSheafedSpace)
    {α : ℂ →+* Y.presheaf.obj (op ⊤)} {β : ℂ →+* Z.presheaf.obj (op ⊤)}
    (h : IsCLinearSheafedHom e.hom α β) :
    ComplexAnalytic.IsCLinearHom (LocallyRingedSpace.isoOfSheafedSpaceIso e).hom α β :=
  h

namespace HolomorphicManifold

variable (ι : Type) [Fintype ι] (M : Type) [TopologicalSpace M] [ChartedSpace (ι → ℂ) M]

/-- The sheaf of analytic complex-valued maps on a complex manifold. -/
def sheafToTypes : TopCat.Sheaf (Type) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := 𝓘(ℂ, ι → ℂ))
    (I' := 𝓘(ℂ)) ω).sheaf M ℂ

instance sectionCommRing (U : (Opens (TopCat.of M))ᵒᵖ) :
    CommRing ((sheafToTypes ι M).presheaf.obj U) :=
  inferInstanceAs <| CommRing C^ω⟮𝓘(ℂ, ι → ℂ), (unop U : Opens M); ℂ⟯

/-- The presheaf of analytic complex-valued maps on a complex manifold. -/
def presheaf : TopCat.Presheaf CommRingCat (TopCat.of M) where
  obj U := CommRingCat.of ((sheafToTypes ι M).presheaf.obj U)
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom 𝓘(ℂ, ι → ℂ) 𝓘(ℂ) ℂ <|
      CategoryTheory.leOfHom h.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf of analytic complex-valued maps on a complex manifold. -/
def sheaf : TopCat.Sheaf CommRingCat (TopCat.of M) where
  obj := presheaf ι M
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (sheafToTypes ι M).property

/-- A complex manifold with its sheaf of analytic functions. -/
def sheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of M
  presheaf := presheaf (ι := ι) (M := M)
  IsSheaf := (sheaf (ι := ι) (M := M)).property

variable {ι κ : Type} [Fintype ι] [Fintype κ] {M P : Type}
  [TopologicalSpace M] [ChartedSpace (ι → ℂ) M]
  [TopologicalSpace P] [ChartedSpace (κ → ℂ) P]

/-- Analyticity into an open submanifold can be checked after its subtype inclusion. -/
lemma contMDiffAt_subtypeVal_comp_iff_omega {V : Opens P} (f : M → V) (x : M) :
    ContMDiffAt 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω
        (Subtype.val ∘ f) x ↔
      ContMDiffAt 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω f x := by
  exact ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f Set.univ x

/-- Analyticity into an open submanifold can be checked after its subtype inclusion. -/
lemma contMDiff_subtypeVal_comp_iff_omega {V : Opens P} (f : M → V) :
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω
        (Subtype.val ∘ f) ↔
      ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω f := by
  exact forall_congr' fun x ↦ contMDiffAt_subtypeVal_comp_iff_omega f x

/-- An analytic map pulls analytic functions back. -/
def sheafHom (f : M → P)
    (hf : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω f) :
    sheaf (ι := κ) (M := P) ⟶
      (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
        (sheaf (ι := ι) (M := M)) where
  hom.app U := CommRingCat.ofHom
    { toFun := fun (g : C^ω⟮𝓘(ℂ, κ → ℂ), (unop U : Opens P); ℂ⟯) ↦
        ⟨g ∘ (fun x ↦ ⟨f x, TopologicalSpace.Opens.mem_map.mp x.2⟩), by
          apply ContMDiff.comp (I' := 𝓘(ℂ, κ → ℂ)) g.2
          apply (contMDiff_subtypeVal_comp_iff_omega _).mp
          exact fun x ↦ contMDiffAt_subtype_iff.mpr (hf x)⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  hom.naturality U V i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro g
    apply ContMDiffMap.ext
    intro x
    rfl

/-- An analytic map gives a morphism of holomorphic sheafed spaces. -/
def map (f : M → P)
    (hf : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω f) :
    sheafedSpace (ι := ι) (M := M) ⟶ sheafedSpace (ι := κ) (M := P) :=
  InducedCategory.homMk
    { base := TopCat.ofHom ⟨f, hf.continuous⟩
      c := (sheafHom f hf).hom }

theorem map_congr {f g : M → P}
    (hf : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω f)
    (hg : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω g) (hfg : f = g) :
    map f hf = map g hg := by
  subst g
  rfl

theorem map_id (ι : Type) [Fintype ι] (M : Type) [TopologicalSpace M]
    [ChartedSpace (ι → ℂ) M] :
    map (ι := ι) (κ := ι) (M := M) (P := M) id contMDiff_id = 𝟙 _ :=
  rfl

theorem map_comp {τ : Type} [Fintype τ] {Q : Type} [TopologicalSpace Q]
    [ChartedSpace (τ → ℂ) Q]
    {f : M → P} (hf : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω f)
    {g : P → Q} (hg : ContMDiff 𝓘(ℂ, κ → ℂ) 𝓘(ℂ, τ → ℂ) ω g) :
    map (g ∘ f) (hg.comp hf) = map f hf ≫ map g hg :=
  rfl

private theorem map_isCLinear (f : M → P)
    (hf : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω f) :
    IsCLinearSheafedHom (map f hf) ContMDiffMap.C ContMDiffMap.C := by
  intro c
  rfl

/-- A biholomorphism gives an isomorphism of holomorphic sheafed spaces. -/
def isoOfHomeomorph (h : M ≃ₜ P)
    (hf : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω h)
    (hinv : ContMDiff 𝓘(ℂ, κ → ℂ) 𝓘(ℂ, ι → ℂ) ω h.symm) :
    sheafedSpace (ι := ι) (M := M) ≅ sheafedSpace (ι := κ) (M := P) where
  hom := map h hf
  inv := map h.symm hinv
  hom_inv_id := by
    rw [← map_comp]
    exact (map_congr _ _ (funext h.left_inv)).trans (map_id ι M)
  inv_hom_id := by
    rw [← map_comp]
    exact (map_congr _ _ (funext h.right_inv)).trans (map_id κ P)

private theorem isoOfHomeomorph_isCLinear (h : M ≃ₜ P)
    (hf : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, κ → ℂ) ω h)
    (hinv : ContMDiff 𝓘(ℂ, κ → ℂ) 𝓘(ℂ, ι → ℂ) ω h.symm) :
    IsCLinearSheafedHom (isoOfHomeomorph h hf hinv).hom
      ContMDiffMap.C ContMDiffMap.C :=
  map_isCLinear h hf

instance (U : Opens M) : SheafedSpace.IsOpenImmersion
    (map (ι := ι) (κ := ι) (M := U) (P := M) Subtype.val
      (contMDiff_subtype_val (I := 𝓘(ℂ, ι → ℂ)))) where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ Subtype.ext ?_, fun ⟨g, hg⟩ ↦ ?_⟩
    · ext ⟨x, y, hy, rfl⟩
      exact congr($(hab).1 ⟨y, ⟨y, hy, rfl⟩⟩)
    · let a : TopCat.of U ⟶ TopCat.of M :=
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      have ha : IsOpenEmbedding a.hom := U.isOpenEmbedding'
      let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
      let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        U.isOpenEmbedding'.homeomorphOfSubsetRange <| Set.image_subset_range _ V.1
      refine ⟨⟨g ∘ b.symm, ContMDiff.comp hg ?_⟩, Subtype.ext <| funext fun _ ↦ ?_⟩
      · refine (contMDiff_subtypeVal_comp_iff_omega _).mp ?_
        rw [← contMDiff_subtypeVal_comp_iff_omega]
        convert! contMDiff_subtype_val
        ext x
        exact congr($(b.apply_symm_apply x).1)
      · change g _ = _
        congr
        apply b.symm_apply_apply

/-- Restriction to an open subset agrees with its analytic manifold sheaf. -/
def restrictSheafedSpaceIso (U : Opens M) :
    (sheafedSpace (ι := ι) (M := M)).restrict U.isOpenEmbedding ≅
      sheafedSpace (ι := ι) (M := U) := by
  exact (SheafedSpace.IsOpenImmersion.isoRestrict
    (map (ι := ι) (κ := ι) (M := U) (P := M) Subtype.val
      (contMDiff_subtype_val (I := 𝓘(ℂ, ι → ℂ))))).symm

set_option backward.isDefEq.respectTransparency false in
private theorem restrictSheafedSpaceIso_isCLinear (U : Opens M) :
    IsCLinearSheafedHom (restrictSheafedSpaceIso (ι := ι) (M := M) U).hom
      (sheafedResAlgMap (sheafedSpace (ι := ι) (M := M)) ContMDiffMap.C U)
      ContMDiffMap.C := by
  exact IsCLinearSheafedHom.of_comp
    (SheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict _)
    (isCLinearSheafedHom_ofRestrict
      (sheafedSpace (ι := ι) (M := M)) ContMDiffMap.C U)
    (map_isCLinear Subtype.val (contMDiff_subtype_val (I := 𝓘(ℂ, ι → ℂ))))

end HolomorphicManifold

namespace Euclidean

variable {n : ℕ} {U : Opens (Fin n → ℂ)}

/-- On an open subset of `ℂ^n`, Mathlib's analytic manifold maps are Oka-analytic. -/
theorem contMDiff_omega_iff_okaAnalytic (f : U → ℂ) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω f ↔ OkaAnalytic f := by
  rw [okaAnalytic_iff]
  constructor
  · intro hf x hx
    let xU : U := ⟨x, hx⟩
    have hrestrict :
        (fun y : U ↦ Function.extend Subtype.val f 0 y) = f := by
      funext y
      exact Subtype.val_injective.extend_apply
        (f := (Subtype.val : U → Fin n → ℂ)) f 0 y
    have hmanifold : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω
        (Function.extend Subtype.val f 0) x := by
      apply (contMDiffAt_subtype_iff (U := U) (x := xU)).mp
      simpa only [hrestrict] using hf xU
    exact hmanifold.contDiffAt.analyticAt
  · intro hf x
    have hambient : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ω
        (Function.extend Subtype.val f 0) x :=
      (hf x x.2).contDiffAt.contMDiffAt
    have hrestrict := (contMDiffAt_subtype_iff (U := U) (x := x)).mpr hambient
    simpa only [Subtype.val_injective.extend_apply] using hrestrict

/-- Analytic manifold maps and Oka functions give the same section ring on a Euclidean open. -/
def contMDiffMapRingEquivOkaRing (U : Opens (Fin n → ℂ)) :
    C^ω⟮𝓘(ℂ, Fin n → ℂ), U; ℂ⟯ ≃+* OkaRing U where
  toFun f := ⟨f, (contMDiff_omega_iff_okaAnalytic f).mp f.2⟩
  invFun f := ⟨f.toFun, (contMDiff_omega_iff_okaAnalytic f.toFun).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The presheaf of analytic manifold maps on a finite-dimensional complex coordinate space. -/
def holomorphicPresheaf (n : ℕ) :
    TopCat.Presheaf CommRingCat (TopCat.of (Fin n → ℂ)) where
  obj U := CommRingCat.of C^ω⟮𝓘(ℂ, Fin n → ℂ), (unop U : Opens (Fin n → ℂ)); ℂ⟯
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) ℂ <|
      CategoryTheory.leOfHom h.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Oka's holomorphic presheaf is the analytic-manifold presheaf. -/
def holomorphicPresheafIsoOka (n : ℕ) :
    holomorphicPresheaf n ≅ okaCommPresheaf (Fin n) :=
  NatIso.ofComponents
    (fun U ↦ (contMDiffMapRingEquivOkaRing (unop U)).toCommRingCatIso)
    (fun _ ↦ by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro f
      rfl)

/-- The analytic-manifold and Oka sheafed spaces on a coordinate space are isomorphic. -/
def holomorphicSheafedSpaceIsoOka (n : ℕ) :
    HolomorphicManifold.sheafedSpace (ι := Fin n) (M := Fin n → ℂ) ≅
      (complexSpace (Fin n)).toSheafedSpace :=
  SheafedSpace.isoMk <|
    PresheafedSpace.isoOfComponents (Iso.refl _) (holomorphicPresheafIsoOka n)

private theorem holomorphicSheafedSpaceIsoOka_isCLinear (n : ℕ) :
    IsCLinearSheafedHom (holomorphicSheafedSpaceIsoOka n).hom ContMDiffMap.C
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (Fin n → ℂ)))) := by
  intro c
  rfl

/-- The Euclidean sheaf comparison restricted to an open subset. -/
def restrictHolomorphicSheafedSpaceIsoOka (V : Opens (Fin n → ℂ)) :
    (HolomorphicManifold.sheafedSpace (ι := Fin n) (M := Fin n → ℂ)).restrict
        V.isOpenEmbedding ≅
      (complexSpace (Fin n)).toSheafedSpace.restrict V.isOpenEmbedding := by
  let f := SheafedSpace.ofRestrict
      (HolomorphicManifold.sheafedSpace (ι := Fin n) (M := Fin n → ℂ))
      V.isOpenEmbedding ≫
    (holomorphicSheafedSpaceIsoOka n).hom
  exact SheafedSpace.IsOpenImmersion.isoRestrict f

set_option backward.isDefEq.respectTransparency false in
private theorem restrictHolomorphicSheafedSpaceIsoOka_isCLinear
    (V : Opens (Fin n → ℂ)) :
    IsCLinearSheafedHom (restrictHolomorphicSheafedSpaceIsoOka V).hom
      (sheafedResAlgMap (HolomorphicManifold.sheafedSpace
        (ι := Fin n) (M := Fin n → ℂ)) ContMDiffMap.C V)
      ((complexSpace (Fin n)).resAlgMap
        (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (Fin n → ℂ)))) V) := by
  exact IsCLinearSheafedHom.of_comp
    (SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict _)
    ((isCLinearSheafedHom_ofRestrict
        (HolomorphicManifold.sheafedSpace (ι := Fin n) (M := Fin n → ℂ))
        ContMDiffMap.C V).comp
      (holomorphicSheafedSpaceIsoOka_isCLinear n))
    (isCLinearSheafedHom_ofRestrict (complexSpace (Fin n)).toSheafedSpace
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (Fin n → ℂ)))) V)

variable {ι κ : Type u} [Fintype ι] [Fintype κ]

/-- The coordinate homeomorphism underlying a continuous linear equivalence. -/
def complexSpaceBaseIso (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) :
    TopCat.of (ι → ℂ) ≅ TopCat.of (κ → ℂ) :=
  TopCat.isoOfHomeo φ.toHomeomorph

/-- Pull Oka functions through a continuous linear coordinate equivalence. -/
def OkaRing.reindex (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (V : Opens (κ → ℂ)) :
    OkaRing ((Opens.map (complexSpaceBaseIso φ).hom).obj V) ≃+* OkaRing V where
  toFun f := OkaRing.mk
    (fun y ↦ f.toFun _ ⟨φ.symm y, by
      change φ (φ.symm y) ∈ V
      simp [y.2]⟩)
    (f.2.comp_continuousLinearMap
      (φ.symm : (κ → ℂ) →L[ℂ] (ι → ℂ)) (fun y hy ↦ by
        change φ (φ.symm y) ∈ V
        simp [hy]))
  invFun g := OkaRing.mk
    (fun x ↦ g.toFun _ ⟨φ x, x.2⟩)
    (g.2.comp_continuousLinearMap
      (φ : (ι → ℂ) →L[ℂ] (κ → ℂ)) (fun x hx ↦ hx))
  left_inv f := by
    ext x
    exact congrArg (f.toFun _) (Subtype.ext (φ.symm_apply_apply (x : ι → ℂ)))
  right_inv g := by
    ext y
    exact congrArg (g.toFun _) (Subtype.ext (φ.apply_symm_apply (y : κ → ℂ)))
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The Oka presheaves are invariant under a continuous linear coordinate equivalence. -/
def complexSpacePresheafIso (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) :
    (complexSpaceBaseIso φ).hom _* (complexSpace ι).presheaf ≅
      (complexSpace κ).presheaf :=
  NatIso.ofComponents
    (fun V ↦ (OkaRing.reindex φ V.unop).toCommRingCatIso)
    (fun {_ _} _ ↦ by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro f
      rfl)

/-- Oka sheafed spaces are invariant under a continuous linear coordinate equivalence. -/
def complexSpaceSheafedSpaceIso (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) :
    (complexSpace ι).toSheafedSpace ≅ (complexSpace κ).toSheafedSpace :=
  SheafedSpace.isoMk <|
    PresheafedSpace.isoOfComponents (complexSpaceBaseIso φ) (complexSpacePresheafIso φ)

/-- Oka locally ringed spaces are invariant under a continuous linear coordinate equivalence. -/
def complexSpaceIso (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) :
    complexSpace ι ≅ complexSpace κ :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (complexSpaceSheafedSpaceIso φ)

/-- A linear change of complex coordinates preserves constant functions. -/
theorem complexSpaceIso_isCLinear (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) :
    ComplexAnalytic.IsCLinearHom (complexSpaceIso φ).hom
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ι → ℂ))))
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (κ → ℂ)))) := by
  intro c
  rfl

/-- Coordinate equivalences identify the corresponding canonical open restrictions. -/
def canonicalRestrictedComplexSpaceIso (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ))
    (U : Opens (ι → ℂ)) :
    (complexSpace ι).restrict U.isOpenEmbedding ≅
      (complexSpace κ).restrict (φ.opensCongr U).isOpenEmbedding := by
  let f : (complexSpace ι).restrict U.isOpenEmbedding ⟶ complexSpace κ :=
    (complexSpace ι).ofRestrict U.isOpenEmbedding ≫ (complexSpaceIso φ).hom
  let g : (complexSpace κ).restrict (φ.opensCongr U).isOpenEmbedding ⟶ complexSpace κ :=
    (complexSpace κ).ofRestrict (φ.opensCongr U).isOpenEmbedding
  haveI : LocallyRingedSpace.IsOpenImmersion f := inferInstance
  haveI : LocallyRingedSpace.IsOpenImmersion g := inferInstance
  let hf : PresheafedSpace.IsOpenImmersion f.toHom := by
    change LocallyRingedSpace.IsOpenImmersion f
    infer_instance
  let hg : PresheafedSpace.IsOpenImmersion g.toHom := by
    change LocallyRingedSpace.IsOpenImmersion g
    infer_instance
  have hrange : Set.range f.base = Set.range g.base := by
    change Set.range (fun x : U ↦ φ x) =
      Set.range (Subtype.val : φ.opensCongr U → κ → ℂ)
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨φ x, ?_⟩, rfl⟩
      simp [x.2]
    · rintro ⟨y, rfl⟩
      refine ⟨⟨φ.symm y, ?_⟩, ?_⟩
      · simpa using y.2
      · simp
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq f g hrange

/-- The restricted coordinate comparison preserves constant functions. -/
theorem canonicalRestrictedComplexSpaceIso_isCLinear
    (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (U : Opens (ι → ℂ)) :
    ComplexAnalytic.IsCLinearHom (canonicalRestrictedComplexSpaceIso φ U).hom
      ((complexSpace ι).resAlgMap
        (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ι → ℂ)))) U)
      ((complexSpace κ).resAlgMap
        (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (κ → ℂ)))) (φ.opensCongr U)) := by
  exact ComplexAnalytic.IsCLinearHom.of_comp
    (by simp [canonicalRestrictedComplexSpaceIso])
    ((ComplexAnalytic.isCLinearHom_ofRestrict (complexSpace ι) _ U).comp
      (complexSpaceIso_isCLinear φ))
    (ComplexAnalytic.isCLinearHom_ofRestrict (complexSpace κ) _ (φ.opensCongr U))

end Euclidean

/-- The project-specific holomorphic sheaf is the analytic-manifold sheaf. -/
def holomorphicSheafedSpaceIso :
    (holomorphicLocallyRingedSpace X d).toSheafedSpace ≅
      HolomorphicManifold.sheafedSpace (ι := Fin d) (M := ComplexPoint X) :=
  Iso.refl _

/-- The source of the chosen analytic chart at `z`. -/
def localChartSource (z : ComplexPoint X) : Opens (ComplexPoint X) :=
  ⟨(localChart X d z).source, (localChart X d z).open_source⟩

/-- The target of the chosen analytic chart at `z`. -/
def localChartTarget (z : ComplexPoint X) : Opens (Fin d → ℂ) :=
  ⟨(localChart X d z).target, (localChart X d z).open_target⟩

local instance localChartSourceChartedSpace (z : ComplexPoint X) :
    ChartedSpace (Fin d → ℂ) (localChartSource X d z) :=
  TopologicalSpace.Opens.instChartedSpace _

local instance localChartTargetChartedSpace (z : ComplexPoint X) :
    ChartedSpace (Fin d → ℂ) (localChartTarget X d z) :=
  TopologicalSpace.Opens.instChartedSpace _

/-- The homeomorphism between the source and target of the chosen chart. -/
def localChartHomeomorph (z : ComplexPoint X) :
    localChartSource X d z ≃ₜ localChartTarget X d z :=
  (localChart X d z).toHomeomorphSourceTarget

/-- The holomorphic sheaf restricted to a chart source, with the source type fixed explicitly. -/
def localChartSourceSheafedSpaceIso (z : ComplexPoint X) :
    ((holomorphicLocallyRingedSpace X d).restrict
        (localChartSource X d z).isOpenEmbedding).toSheafedSpace ≅
      HolomorphicManifold.sheafedSpace
        (ι := Fin d) (M := localChartSource X d z) :=
  HolomorphicManifold.restrictSheafedSpaceIso
    (ι := Fin d) (M := ComplexPoint X) (localChartSource X d z)

private theorem localChartSourceSheafedSpaceIso_isCLinear (z : ComplexPoint X) :
    IsCLinearSheafedHom (localChartSourceSheafedSpaceIso X d z).hom
      (sheafedResAlgMap (holomorphicLocallyRingedSpace X d).toSheafedSpace
        ContMDiffMap.C (localChartSource X d z)) ContMDiffMap.C :=
  HolomorphicManifold.restrictSheafedSpaceIso_isCLinear
    (ι := Fin d) (M := ComplexPoint X) (localChartSource X d z)

/-- The chosen chart is analytic on its source. -/
theorem contMDiff_localChartHomeomorph (z : ComplexPoint X) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (localChartHomeomorph X d z) := by
  rw [← HolomorphicManifold.contMDiff_subtypeVal_comp_iff_omega]
  intro y
  change ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
    (fun x : localChartSource X d z ↦ localChart X d z x) y
  rw [contMDiffAt_subtype_iff]
  exact (contMDiffOn_chart (I := 𝓘(ℂ, Fin d → ℂ)) (x := z) y y.2).contMDiffAt
    ((localChart X d z).open_source.mem_nhds y.2)

/-- The inverse chosen chart is analytic on its target. -/
theorem contMDiff_localChartHomeomorph_symm (z : ComplexPoint X) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (localChartHomeomorph X d z).symm := by
  rw [← HolomorphicManifold.contMDiff_subtypeVal_comp_iff_omega]
  intro y
  change ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
    (fun x : localChartTarget X d z ↦ (localChart X d z).symm x) y
  rw [contMDiffAt_subtype_iff]
  exact (contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin d → ℂ)) (x := z) y y.2).contMDiffAt
    ((localChart X d z).open_target.mem_nhds y.2)

/-- The chosen chart identifies the restricted holomorphic sheaf with Oka's sheaf. -/
def localChartSheafedSpaceIsoFin (z : ComplexPoint X) :
    ((holomorphicLocallyRingedSpace X d).restrict
        (localChartSource X d z).isOpenEmbedding).toSheafedSpace ≅
      ((complexSpace (Fin d)).restrict
        (localChartTarget X d z).isOpenEmbedding).toSheafedSpace :=
  localChartSourceSheafedSpaceIso X d z ≪≫
    HolomorphicManifold.isoOfHomeomorph
      (localChartHomeomorph X d z)
      (contMDiff_localChartHomeomorph (X := X) (d := d) z)
      (contMDiff_localChartHomeomorph_symm (X := X) (d := d) z) ≪≫
    (HolomorphicManifold.restrictSheafedSpaceIso
      (ι := Fin d) (M := Fin d → ℂ) (localChartTarget X d z)).symm ≪≫
    Euclidean.restrictHolomorphicSheafedSpaceIsoOka (localChartTarget X d z)

private theorem localChartSheafedSpaceComposite_isCLinear (z : ComplexPoint X) :
    IsCLinearSheafedHom
      ((localChartSourceSheafedSpaceIso X d z).hom ≫
        ((HolomorphicManifold.isoOfHomeomorph
            (ι := Fin d) (κ := Fin d) (M := localChartSource X d z)
            (P := localChartTarget X d z)
            (localChartHomeomorph X d z)
            (contMDiff_localChartHomeomorph X d z)
            (contMDiff_localChartHomeomorph_symm X d z)).hom ≫
          ((HolomorphicManifold.restrictSheafedSpaceIso
              (ι := Fin d) (M := Fin d → ℂ) (localChartTarget X d z)).symm ≪≫
            Euclidean.restrictHolomorphicSheafedSpaceIsoOka
              (n := d) (localChartTarget X d z)).hom))
      (sheafedResAlgMap (holomorphicLocallyRingedSpace X d).toSheafedSpace
        ContMDiffMap.C (localChartSource X d z))
      ((complexSpace (Fin d)).resAlgMap
        (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (Fin d → ℂ))))
        (localChartTarget X d z)) := by
  have hsource := localChartSourceSheafedSpaceIso_isCLinear X d z
  have hchart := HolomorphicManifold.isoOfHomeomorph_isCLinear
    (ι := Fin d) (κ := Fin d) (M := localChartSource X d z)
    (P := localChartTarget X d z)
    (localChartHomeomorph X d z)
    (contMDiff_localChartHomeomorph X d z)
    (contMDiff_localChartHomeomorph_symm X d z)
  have htarget := IsCLinearSheafedHom.iso_inv
    (HolomorphicManifold.restrictSheafedSpaceIso
      (ι := Fin d) (M := Fin d → ℂ) (localChartTarget X d z))
    (HolomorphicManifold.restrictSheafedSpaceIso_isCLinear
      (ι := Fin d) (M := Fin d → ℂ) (localChartTarget X d z))
  have hOka := Euclidean.restrictHolomorphicSheafedSpaceIsoOka_isCLinear
    (n := d) (localChartTarget X d z)
  have htail := htarget.comp hOka
  change IsCLinearSheafedHom
    (((HolomorphicManifold.restrictSheafedSpaceIso
      (ι := Fin d) (M := Fin d → ℂ) (localChartTarget X d z)).symm ≪≫
      Euclidean.restrictHolomorphicSheafedSpaceIsoOka
        (localChartTarget X d z)).hom) _ _ at htail
  exact hsource.comp (hchart.comp htail)

/-- The chosen chart gives an isomorphism of locally ringed spaces in `Fin` coordinates. -/
def localChartLocallyRingedSpaceIsoFin (z : ComplexPoint X) :
    (holomorphicLocallyRingedSpace X d).restrict
        (localChartSource X d z).isOpenEmbedding ≅
      (complexSpace (Fin d)).restrict
      (localChartTarget X d z).isOpenEmbedding :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (localChartSheafedSpaceIsoFin X d z)

/-- The chosen chart in `Fin` coordinates preserves constant functions. -/
theorem localChartLocallyRingedSpaceIsoFin_isCLinear (z : ComplexPoint X) :
    ComplexAnalytic.IsCLinearHom (localChartLocallyRingedSpaceIsoFin X d z).hom
      ((holomorphicLocallyRingedSpace X d).resAlgMap ContMDiffMap.C
        (localChartSource X d z))
      ((complexSpace (Fin d)).resAlgMap
        (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (Fin d → ℂ))))
        (localChartTarget X d z)) := by
  apply isoOfSheafedSpaceIso_isCLinear
  change IsCLinearSheafedHom
    ((localChartSourceSheafedSpaceIso X d z).hom ≫
      ((HolomorphicManifold.isoOfHomeomorph
          (ι := Fin d) (κ := Fin d) (M := localChartSource X d z)
          (P := localChartTarget X d z)
          (localChartHomeomorph X d z)
          (contMDiff_localChartHomeomorph X d z)
          (contMDiff_localChartHomeomorph_symm X d z)).hom ≫
        ((HolomorphicManifold.restrictSheafedSpaceIso
          (ι := Fin d) (M := Fin d → ℂ) (localChartTarget X d z)).inv ≫
          (Euclidean.restrictHolomorphicSheafedSpaceIsoOka
            (n := d) (localChartTarget X d z)).hom))) _ _
  exact localChartSheafedSpaceComposite_isCLinear X d z

/-- Relabel `Fin d` coordinates by Oka's `ULift` convention. -/
def finToULiftCoord :
    (Fin d → ℂ) ≃L[ℂ] (ULift.{0} (Fin d) → ℂ) :=
  ((LinearEquiv.funCongrLeft ℂ ℂ
    (Equiv.ulift.{0} (α := Fin d)).symm).toContinuousLinearEquiv).symm

/-- The chosen chart target in Oka's coordinate convention. -/
def localChartTargetULift (z : ComplexPoint X) :
    Opens (ULift.{0} (Fin d) → ℂ) :=
  (finToULiftCoord d).opensCongr (localChartTarget X d z)

/-- The chosen chart gives an isomorphism to an open subspace of Oka's affine space. -/
def localChartLocallyRingedSpaceIso (z : ComplexPoint X) :
    (holomorphicLocallyRingedSpace X d).restrict
        (localChartSource X d z).isOpenEmbedding ≅
      (_root_.complexAffineSpace.{0} d).restrict
        (localChartTargetULift X d z).isOpenEmbedding :=
  localChartLocallyRingedSpaceIsoFin X d z ≪≫
    Euclidean.canonicalRestrictedComplexSpaceIso
      (finToULiftCoord d) (localChartTarget X d z)

set_option backward.isDefEq.respectTransparency false in
/-- The chosen Oka chart preserves constant functions. -/
theorem localChartLocallyRingedSpaceIso_isCLinear (z : ComplexPoint X) :
    ComplexAnalytic.IsCLinearHom (localChartLocallyRingedSpaceIso X d z).hom
      ((holomorphicLocallyRingedSpace X d).resAlgMap ContMDiffMap.C
        (localChartSource X d z))
      (ComplexAnalytic.constantsAlgMap d (localChartTargetULift X d z)) := by
  rw [ComplexAnalytic.constantsAlgMap_eq_resAlgMap]
  change ComplexAnalytic.IsCLinearHom
    ((localChartLocallyRingedSpaceIsoFin X d z).hom ≫
      (Euclidean.canonicalRestrictedComplexSpaceIso
        (finToULiftCoord d) (localChartTarget X d z)).hom) _ _
  exact (localChartLocallyRingedSpaceIsoFin_isCLinear X d z).comp
    (Euclidean.canonicalRestrictedComplexSpaceIso_isCLinear
      (finToULiftCoord d) (localChartTarget X d z))

/-- A locally ringed space is cut out inside itself by the empty family. -/
theorem isCutOutBy_id_empty (Y : LocallyRingedSpace) :
    ComplexAnalytic.IsCutOutBy (𝟙 Y) (fun i : Fin 0 ↦ Fin.elim0 i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using IsClosedEmbedding.id
  · simp
  · intro x
    simp only [LocallyRingedSpace.stalkMap_id]
    exact fun y ↦ ⟨y, rfl⟩
  · intro x
    simp only [LocallyRingedSpace.stalkMap_id, Set.range_eq_empty, Ideal.span_empty]
    ext a
    exact Iff.rfl

/-- A chosen chart neighborhood is an Oka local model. -/
theorem isLocalModel_localChartRestriction (z : ComplexPoint X) :
    ComplexAnalytic.IsLocalModel <|
      (holomorphicLocallyRingedSpace X d).restrict
        (localChartSource X d z).isOpenEmbedding := by
  let V := localChartTargetULift X d z
  let e := localChartLocallyRingedSpaceIso X d z
  refine ⟨d, 0, V, e.hom, Fin.elim0, ?_⟩
  exact (isCutOutBy_id_empty
    ((_root_.complexAffineSpace.{0} d).restrict V.isOpenEmbedding)).comp_iso e

/-- The complex points with their holomorphic functions form an Oka analytic space. -/
def holomorphicAnalyticSpace : ComplexAnalytic.AnalyticSpace where
  toLocallyRingedSpace := holomorphicLocallyRingedSpace X d
  algebraMap := ContMDiffMap.C
  local_model z := by
    let U : OpenNhds z := ⟨localChartSource X d z, mem_localChart_source X d z⟩
    let V := localChartTargetULift X d z
    let e := localChartLocallyRingedSpaceIso X d z
    refine ⟨U, d, 0, V, e.hom, Fin.elim0, ?_, ?_⟩
    · exact (isCutOutBy_id_empty
        ((_root_.complexAffineSpace.{0} d).restrict V.isOpenEmbedding)).comp_iso e
    · exact localChartLocallyRingedSpaceIso_isCLinear X d z

/-- The holomorphic structure sheaf has locally finitely generated relations. -/
theorem holomorphicLocallyRingedSpace_hasLocalRelations :
    (holomorphicLocallyRingedSpace X d).HasLocalRelations := by
  refine LocallyRingedSpace.hasLocalRelations_of_openCover
    (fun z : ComplexPoint X ↦ localChartSource X d z)
    (fun z ↦ ⟨z, mem_localChart_source X d z⟩) ?_
  intro z
  exact LocallyRingedSpace.HasLocalRelations.hasLocalRelationsOn _
    (ComplexAnalytic.IsLocalModel.hasLocalRelations
      (isLocalModel_localChartRestriction X d z))

/-- The holomorphic structure sheaf on the complex-point space is coherent. -/
theorem holomorphicLocallyRingedSpace_isCoherentStructureSheaf :
    (holomorphicLocallyRingedSpace X d).IsCoherentStructureSheaf :=
  LocallyRingedSpace.isCoherentStructureSheaf_of_hasLocalRelations
    (holomorphicLocallyRingedSpace_hasLocalRelations X d)

end AlgebraicGeometry.ComplexPoint
