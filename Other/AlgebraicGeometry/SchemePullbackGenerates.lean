/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SchemePullbackSection

/-!
# The inverse image of a generating section generates

If `g : Γ(M, U)` generates a sheaf of modules `M` on an open `U` of a scheme `Y`, then its
inverse image `pullbackSection f M U g` generates `(Scheme.Modules.pullback f).obj M` on
`f ⁻¹ᵁ U`, for any morphism of schemes `f : X ⟶ Y`.

The proof is the scheme analogue of
[`Other/AlgebraicGeometry/AnalytificationGenerates.lean`](AnalytificationGenerates.lean); see the
module docstring there for the argument.  No base-change theorem is needed: the two sheaves

* `starUnitSheaf A : V ↦ Γ(X, A ⨯ V)` and
* `starModuleSheaf A N : V ↦ Γ(N, A ⨯ V)`

are pushforwards along `Over.star A`, the coefficient morphism `coeffHom` is adjoint to a map
`(pullback f).obj M ⟶ starUnitSheaf (f ⁻¹ᵁ U)`, and the triangle identity turns the algebraic
identity `hg.coeff W t • g|_{W ⊓ U} = t|_{W ⊓ U}` into a two-sided inverse for multiplication by
the inverse image of `g`.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pushforward along `Over.star A`. -/
abbrev starPushforward (A : X.Opens) :
    SheafOfModules.{u} (X.ringCatSheaf.over A) ⥤ X.Modules :=
  SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver A)

/-- The sheaf `V ↦ Γ(X, A ⨯ V)`. -/
abbrev starUnitSheaf (A : X.Opens) : X.Modules :=
  (starPushforward (X := X) A).obj (SheafOfModules.unit (X.ringCatSheaf.over A))

/-- The sheaf `V ↦ Γ(N, A ⨯ V)`. -/
abbrev starModuleSheaf (A : X.Opens) (N : X.Modules) : X.Modules :=
  (starPushforward (X := X) A).obj (N.over A)

lemma preimage_inf (U W : Y.Opens) : f ⁻¹ᵁ (W ⊓ U) = f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ U := rfl

lemma prod_le_preimage_inf (U W : Y.Opens) :
    (f ⁻¹ᵁ U ⨯ f ⁻¹ᵁ W : X.Opens) ≤ f ⁻¹ᵁ (W ⊓ U) := by
  rw [preimage_inf]
  exact le_inf (leOfHom Limits.prod.snd) (leOfHom Limits.prod.fst)

/-- Monotonicity of `A ⨯ -`. -/
lemma prod_mono (A : X.Opens) {V V' : X.Opens} (h : V' ≤ V) :
    (A ⨯ V' : X.Opens) ≤ (A ⨯ V : X.Opens) :=
  leOfHom (Limits.prod.map (𝟙 A) (homOfLE h))

section SmulSection

variable {N : X.Modules} {A : X.Opens} (s : Γ(N, A))

/-- The compatible family of restrictions of `s`. -/
def smulSectionFamily : (N.over A).sections :=
  PresheafOfModules.sectionsMk (fun Z => resSection N (leOfHom Z.unop.hom) s)
    (fun _ _ _ => resSection_resSection _ _ s)

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by `s`, as a morphism of sheaves of modules on the site over `A`. -/
def smulSectionHom : SheafOfModules.unit (X.ringCatSheaf.over A) ⟶ N.over A :=
  (SheafOfModules.unitHomEquiv (N.over A)).symm (smulSectionFamily s)

lemma smulSectionHom_val_app (Z : Over A) (r : Γ(X, Z.left)) :
    (smulSectionHom s).val.app (op Z) r = r • resSection N (leOfHom Z.hom) s := rfl

set_option backward.isDefEq.respectTransparency false in
variable (N A) in
/-- The canonical map `Γ(N, V) → Γ(N, A ⨯ V)`. -/
def toStarModuleSheaf : N ⟶ starModuleSheaf A N :=
  (SheafOfModules.overPushforwardOverAdj.{u} A).unit.app N

lemma toStarModuleSheaf_val_app (V : X.Opens) (m : Γ(N, V)) :
    (toStarModuleSheaf N A).val.app (op V) m =
      resSection N (leOfHom (Limits.prod.snd : (A ⨯ V : X.Opens) ⟶ V)) m := rfl

end SmulSection

section

variable {M : Y.Modules} {U : Y.Opens} {g : Γ(M, U)}

/-- The inverse image of the coefficient of a section with respect to a generating section. -/
def pullbackCoeff (hg : Generates g) (W : Y.Opens) (t : Γ(M, W)) :
    Γ(X, (f ⁻¹ᵁ U ⨯ f ⁻¹ᵁ W : X.Opens)) :=
  resRing (prod_le_preimage_inf f U W) (pullbackFunction f (W ⊓ U) (hg.coeff W t))

lemma pullbackCoeff_apply (hg : Generates g) (W : Y.Opens) (t : Γ(M, W)) :
    pullbackCoeff f hg W t =
      resRing (prod_le_preimage_inf f U W) (pullbackFunction f (W ⊓ U) (hg.coeff W t)) := rfl

lemma pullbackCoeff_add (hg : Generates g) (W : Y.Opens) (t t' : Γ(M, W)) :
    pullbackCoeff f hg W (t + t') = pullbackCoeff f hg W t + pullbackCoeff f hg W t' := by
  rw [pullbackCoeff_apply, pullbackCoeff_apply, pullbackCoeff_apply, hg.coeff_add,
    pullbackFunction_add, resRing_add]

lemma pullbackCoeff_smul (hg : Generates g) (W : Y.Opens) (r : Γ(Y, W)) (t : Γ(M, W)) :
    pullbackCoeff f hg W (r • t) =
      resRing (leOfHom (Limits.prod.snd : (f ⁻¹ᵁ U ⨯ f ⁻¹ᵁ W : X.Opens) ⟶ f ⁻¹ᵁ W))
        (pullbackFunction f W r) * pullbackCoeff f hg W t := by
  rw [pullbackCoeff_apply, pullbackCoeff_apply, hg.coeff_smul, smul_eq_mul,
    pullbackFunction_mul, resRing_mul]
  congr 1
  rw [pullbackFunction_res, resRing_resRing]

lemma pullbackCoeff_res (hg : Generates g) {W W' : Y.Opens} (h : W' ≤ W) (t : Γ(M, W)) :
    pullbackCoeff f hg W' (resSection M h t) =
      resRing (prod_mono (f ⁻¹ᵁ U) (preimage_mono f h)) (pullbackCoeff f hg W t) := by
  rw [pullbackCoeff_apply, pullbackCoeff_apply, hg.coeff_res]
  rw [show (Y.presheaf.map (homOfLE (inf_le_inf_right U h)).op) (hg.coeff W t) =
      resRing (inf_le_inf_right U h) (hg.coeff W t) from rfl,
    pullbackFunction_res, resRing_resRing, resRing_resRing]

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of sheaves of modules given by the inverse-image coefficient. -/
def coeffHom (hg : Generates g) :
    M ⟶ (Scheme.Modules.pushforward f).obj (starUnitSheaf (f ⁻¹ᵁ U)) :=
  SheafOfModules.Hom.mk
    { app := fun W => ModuleCat.homMk
        (AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun t => pullbackCoeff f hg W.unop t)
          (fun t t' => pullbackCoeff_add f hg W.unop t t')))
        (fun r => by
          ext t
          exact (pullbackCoeff_smul f hg W.unop r t).symm)
      naturality := fun {W W'} i => by
        ext x
        exact pullbackCoeff_res f hg (leOfHom i.unop) x }

lemma coeffHom_val_app (hg : Generates g) (W : Y.Opens) (t : Γ(M, W)) :
    (coeffHom f hg).val.app (op W) t = pullbackCoeff f hg W t := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The adjoint morphism `f^* M ⟶ starUnitSheaf (f ⁻¹ᵁ U)`. -/
def pullbackCoeffHom (hg : Generates g) :
    (Scheme.Modules.pullback f).obj M ⟶ starUnitSheaf (f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M
    (starUnitSheaf (f ⁻¹ᵁ U))).symm (coeffHom f hg)
set_option backward.isDefEq.respectTransparency false in

lemma pullbackCoeffHom_pullbackSection (hg : Generates g) (W : Y.Opens) (t : Γ(M, W)) :
    (pullbackCoeffHom f hg).val.app (op (f ⁻¹ᵁ W)) (pullbackSection f M W t) =
      pullbackCoeff f hg W t := by
  have h : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map (pullbackCoeffHom f hg) = coeffHom f hg := by
    have h0 : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M
        (starUnitSheaf (f ⁻¹ᵁ U)) (pullbackCoeffHom f hg) = coeffHom f hg :=
      Equiv.apply_symm_apply _ _
    rw [Adjunction.homEquiv_unit] at h0
    exact h0
  exact congrArg
    (fun φ : M ⟶ (Scheme.Modules.pushforward f).obj (starUnitSheaf (f ⁻¹ᵁ U)) =>
      ConcreteCategory.hom (SheafOfModules.Hom.val φ |>.app (op W)) t) h

lemma smul_pullbackSection_key (hg : Generates g) (W : Y.Opens) (t : Γ(M, W)) :
    pullbackCoeff f hg W t •
        resSection ((Scheme.Modules.pullback f).obj M)
          (leOfHom (Limits.prod.fst : (f ⁻¹ᵁ U ⨯ f ⁻¹ᵁ W : X.Opens) ⟶ f ⁻¹ᵁ U))
          (pullbackSection f M U g) =
      resSection ((Scheme.Modules.pullback f).obj M)
        (leOfHom (Limits.prod.snd : (f ⁻¹ᵁ U ⨯ f ⁻¹ᵁ W : X.Opens) ⟶ f ⁻¹ᵁ W))
        (pullbackSection f M W t) := by
  have hbase := pullbackSection_smul_res f M
    (inf_le_right : W ⊓ U ≤ U) (inf_le_left : W ⊓ U ≤ W)
    (hg.coeff W t) g t (hg.coeff_smul_eq W t)
  have h2 := congrArg (resSection ((Scheme.Modules.pullback f).obj M)
    (prod_le_preimage_inf f U W)) hbase
  rw [resSection_smul, resSection_resSection, resSection_resSection] at h2
  exact h2
set_option backward.isDefEq.respectTransparency false in

theorem pullbackCoeffHom_comp_smulSectionHom (hg : Generates g) :
    pullbackCoeffHom f hg ≫ (starPushforward (X := X) (f ⁻¹ᵁ U)).map
        (smulSectionHom (pullbackSection f M U g)) =
      toStarModuleSheaf ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ (fun W => ?_)
  ext t
  show ((starPushforward (X := X) (f ⁻¹ᵁ U)).map
      (smulSectionHom (pullbackSection f M U g))).val.app (op (f ⁻¹ᵁ W))
        ((pullbackCoeffHom f hg).val.app (op (f ⁻¹ᵁ W)) (pullbackSection f M W t)) = _
  rw [pullbackCoeffHom_pullbackSection]
  exact smul_pullbackSection_key f hg W t

lemma pullbackCoeff_self (hg : Generates g) : pullbackCoeff f hg U g = 1 := by
  rw [pullbackCoeff_apply, hg.coeff_self, pullbackFunction_one, resRing_one]

/-- Sections of `starUnitSheaf` over `V` are the regular functions on `A ⨯ V`. -/
def starUnitSheafSection {A V : X.Opens} (x : Γ(starUnitSheaf A, V)) :
    Γ(X, (A ⨯ V : X.Opens)) := x

lemma starUnitSheafSection_smul {A V : X.Opens} (r : Γ(X, V))
    (x : Γ(starUnitSheaf A, V)) :
    starUnitSheafSection (r • x) =
      resRing (leOfHom (Limits.prod.snd : (A ⨯ V : X.Opens) ⟶ V)) r *
        starUnitSheafSection x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The inverse image of a generating section generates.** -/
theorem generates_pullbackSection (hg : Generates g) :
    Generates (L := (Scheme.Modules.pullback f).obj M) (pullbackSection f M U g) := by
  intro V hV
  have hVp : V ≤ (f ⁻¹ᵁ U ⨯ V : X.Opens) := leOfHom (Limits.prod.lift (homOfLE hV) (𝟙 V))
  have key : ∀ m : Γ((Scheme.Modules.pullback f).obj M, V),
      starUnitSheafSection ((pullbackCoeffHom f hg).val.app (op V) m) •
          resSection ((Scheme.Modules.pullback f).obj M)
            (leOfHom (Limits.prod.fst : (f ⁻¹ᵁ U ⨯ V : X.Opens) ⟶ f ⁻¹ᵁ U))
            (pullbackSection f M U g) =
        resSection ((Scheme.Modules.pullback f).obj M)
          (leOfHom (Limits.prod.snd : (f ⁻¹ᵁ U ⨯ V : X.Opens) ⟶ V)) m := fun m =>
    congrArg (fun (h : (Scheme.Modules.pullback f).obj M ⟶
        starModuleSheaf (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)) =>
      ConcreteCategory.hom (SheafOfModules.Hom.val h |>.app (op V)) m)
      (pullbackCoeffHom_comp_smulSectionHom f hg)
  have hone : starUnitSheafSection ((pullbackCoeffHom f hg).val.app (op V)
      (resSection ((Scheme.Modules.pullback f).obj M) hV (pullbackSection f M U g))) = 1 := by
    have hnat := PresheafOfModules.naturality_apply (pullbackCoeffHom f hg).val (homOfLE hV).op
      (pullbackSection f M U g)
    rw [pullbackCoeffHom_pullbackSection f hg U g, pullbackCoeff_self] at hnat
    have h3 : (pullbackCoeffHom f hg).val.app (op V)
        (resSection ((Scheme.Modules.pullback f).obj M) hV (pullbackSection f M U g)) =
        resRing (prod_mono (f ⁻¹ᵁ U) hV)
          (1 : Γ(X, ((f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ U) : X.Opens))) := hnat
    rw [h3]
    exact resRing_one (prod_mono (f ⁻¹ᵁ U) hV)
  have hkap : ∀ r : Γ(X, V),
      resRing hVp (starUnitSheafSection ((pullbackCoeffHom f hg).val.app (op V)
        (r • resSection ((Scheme.Modules.pullback f).obj M) hV
          (pullbackSection f M U g)))) = r := by
    intro r
    rw [(pullbackCoeffHom f hg).val.app (op V) |>.hom.map_smul r
      (resSection ((Scheme.Modules.pullback f).obj M) hV (pullbackSection f M U g)),
      starUnitSheafSection_smul, hone, mul_one, resRing_resRing, resRing_rfl]
  constructor
  · intro r r' hrr'
    have hrr2 : r • resSection ((Scheme.Modules.pullback f).obj M) hV
        (pullbackSection f M U g) =
      r' • resSection ((Scheme.Modules.pullback f).obj M) hV (pullbackSection f M U g) := hrr'
    have h1 := hkap r
    rw [hrr2] at h1
    exact h1.symm.trans (hkap r')
  · intro m
    refine ⟨resRing hVp
      (starUnitSheafSection ((pullbackCoeffHom f hg).val.app (op V) m)), ?_⟩
    have h2 := congrArg (resSection ((Scheme.Modules.pullback f).obj M) hVp) (key m)
    rw [resSection_smul, resSection_resSection, resSection_resSection, resSection_rfl] at h2
    exact h2

end

end AlgebraicGeometry.Scheme.Modules
