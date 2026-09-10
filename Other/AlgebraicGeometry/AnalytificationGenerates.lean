/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSectionOfAlgebraic
public import Other.AlgebraicGeometry.GeneratingSectionCoefficient

/-!
# The analytification of a generating section generates

This file proves `AnalytificationGenerates X d`
(`Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean`, `docs/DIVISOR_HANDOFF.md` §4.2(b)):
if `g : Γ(L, U)` generates an algebraic sheaf of modules `L` on an algebraic open `U`, then its
analytification `analyticSection X d L U g` generates `(moduleAnalytification X d).obj L` on the
analytic open `U^an`.

## The argument

No base-change theorem is needed. Write `φ := regularToHolomorphicRingSheaf X d`,
`M := (moduleAnalytification X d).obj L = (pullback φ).obj L` and `A := U^an`. The two sheaves
of `𝒪^an`-modules

* `starUnitSheaf X d A : V ↦ 𝒪^an(A ⨯ V)` and
* `starModuleSheaf X d A M : V ↦ M(A ⨯ V)`

are pushforwards along `Over.star A` of `unit (𝒪^an.over A)` and of `M.over A`, so they are
sheaves for free, and they see exactly the analytic opens contained in `A`.

* `coeffHom` is the *explicit* morphism of algebraic sheaves of modules
  `L ⟶ (pushforward φ).obj (starUnitSheaf X d A)` sending `t : Γ(L, W)` to the evaluation of the
  coefficient `hg.coeff W t` of `t` with respect to `g` (`GeneratingSectionCoefficient.lean`).
* `analyticCoeffHom` is its adjoint `M ⟶ starUnitSheaf X d A` under
  `moduleAnalytificationAdjunction`; by the triangle identity it satisfies
  `analyticCoeffHom (t^an) = coeffHom t` (`analyticCoeffHom_analyticSection`).
* `smulSectionHom` is multiplication by `s := analyticSection X d L U g`, a morphism
  `unit (𝒪^an.over A) ⟶ M.over A`; `HolomorphicGenerates s` is precisely the statement that all
  of its components are bijective.
* `analyticCoeffHom_comp_smulSectionHom` states that `analyticCoeffHom` followed by (the
  pushforward of) `smulSectionHom` is the canonical map
  `toStarModuleSheaf : M ⟶ starModuleSheaf X d A M`, `m ↦ m|_{A ⨯ V}`. Because morphisms out of
  a pullback are determined by their adjoints, this reduces to the algebraic identity
  `hg.coeff W t • g|_{W ⊓ U} = t|_{W ⊓ U}` transported to the analytic side, which is exactly
  the already-proved `analyticSection_smul_res`.

Evaluating `analyticCoeffHom_comp_smulSectionHom` on an analytic open `V ≤ A` gives a two-sided
inverse to multiplication by `s|_V`, hence `holomorphicGenerates_analyticSection` and
`analytificationGenerates`.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite Limits

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance analytificationGeneratesTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- Pushforward along `Over.star A`. -/
abbrev starPushforward (A : Opens (TopCat.of (ComplexPoint X))) :
    SheafOfModules.{0} ((holomorphicRingSheaf X d).over A) ⥤
      SheafOfModules.{0} (holomorphicRingSheaf X d) :=
  SheafOfModules.pushforward.{0} (SheafOfModules.pushforwardOver A)

/-- The sheaf `V ↦ 𝒪^an(A ⨯ V)`. -/
abbrev starUnitSheaf (A : Opens (TopCat.of (ComplexPoint X))) :
    SheafOfModules.{0} (holomorphicRingSheaf X d) :=
  (starPushforward X d A).obj (SheafOfModules.unit ((holomorphicRingSheaf X d).over A))

/-- The sheaf `V ↦ M(A ⨯ V)`. -/
abbrev starModuleSheaf (A : Opens (TopCat.of (ComplexPoint X)))
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d)) :
    SheafOfModules.{0} (holomorphicRingSheaf X d) :=
  (starPushforward X d A).obj (M.over A)

/-- Restriction in the holomorphic structure sheaf. -/
def resH {V V' : Opens (TopCat.of (ComplexPoint X))} (h : V' ≤ V)
    (r : (holomorphicRingSheaf X d).obj.obj (op V)) :
    (holomorphicRingSheaf X d).obj.obj (op V') :=
  (holomorphicRingSheaf X d).obj.map (homOfLE h).op r

@[simp]
lemma resH_comp {V₁ V₂ V₃ : Opens (TopCat.of (ComplexPoint X))} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂)
    (r : (holomorphicRingSheaf X d).obj.obj (op V₁)) :
    resH X d h₂ (resH X d h₁ r) = resH X d (h₂.trans h₁) r := by
  rw [resH, resH, resH, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma resH_map {V V' : Opens (TopCat.of (ComplexPoint X))} (f : V' ⟶ V)
    (r : (holomorphicRingSheaf X d).obj.obj (op V)) :
    (holomorphicRingSheaf X d).obj.map f.op r = resH X d (leOfHom f) r := rfl

lemma resH_mul {V V' : Opens (TopCat.of (ComplexPoint X))} (h : V' ≤ V)
    (r r' : (holomorphicRingSheaf X d).obj.obj (op V)) :
    resH X d h (r * r') = resH X d h r * resH X d h r' :=
  map_mul ((holomorphicRingSheaf X d).obj.map (homOfLE h).op).hom r r'

lemma resH_add {V V' : Opens (TopCat.of (ComplexPoint X))} (h : V' ≤ V)
    (r r' : (holomorphicRingSheaf X d).obj.obj (op V)) :
    resH X d h (r + r') = resH X d h r + resH X d h r' :=
  map_add ((holomorphicRingSheaf X d).obj.map (homOfLE h).op).hom r r'

@[simp]
lemma resH_rfl {V : Opens (TopCat.of (ComplexPoint X))}
    (r : (holomorphicRingSheaf X d).obj.obj (op V)) : resH X d le_rfl r = r := by
  rw [resH]
  change ((holomorphicRingSheaf X d).obj.map (𝟙 (op V))) r = r
  rw [(holomorphicRingSheaf X d).obj.map_id]
  rfl

@[simp]
lemma resH_one {V V' : Opens (TopCat.of (ComplexPoint X))} (h : V' ≤ V) :
    resH X d h (1 : (holomorphicRingSheaf X d).obj.obj (op V)) = 1 :=
  map_one ((holomorphicRingSheaf X d).obj.map (homOfLE h).op).hom

lemma analyticFunction_add (V : X.left.Opens) (r r' : Γ(X.left, V)) :
    analyticFunction X d V (r + r') = analyticFunction X d V r + analyticFunction X d V r' :=
  map_add ((regularToHolomorphicRingSheaf X d).hom.app (op V)).hom r r'

lemma analyticOpen_inf (U W : X.left.Opens) :
    analyticOpen X (W ⊓ U) = analyticOpen X W ⊓ analyticOpen X U := rfl

lemma prod_le_analyticOpen_inf (U W : X.left.Opens) :
    (analyticOpen X U ⨯ analyticOpen X W : Opens (TopCat.of (ComplexPoint X))) ≤
      analyticOpen X (W ⊓ U) := by
  rw [analyticOpen_inf]
  exact le_inf (leOfHom Limits.prod.snd) (leOfHom Limits.prod.fst)

lemma analyticOpen_inf_le_prod (U W : X.left.Opens) :
    analyticOpen X (W ⊓ U) ≤
      (analyticOpen X U ⨯ analyticOpen X W : Opens (TopCat.of (ComplexPoint X))) := by
  rw [analyticOpen_inf]
  exact leOfHom (Limits.prod.lift (homOfLE inf_le_right) (homOfLE inf_le_left))

/-- Monotonicity of `A ⨯ -`. -/
lemma prod_mono (A : Opens (TopCat.of (ComplexPoint X)))
    {V V' : Opens (TopCat.of (ComplexPoint X))} (h : V' ≤ V) :
    (A ⨯ V' : Opens (TopCat.of (ComplexPoint X))) ≤
      (A ⨯ V : Opens (TopCat.of (ComplexPoint X))) :=
  leOfHom (Limits.prod.map (𝟙 A) (homOfLE h))

section SmulSection

variable {M : SheafOfModules.{0} (holomorphicRingSheaf X d)}
  {A : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op A))

/-- The compatible family of restrictions of `s`. -/
def smulSectionFamily : (M.over A).sections :=
  PresheafOfModules.sectionsMk (fun Z => holRes M (leOfHom Z.unop.hom) s)
    (fun _ _ _ => holRes_holRes _ _ s)

/-- Multiplication by `s`, as a morphism of sheaves of modules on the site over `A`. -/
def smulSectionHom : SheafOfModules.unit ((holomorphicRingSheaf X d).over A) ⟶ M.over A :=
  (SheafOfModules.unitHomEquiv (M.over A)).symm (smulSectionFamily X d s)

lemma smulSectionHom_val_app (Z : Over A) (r : (holomorphicRingSheaf X d).obj.obj (op Z.left)) :
    (smulSectionHom X d s).val.app (op Z) r = r • holRes M (leOfHom Z.hom) s := rfl

variable (M A) in
/-- The canonical map `M(V) → M(A ⨯ V)`. -/
def toStarModuleSheaf : M ⟶ starModuleSheaf X d A M :=
  (SheafOfModules.overPushforwardOverAdj.{0} A).unit.app M

lemma toStarModuleSheaf_val_app (V : Opens (TopCat.of (ComplexPoint X)))
    (m : M.val.obj (op V)) :
    (toStarModuleSheaf X d M A).val.app (op V) m =
      holRes M (leOfHom (Limits.prod.snd : (A ⨯ V) ⟶ V)) m := rfl

end SmulSection

section

variable {L : X.left.Modules} {U : X.left.Opens} {g : Γ(L, U)}

/-- The analytified coefficient of a section with respect to a generating section. -/
def analyticCoeff (hg : Scheme.Modules.Generates g) (W : X.left.Opens) (t : Γ(L, W)) :
    (holomorphicRingSheaf X d).obj.obj
      (op (analyticOpen X U ⨯ analyticOpen X W : Opens (TopCat.of (ComplexPoint X)))) :=
  resH X d (prod_le_analyticOpen_inf X U W) (analyticFunction X d (W ⊓ U) (hg.coeff W t))

lemma analyticCoeff_apply (hg : Scheme.Modules.Generates g) (W : X.left.Opens) (t : Γ(L, W)) :
    analyticCoeff X d hg W t =
      resH X d (prod_le_analyticOpen_inf X U W)
        (analyticFunction X d (W ⊓ U) (hg.coeff W t)) := rfl

lemma analyticCoeff_add (hg : Scheme.Modules.Generates g) (W : X.left.Opens) (t t' : Γ(L, W)) :
    analyticCoeff X d hg W (t + t') = analyticCoeff X d hg W t + analyticCoeff X d hg W t' := by
  rw [analyticCoeff_apply, analyticCoeff_apply, analyticCoeff_apply, hg.coeff_add,
    analyticFunction_add, resH_add]

lemma analyticCoeff_smul (hg : Scheme.Modules.Generates g) (W : X.left.Opens) (r : Γ(X.left, W))
    (t : Γ(L, W)) :
    analyticCoeff X d hg W (r • t) =
      resH X d (leOfHom (Limits.prod.snd :
          (analyticOpen X U ⨯ analyticOpen X W : Opens (TopCat.of (ComplexPoint X))) ⟶
            analyticOpen X W))
        (analyticFunction X d W r) * analyticCoeff X d hg W t := by
  rw [analyticCoeff_apply, analyticCoeff_apply, hg.coeff_smul, smul_eq_mul,
    analyticFunction_mul, resH_mul]
  congr 1
  rw [analyticFunction_res, resH_map, resH_comp]

lemma analyticCoeff_res (hg : Scheme.Modules.Generates g) {W W' : X.left.Opens} (h : W' ≤ W)
    (t : Γ(L, W)) :
    analyticCoeff X d hg W' (Scheme.Modules.resSection L h t) =
      resH X d (prod_mono X (analyticOpen X U) (analyticOpen_mono X h))
        (analyticCoeff X d hg W t) := by
  rw [analyticCoeff_apply, analyticCoeff_apply, hg.coeff_res, analyticFunction_res, resH_map,
    resH_comp, resH_comp]

/-- The morphism of sheaves of modules given by the analytified coefficient. -/
def coeffHom (hg : Scheme.Modules.Generates g) :
    L ⟶ (holomorphicModulePushforward X d).obj (starUnitSheaf X d (analyticOpen X U)) :=
  SheafOfModules.Hom.mk
    { app := fun W => ModuleCat.homMk
        (AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun t => analyticCoeff X d hg W.unop t)
          (fun t t' => analyticCoeff_add X d hg W.unop t t')))
        (fun r => by
          ext t
          exact (analyticCoeff_smul X d hg W.unop r t).symm)
      naturality := fun {W W'} i => by
        ext x
        exact analyticCoeff_res X d hg (leOfHom i.unop) x }

lemma coeffHom_val_app (hg : Scheme.Modules.Generates g) (W : X.left.Opens) (t : Γ(L, W)) :
    (coeffHom X d hg).val.app (op W) t = analyticCoeff X d hg W t := rfl

/-- The adjoint morphism `L^an ⟶ starUnitSheaf X d U^an`. -/
def analyticCoeffHom (hg : Scheme.Modules.Generates g) :
    (moduleAnalytification X d).obj L ⟶ starUnitSheaf X d (analyticOpen X U) :=
  ((moduleAnalytificationAdjunction X d).homEquiv L (starUnitSheaf X d (analyticOpen X U))).symm
    (coeffHom X d hg)

lemma analyticCoeffHom_analyticSection (hg : Scheme.Modules.Generates g) (W : X.left.Opens)
    (t : Γ(L, W)) :
    (analyticCoeffHom X d hg).val.app (op (analyticOpen X W)) (analyticSection X d L W t) =
      analyticCoeff X d hg W t := by
  have h : (moduleAnalytificationAdjunction X d).unit.app L ≫
      (holomorphicModulePushforward X d).map (analyticCoeffHom X d hg) = coeffHom X d hg := by
    have h0 : (moduleAnalytificationAdjunction X d).homEquiv L
        (starUnitSheaf X d (analyticOpen X U)) (analyticCoeffHom X d hg) =
        coeffHom X d hg := Equiv.apply_symm_apply _ _
    rw [Adjunction.homEquiv_unit] at h0
    exact h0
  exact congrArg
    (fun f : L ⟶ (holomorphicModulePushforward X d).obj (starUnitSheaf X d (analyticOpen X U)) =>
      ConcreteCategory.hom (SheafOfModules.Hom.val f |>.app (op W)) t) h

lemma smul_analyticSection_key (hg : Scheme.Modules.Generates g) (W : X.left.Opens)
    (t : Γ(L, W)) :
    analyticCoeff X d hg W t •
        holRes ((moduleAnalytification X d).obj L)
          (leOfHom (Limits.prod.fst :
            (analyticOpen X U ⨯ analyticOpen X W : Opens (TopCat.of (ComplexPoint X))) ⟶
              analyticOpen X U))
          (analyticSection X d L U g) =
      holRes ((moduleAnalytification X d).obj L)
        (leOfHom (Limits.prod.snd :
          (analyticOpen X U ⨯ analyticOpen X W : Opens (TopCat.of (ComplexPoint X))) ⟶
            analyticOpen X W))
        (analyticSection X d L W t) := by
  have hbase := analyticSection_smul_res (X := X) (d := d) L
    (inf_le_right : W ⊓ U ≤ U) (inf_le_left : W ⊓ U ≤ W)
    (hg.coeff W t) g t (hg.coeff_smul_eq W t)
  have h2 := congrArg (holRes ((moduleAnalytification X d).obj L)
    (prod_le_analyticOpen_inf X U W)) hbase
  rw [holRes_smul, holRes_holRes, holRes_holRes] at h2
  exact h2

theorem analyticCoeffHom_comp_smulSectionHom (hg : Scheme.Modules.Generates g) :
    analyticCoeffHom X d hg ≫ (starPushforward X d (analyticOpen X U)).map
        (smulSectionHom X d (analyticSection X d L U g)) =
      toStarModuleSheaf X d ((moduleAnalytification X d).obj L) (analyticOpen X U) := by
  apply ((moduleAnalytificationAdjunction X d).homEquiv L _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ (fun W => ?_)
  ext t
  show ((starPushforward X d (analyticOpen X U)).map
      (smulSectionHom X d (analyticSection X d L U g))).val.app (op (analyticOpen X W))
        ((analyticCoeffHom X d hg).val.app (op (analyticOpen X W)) (analyticSection X d L W t)) = _
  rw [analyticCoeffHom_analyticSection]
  exact smul_analyticSection_key X d hg W t

lemma analyticCoeff_self (hg : Scheme.Modules.Generates g) : analyticCoeff X d hg U g = 1 := by
  rw [analyticCoeff_apply, hg.coeff_self, analyticFunction_one, resH_one]

/-- Sections of `starUnitSheaf` over `V` are the holomorphic functions on `A ⨯ V`. -/
def starUnitSheafSection {A V : Opens (TopCat.of (ComplexPoint X))}
    (x : (starUnitSheaf X d A).val.obj (op V)) :
    (holomorphicRingSheaf X d).obj.obj (op (A ⨯ V : Opens (TopCat.of (ComplexPoint X)))) := x

lemma starUnitSheafSection_smul {A V : Opens (TopCat.of (ComplexPoint X))}
    (r : (holomorphicRingSheaf X d).obj.obj (op V)) (x : (starUnitSheaf X d A).val.obj (op V)) :
    starUnitSheafSection X d (r • x) =
      resH X d (leOfHom (Limits.prod.snd :
        (A ⨯ V : Opens (TopCat.of (ComplexPoint X))) ⟶ V)) r * starUnitSheafSection X d x := rfl

/-- **The analytification of a generating section generates.** -/
theorem holomorphicGenerates_analyticSection (hg : Scheme.Modules.Generates g) :
    HolomorphicGenerates (M := (moduleAnalytification X d).obj L)
      (analyticSection X d L U g) := by
  intro V hV
  have hVp : V ≤ (analyticOpen X U ⨯ V : Opens (TopCat.of (ComplexPoint X))) :=
    leOfHom (Limits.prod.lift (homOfLE hV) (𝟙 V))
  have key : ∀ m : ((moduleAnalytification X d).obj L).val.obj (op V),
      starUnitSheafSection X d ((analyticCoeffHom X d hg).val.app (op V) m) •
          holRes ((moduleAnalytification X d).obj L)
            (leOfHom (Limits.prod.fst :
              (analyticOpen X U ⨯ V : Opens (TopCat.of (ComplexPoint X))) ⟶ analyticOpen X U))
            (analyticSection X d L U g) =
        holRes ((moduleAnalytification X d).obj L)
          (leOfHom (Limits.prod.snd :
            (analyticOpen X U ⨯ V : Opens (TopCat.of (ComplexPoint X))) ⟶ V)) m := fun m =>
    congrArg (fun (h : (moduleAnalytification X d).obj L ⟶
        starModuleSheaf X d (analyticOpen X U) ((moduleAnalytification X d).obj L)) =>
      ConcreteCategory.hom (SheafOfModules.Hom.val h |>.app (op V)) m)
      (analyticCoeffHom_comp_smulSectionHom X d hg)
  have hone : starUnitSheafSection X d ((analyticCoeffHom X d hg).val.app (op V)
      (holRes ((moduleAnalytification X d).obj L) hV (analyticSection X d L U g))) = 1 := by
    have hnat := PresheafOfModules.naturality_apply (analyticCoeffHom X d hg).val (homOfLE hV).op
      (analyticSection X d L U g)
    rw [analyticCoeffHom_analyticSection X d hg U g, analyticCoeff_self] at hnat
    rw [hnat]
    exact resH_one X d (prod_mono X (analyticOpen X U) hV)
  have hkap : ∀ r : (holomorphicRingSheaf X d).obj.obj (op V),
      resH X d hVp (starUnitSheafSection X d ((analyticCoeffHom X d hg).val.app (op V)
        (r • holRes ((moduleAnalytification X d).obj L) hV
          (analyticSection X d L U g)))) = r := by
    intro r
    rw [(analyticCoeffHom X d hg).val.app (op V) |>.hom.map_smul r
      (holRes ((moduleAnalytification X d).obj L) hV (analyticSection X d L U g)),
      starUnitSheafSection_smul, hone, mul_one, resH_comp, resH_rfl]
  constructor
  · intro r r' hrr'
    have hrr2 : r • holRes ((moduleAnalytification X d).obj L) hV
        (analyticSection X d L U g) =
      r' • holRes ((moduleAnalytification X d).obj L) hV (analyticSection X d L U g) := hrr'
    have h1 := hkap r
    rw [hrr2] at h1
    exact h1.symm.trans (hkap r')
  · intro m
    refine ⟨resH X d hVp
      (starUnitSheafSection X d ((analyticCoeffHom X d hg).val.app (op V) m)), ?_⟩
    have h2 := congrArg (holRes ((moduleAnalytification X d).obj L) hVp) (key m)
    rw [holRes_smul, holRes_holRes, holRes_holRes, holRes_rfl] at h2
    exact h2

end

/-- **The analytification of a generating section generates.** -/
theorem analytificationGenerates : AnalytificationGenerates X d :=
  fun _ _ _ hg => holomorphicGenerates_analyticSection X d hg

end AlgebraicGeometry.ComplexPoint

