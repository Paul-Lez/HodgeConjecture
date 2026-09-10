/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Tactic
public import Other.TauCeti.SheafOfModules.LocalTriviality
public import Other.TauCeti.SheafOfModules.Free

/-!
# Negative twisting sheaves on projective spectra

This file constructs `𝒪(-n)` on the projective spectrum of an `ℕ`-graded commutative ring.
Its sections are ambient-localization fractions whose numerator has homogeneous degree `d` and
whose denominator has degree `d + n`, locally on the projective spectrum. The construction is
closed under regular scalars and restriction, satisfies the sheaf condition, and recovers the
structure sheaf at `n = 0`.

This is the first algebraic input for a projective-space proof of GAGA by twists and finite
presentations. It is independent of the analytic comparison still required by GAGA.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise
open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local instance projectivePointPrime (x : ProjectiveSpectrum.top 𝒜) :
    Ideal.IsPrime (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x)) :=
  ProjectiveSpectrum.isPrime x

abbrev ProjectiveSpectrum.ambientLocalization
    (x : ProjectiveSpectrum.top 𝒜) :=
  Localization.AtPrime
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

def ProjectiveSpectrum.ambientDenominator
    (x : ProjectiveSpectrum.top 𝒜) (s : A)
    (hs : s ∉ ProjectiveSpectrum.asHomogeneousIdeal x) :
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x)).primeCompl :=
  ⟨s, hs⟩

namespace ProjectiveSpectrum.NegativeTwist

local notation3 "loc[" x "]" => ProjectiveSpectrum.ambientLocalization 𝒜 x

set_option backward.isDefEq.respectTransparency.types false in
/-- A local fraction of homogeneous degree `-n`. The zero function is allowed separately because
a general graded ring need not have a degree-one denominator near every projective prime. -/
def IsFractionOrZero (n : ℕ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (f : ∀ x : U, loc[x.1]) : Prop :=
  f = 0 ∨ ∃ (d : ℕ) (r : 𝒜 d) (s : 𝒜 (d + n))
    (s_nin : ∀ x : U, s.1 ∉ x.1.asHomogeneousIdeal),
      ∀ x : U, f x = Localization.mk (r : A)
        (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 s (s_nin x))

set_option backward.isDefEq.respectTransparency.types false in
def isFractionOrZeroPrelocal (n : ℕ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => loc[x] where
  pred f := IsFractionOrZero 𝒜 n f
  res := by
    rintro V U i f (hzero | ⟨d, r, s, hs, h⟩)
    · left
      funext x
      exact congrFun hzero (i x)
    · exact Or.inr ⟨d, r, s, (hs <| i ·), (h <| i ·)⟩

set_option backward.isDefEq.respectTransparency.types false in
def isLocallyFractionOrZero (n : ℕ) :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => loc[x] :=
  (isFractionOrZeroPrelocal 𝒜 n).sheafify

namespace Sections

variable {𝒜}

set_option backward.isDefEq.respectTransparency.types false in
theorem zero_mem (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFractionOrZero 𝒜 n).pred (0 : ∀ x : U.unop, loc[x.1]) := fun x =>
  ⟨U.unop, x.2, 𝟙 U.unop, Or.inl rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem neg_mem (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : ∀ x : U.unop, loc[x.1])
    (ha : (isLocallyFractionOrZero 𝒜 n).pred a) :
    (isLocallyFractionOrZero 𝒜 n).pred (-a) := fun x => by
  rcases ha x with ⟨V, hxV, i, hzero | ⟨d, r, s, hs, h⟩⟩
  · refine ⟨V, hxV, i, Or.inl ?_⟩
    funext y
    simp only [Pi.neg_apply, Pi.zero_apply, neg_eq_zero]
    exact congrFun hzero y
  · refine ⟨V, hxV, i, Or.inr ⟨d, ⟨-r, NegMemClass.neg_mem r.2⟩, s, hs, ?_⟩⟩
    intro y
    change -a (i y) = _
    have hy := h y
    change a (i y) = _ at hy
    rw [hy, Localization.neg_mk]

set_option backward.isDefEq.respectTransparency.types false in
theorem add_mem (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a b : ∀ x : U.unop, loc[x.1])
    (ha : (isLocallyFractionOrZero 𝒜 n).pred a)
    (hb : (isLocallyFractionOrZero 𝒜 n).pred b) :
  (isLocallyFractionOrZero 𝒜 n).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, hxa, ia, hza | ⟨da, ra, sa, hsa, ha⟩⟩
  all_goals rcases hb x with ⟨Vb, hxb, ib, hzb | ⟨db, rb, sb, hsb, hb⟩⟩
  · refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia, Or.inl ?_⟩
    funext y
    change a (ia ⟨y.1, y.2.1⟩) + b (ib ⟨y.1, y.2.2⟩) = 0
    have ha0 := congrFun hza ⟨y.1, y.2.1⟩
    have hb0 := congrFun hzb ⟨y.1, y.2.2⟩
    simpa using congrArg₂ (fun p q => p + q) ha0 hb0
  · refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia, Or.inr ?_⟩
    exact ⟨db, rb, sb, (fun y => hsb ⟨y.1, y.2.2⟩), fun y => by
      change a (ia ⟨y.1, y.2.1⟩) + b (ib ⟨y.1, y.2.2⟩) = _
      have ha0 := congrFun hza ⟨y.1, y.2.1⟩
      calc
        _ = 0 + b (ib ⟨y.1, y.2.2⟩) := congrArg (fun z => z + b (ib ⟨y.1, y.2.2⟩)) ha0
        _ = b (ib ⟨y.1, y.2.2⟩) := zero_add _
        _ = _ := hb ⟨y.1, y.2.2⟩⟩
  · refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia, Or.inr ?_⟩
    exact ⟨da, ra, sa, (fun y => hsa ⟨y.1, y.2.1⟩), fun y => by
      change a (ia ⟨y.1, y.2.1⟩) + b (ib ⟨y.1, y.2.2⟩) = _
      have hb0 := congrFun hzb ⟨y.1, y.2.2⟩
      calc
        _ = a (ia ⟨y.1, y.2.1⟩) + 0 :=
          congrArg (fun z => a (ia ⟨y.1, y.2.1⟩) + z) hb0
        _ = a (ia ⟨y.1, y.2.1⟩) := add_zero _
        _ = _ := ha ⟨y.1, y.2.1⟩⟩
  · refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia, Or.inr ?_⟩
    let d := da + db + n
    let r : 𝒜 d := ⟨ra * sb + sa * rb, by
      dsimp [d]
      apply AddMemClass.add_mem
      · simpa only [Nat.add_assoc] using SetLike.mul_mem_graded ra.2 sb.2
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          SetLike.mul_mem_graded sa.2 rb.2⟩
    let s : 𝒜 (d + n) := ⟨sa * sb, by
      simpa only [d, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SetLike.mul_mem_graded sa.2 sb.2⟩
    refine ⟨d, r, s, ?_, ?_⟩
    · intro y
      exact y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
        (hsa ⟨y.1, y.2.1⟩) (hsb ⟨y.1, y.2.2⟩)
    · intro y
      change a (ia ⟨y.1, y.2.1⟩) + b (ib ⟨y.1, y.2.2⟩) = _
      simp only [ha ⟨y.1, y.2.1⟩, hb ⟨y.1, y.2.2⟩]
      simp only [Localization.add_mk]
      simp [r, s, ProjectiveSpectrum.ambientDenominator, add_comm, mul_comm]
      congr 1

end Sections

set_option backward.isDefEq.respectTransparency.types false in
def sectionsAddSubgroup (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddSubgroup (∀ x : U.unop, loc[x.1]) where
  carrier := { f | (isLocallyFractionOrZero 𝒜 n).pred f }
  zero_mem' := Sections.zero_mem n U
  add_mem' := Sections.add_mem n U _ _
  neg_mem' := Sections.neg_mem n U _

set_option backward.isDefEq.respectTransparency.types false in
def sheafInType (n : ℕ) : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFractionOrZero 𝒜 n)

instance (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 n).1.obj U) :=
  (sectionsAddSubgroup 𝒜 n U).toAddCommGroup

/-- The structure sheaf of `Proj 𝒜`, with values restricted from commutative rings to rings. -/
def ringSheaf : Sheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)) RingCat :=
  (sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
    (forget₂ CommRingCat RingCat)).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒜)

set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit projective-spectrum ring sheaf agrees with the ring sheaf of Mathlib's
scheme `Proj`. -/
theorem ringSheaf_eq_schemeRingSheaf :
    ringSheaf 𝒜 = (_root_.AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf :=
  rfl

local notation3 "𝒪" => ringSheaf 𝒜

set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation of a regular section in the ambient localizations at the points of an open set. -/
def sectionToAmbientPi (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (𝒪).obj.obj U →+* (∀ x : U.unop, loc[x.1]) where
  toFun a x := (a.1 x).val
  map_zero' := by
    funext x
    change (0 : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal).val = 0
    exact HomogeneousLocalization.val_zero
  map_one' := by
    funext x
    change (1 : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal).val = 1
    exact HomogeneousLocalization.val_one
  map_add' a b := by
    funext x
    change (a.1 x + b.1 x).val = (a.1 x).val + (b.1 x).val
    exact HomogeneousLocalization.val_add _ _
  map_mul' a b := by
    funext x
    change (a.1 x * b.1 x).val = (a.1 x).val * (b.1 x).val
    exact HomogeneousLocalization.val_mul _ _

set_option backward.isDefEq.respectTransparency.types false in
instance ambientPiModule (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((𝒪).obj.obj U) (∀ x : U.unop, loc[x.1]) :=
  Module.compHom _ (sectionToAmbientPi 𝒜 U)

namespace Sections

set_option backward.isDefEq.respectTransparency.types false in
theorem smul_mem (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (𝒪).obj.obj U) (b : ∀ x : U.unop, loc[x.1])
    (hb : (isLocallyFractionOrZero 𝒜 n).pred b) :
    (isLocallyFractionOrZero 𝒜 n).pred (a • b) := fun x => by
  rcases a.2 x with ⟨Va, hxa, ia, ja, ra, sa, hsa, ha⟩
  rcases hb x with ⟨Vb, hxb, ib, hzb | ⟨db, rb, sb, hsb, hb⟩⟩
  · refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia, Or.inl ?_⟩
    funext y
    change (sectionToAmbientPi 𝒜 U a) ((Opens.infLELeft Va Vb ≫ ia) y) *
      b ((Opens.infLELeft Va Vb ≫ ia) y) = 0
    have hb0 := congrFun hzb ⟨y.1, y.2.2⟩
    have hb0' : b ((Opens.infLELeft Va Vb ≫ ia) y) = 0 := by
      change b (ib ⟨y.1, y.2.2⟩) = 0
      exact hb0
    rw [hb0', mul_zero]
  · refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia, Or.inr ?_⟩
    let d := ja + db
    let r : 𝒜 d := ⟨ra * rb, by
      simpa only [d] using SetLike.mul_mem_graded ra.2 rb.2⟩
    let s : 𝒜 (d + n) := ⟨sa * sb, by
      simpa only [d, Nat.add_assoc] using SetLike.mul_mem_graded sa.2 sb.2⟩
    refine ⟨d, r, s, ?_, ?_⟩
    · intro y
      exact y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
        (hsa ⟨y.1, y.2.1⟩) (hsb ⟨y.1, y.2.2⟩)
    · intro y
      change (sectionToAmbientPi 𝒜 U a) ((Opens.infLELeft Va Vb ≫ ia) y) *
        b ((Opens.infLELeft Va Vb ≫ ia) y) = _
      have ha' : (sectionToAmbientPi 𝒜 U a) ((Opens.infLELeft Va Vb ≫ ia) y) =
          Localization.mk (ra : A)
            (ProjectiveSpectrum.ambientDenominator 𝒜 y.1 sa (hsa ⟨y.1, y.2.1⟩)) := by
        change (a.1 (ia ⟨y.1, y.2.1⟩)).val = _
        have hay := ha ⟨y.1, y.2.1⟩
        change a.1 (ia ⟨y.1, y.2.1⟩) = _ at hay
        rw [hay, HomogeneousLocalization.val_mk]
        rfl
      have hb' : b ((Opens.infLELeft Va Vb ≫ ia) y) =
          Localization.mk (rb : A)
            (ProjectiveSpectrum.ambientDenominator 𝒜 y.1 sb (hsb ⟨y.1, y.2.2⟩)) := by
        change b (ib ⟨y.1, y.2.2⟩) = _
        exact hb ⟨y.1, y.2.2⟩
      rw [ha', hb', Localization.mk_mul]
      simp [r, s, ProjectiveSpectrum.ambientDenominator]
      congr 1

end Sections

set_option backward.isDefEq.respectTransparency.types false in
def sectionsSubmodule (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Submodule ((𝒪).obj.obj U) (∀ x : U.unop, loc[x.1]) where
  __ := sectionsAddSubgroup 𝒜 n U
  smul_mem' := Sections.smul_mem (𝒜 := 𝒜) n U

set_option backward.isDefEq.respectTransparency.types false in
instance sectionsModule (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((𝒪).obj.obj U) ((sheafInType 𝒜 n).1.obj U) :=
  inferInstanceAs (Module ((𝒪).obj.obj U) ↑(sectionsSubmodule 𝒜 n U))

/-- Sections of the negative twist on an open set, as a module over regular functions. -/
def sectionModule (n : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    ModuleCat ((𝒪).obj.obj U) :=
  ModuleCat.of _ ((sheafInType 𝒜 n).1.obj U)

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of degree-`-n` homogeneous fractions. -/
def sectionModuleRestriction (n : ℕ)
    {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (i : U ⟶ V) :
    sectionModule 𝒜 n U ⟶
      (ModuleCat.restrictScalars ((𝒪).obj.map i).hom).obj (sectionModule 𝒜 n V) := by
  letI : Module ((𝒪).obj.obj U) (sectionModule 𝒜 n V) :=
    Module.compHom (sectionModule 𝒜 n V) ((𝒪).obj.map i).hom
  refine ModuleCat.ofHom ?_
  exact
    { toFun := (sheafInType 𝒜 n).1.map i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The presheaf of modules whose local sections are degree-`-n` homogeneous fractions. -/
def presheafOfModules (n : ℕ) : PresheafOfModules (𝒪).obj where
  obj := sectionModule 𝒜 n
  map := sectionModuleRestriction 𝒜 n
  map_id _ := rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl

/-- The local homogeneous-fraction presheaf, dressed as a presheaf of abelian groups. -/
def presheafInAddCommGrp (n : ℕ) :
    Presheaf AddCommGrpCat (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 n).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 n).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Forgetting abelian-group structure recovers the original type-valued subsheaf. -/
def presheafInAddCommGrpCompForgetIso (n : ℕ) :
    presheafInAddCommGrp 𝒜 n ⋙ forget AddCommGrpCat ≅ (sheafInType 𝒜 n).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- The local homogeneous-fraction presheaf is a sheaf of abelian groups. -/
def sheafInAddCommGrp (n : ℕ) :
    Sheaf AddCommGrpCat (ProjectiveSpectrum.top 𝒜) :=
  ⟨presheafInAddCommGrp 𝒜 n,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
      (Presheaf.isSheaf_of_iso (presheafInAddCommGrpCompForgetIso 𝒜 n).symm
        (sheafInType 𝒜 n).property)⟩

/-- Forgetting the module structure recovers the sheaf of local homogeneous fractions. -/
def underlyingPresheafIso (n : ℕ) :
    (presheafOfModules 𝒜 n).presheaf ≅ (sheafInAddCommGrp 𝒜 n).1 :=
  NatIso.ofComponents (fun U =>
    { hom := AddCommGrpCat.ofHom
        { toFun := fun f => f
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      inv := AddCommGrpCat.ofHom
        { toFun := fun f => f
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }) (by
        intro U V i
        ext f
        rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-- The algebraic twisting sheaf `𝒪(-n)` on `Proj 𝒜`, constructed from local homogeneous
fractions rather than postulated as a line bundle. -/
def sheafOfModules (n : ℕ) : SheafOfModules (ringSheaf 𝒜) where
  val := presheafOfModules 𝒜 n
  isSheaf := Presheaf.isSheaf_of_iso (underlyingPresheafIso 𝒜 n).symm
    (sheafInAddCommGrp 𝒜 n).property

/-- The same negative twist, expressed in Mathlib's category of modules on the scheme `Proj`. -/
def schemeSheafOfModules (n : ℕ) : (_root_.AlgebraicGeometry.«Proj» 𝒜).Modules := by
  change SheafOfModules (_root_.AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf
  rw [← ringSheaf_eq_schemeRingSheaf]
  exact sheafOfModules 𝒜 n

namespace DegreeZero

set_option backward.isDefEq.respectTransparency.types false in
theorem exists_homogeneousPreimage
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 0).1.obj U)
    (x : U.unop) :
    ∃ z : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal,
      z.val = f.1 x := by
  rcases f.2 x with ⟨V, hxV, i, hzero | ⟨d, r, s, hs, h⟩⟩
  · refine ⟨0, ?_⟩
    have hxy := congrFun hzero ⟨x.1, hxV⟩
    change f.1 x = 0 at hxy
    simpa only [HomogeneousLocalization.val_zero] using hxy.symm
  · let y : V := ⟨x.1, hxV⟩
    refine ⟨HomogeneousLocalization.mk ⟨d, r, s, hs y⟩, ?_⟩
    rw [HomogeneousLocalization.val_mk]
    have hxy := h y
    change f.1 x = _ at hxy
    rw [hxy]
    rfl

/-- The degree-zero homogeneous localization element represented by a local degree-zero
ambient fraction. -/
noncomputable def lift
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 0).1.obj U)
    (x : U.unop) : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal :=
  Classical.choose (exists_homogeneousPreimage 𝒜 U f x)

theorem lift_val
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 0).1.obj U)
    (x : U.unop) : (lift 𝒜 U f x).val = f.1 x :=
  Classical.choose_spec (exists_homogeneousPreimage 𝒜 U f x)

set_option backward.isDefEq.respectTransparency.types false in
/-- A regular section, regarded pointwise as an ambient degree-zero fraction. -/
def ofRegular
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : (𝒪).obj.obj U) :
    (sheafInType 𝒜 0).1.obj U :=
  ⟨sectionToAmbientPi 𝒜 U a, fun x => by
    rcases a.2 x with ⟨V, hxV, i, d, r, s, hs, h⟩
    refine ⟨V, hxV, i, Or.inr ⟨d, r, s, hs, ?_⟩⟩
    intro y
    change (a.1 (i y)).val = _
    have hy := h y
    change a.1 (i y) = _ at hy
    rw [hy, HomogeneousLocalization.val_mk]
    rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A locally degree-zero ambient fraction, lifted uniquely to a regular section. -/
def toRegular
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 0).1.obj U) :
    (𝒪).obj.obj U :=
  ⟨fun x => lift 𝒜 U f x, fun x => by
    rcases f.2 x with ⟨V, hxV, i, hzero | ⟨d, r, s, hs, h⟩⟩
    · refine ⟨V, hxV, i, 0, ⟨0, zero_mem _⟩,
        ⟨1, SetLike.one_mem_graded _⟩, ?_, ?_⟩
      · intro y
        exact y.1.asHomogeneousIdeal.toIdeal.primeCompl.one_mem
      · intro y
        rw [HomogeneousLocalization.ext_iff_val, lift_val]
        have hy := congrFun hzero y
        change f.1 (i y) = 0 at hy
        rw [hy, HomogeneousLocalization.val_mk]
        exact (Localization.mkAddMonoidHom _).map_zero.symm
    · refine ⟨V, hxV, i, d, r, s, hs, ?_⟩
      intro y
      rw [HomogeneousLocalization.ext_iff_val, lift_val, HomogeneousLocalization.val_mk]
      have hy := h y
      change f.1 (i y) = _ at hy
      exact hy⟩

theorem ofRegular_toRegular
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 0).1.obj U) :
    ofRegular 𝒜 U (toRegular 𝒜 U f) = f := by
  apply Subtype.ext
  funext x
  exact lift_val 𝒜 U f x

theorem toRegular_ofRegular
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : (𝒪).obj.obj U) :
    toRegular 𝒜 U (ofRegular 𝒜 U a) = a := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  exact lift_val 𝒜 U (ofRegular 𝒜 U a) x

set_option backward.isDefEq.respectTransparency.types false in
/-- On every open set, regular sections are linearly equivalent to sections of `𝒪(0)`. -/
def sectionLinearEquiv
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (𝒪).obj.obj U ≃ₗ[(𝒪).obj.obj U] sectionModule 𝒜 0 U where
  toFun := ofRegular 𝒜 U
  invFun := toRegular 𝒜 U
  left_inv := toRegular_ofRegular 𝒜 U
  right_inv := ofRegular_toRegular 𝒜 U
  map_add' a b := by
    apply Subtype.ext
    funext x
    change (a.1 x + b.1 x).val = (a.1 x).val + (b.1 x).val
    exact HomogeneousLocalization.val_add _ _
  map_smul' a b := by
    apply Subtype.ext
    funext x
    change (a.1 x * b.1 x).val = (a.1 x).val * (b.1 x).val
    exact HomogeneousLocalization.val_mul _ _

/-- The module isomorphism on sections underlying `𝒪(0) ≅ 𝒪`. -/
def sectionModuleIso
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    ModuleCat.of ((𝒪).obj.obj U) ((𝒪).obj.obj U) ≅ sectionModule 𝒜 0 U :=
  { hom := ModuleCat.ofHom (sectionLinearEquiv 𝒜 U).toLinearMap
    inv := ModuleCat.ofHom (sectionLinearEquiv 𝒜 U).symm.toLinearMap
    hom_inv_id := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (sectionLinearEquiv 𝒜 U).symm_apply_apply a
    inv_hom_id := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (sectionLinearEquiv 𝒜 U).apply_symm_apply f }

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf-level canonical isomorphism `𝒪 ≅ 𝒪(0)`. -/
def unitPresheafIso :
    PresheafOfModules.unit (𝒪).obj ≅ presheafOfModules 𝒜 0 :=
  PresheafOfModules.isoMk (sectionModuleIso 𝒜) (by
    intro U V i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext x
    rfl)

/-- The degree-zero twist is the tensor unit. -/
def unitIso : SheafOfModules.unit (ringSheaf 𝒜) ≅ sheafOfModules 𝒜 0 :=
  { hom := ⟨(unitPresheafIso 𝒜).hom⟩
    inv := ⟨(unitPresheafIso 𝒜).inv⟩
    hom_inv_id := by
      apply SheafOfModules.hom_ext
      exact (unitPresheafIso 𝒜).hom_inv_id
    inv_hom_id := by
      apply SheafOfModules.hom_ext
      exact (unitPresheafIso 𝒜).inv_hom_id }

end DegreeZero

namespace HomogeneousShift

set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication by a homogeneous element of degree `n` sends `𝒪(-n)` to `𝒪(0)`. -/
def multiply {n : ℕ} (q : 𝒜 n)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 n).1.obj U) :
    (sheafInType 𝒜 0).1.obj U :=
  ⟨fun x => Localization.mk (q : A) 1 * f.1 x, fun x => by
    rcases f.2 x with ⟨V, hxV, i, hzero | ⟨d, r, s, hs, h⟩⟩
    · refine ⟨V, hxV, i, Or.inl ?_⟩
      funext y
      change Localization.mk (q : A) 1 * f.1 (i y) = 0
      have hy := congrFun hzero y
      change f.1 (i y) = 0 at hy
      rw [hy, mul_zero]
    · let e := n + d
      let r' : 𝒜 e := ⟨q * r, by
        simpa only [e] using SetLike.mul_mem_graded q.2 r.2⟩
      let s' : 𝒜 (e + 0) := ⟨s, by
        simpa only [e, Nat.add_zero, Nat.add_comm] using s.2⟩
      refine ⟨V, hxV, i, Or.inr ⟨e, r', s', ?_, ?_⟩⟩
      · intro y
        exact hs y
      · intro y
        change Localization.mk (q : A) 1 * f.1 (i y) = _
        have hy := h y
        change f.1 (i y) = _ at hy
        rw [hy, Localization.mk_mul]
        simp [r', s', ProjectiveSpectrum.ambientDenominator]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Division by a homogeneous element nonvanishing on `U` sends `𝒪(0)` to `𝒪(-n)`. -/
def divide {n : ℕ} (q : 𝒜 n)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hq : ∀ x : U.unop, (q : A) ∉ x.1.asHomogeneousIdeal)
    (f : (sheafInType 𝒜 0).1.obj U) : (sheafInType 𝒜 n).1.obj U :=
  ⟨fun x => Localization.mk (1 : A)
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) * f.1 x, fun x => by
    rcases f.2 x with ⟨V, hxV, i, hzero | ⟨d, r, s, hs, h⟩⟩
    · refine ⟨V, hxV, i, Or.inl ?_⟩
      funext y
      change Localization.mk (1 : A)
        (ProjectiveSpectrum.ambientDenominator 𝒜 y.1 q (hq (i y))) * f.1 (i y) = 0
      have hy := congrFun hzero y
      change f.1 (i y) = 0 at hy
      rw [hy, mul_zero]
    · let s' : 𝒜 (d + n) := ⟨q * s, by
        simpa only [Nat.add_zero, Nat.add_comm] using SetLike.mul_mem_graded q.2 s.2⟩
      refine ⟨V, hxV, i, Or.inr ⟨d, r, s', ?_, ?_⟩⟩
      · intro y
        exact y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hq (i y)) (hs y)
      · intro y
        change Localization.mk (1 : A)
          (ProjectiveSpectrum.ambientDenominator 𝒜 y.1 q (hq (i y))) * f.1 (i y) = _
        have hy := h y
        change f.1 (i y) = _ at hy
        rw [hy, Localization.mk_mul]
        simp [s', ProjectiveSpectrum.ambientDenominator]
        congr 1⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem multiply_divide {n : ℕ} (q : 𝒜 n)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hq : ∀ x : U.unop, (q : A) ∉ x.1.asHomogeneousIdeal)
    (f : (sheafInType 𝒜 0).1.obj U) :
    multiply 𝒜 q U (divide 𝒜 q U hq f) = f := by
  apply Subtype.ext
  funext x
  change Localization.mk (q : A) 1 *
    (Localization.mk (1 : A) (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) *
      f.1 x) = f.1 x
  have hunit : Localization.mk (q : A) 1 *
      Localization.mk (1 : A) (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) = 1 := by
    simp only [Localization.mk_eq_mk']
    exact IsLocalization.mk'_mul_mk'_eq_one
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) 1
  rw [← mul_assoc, hunit, one_mul]

set_option backward.isDefEq.respectTransparency.types false in
theorem divide_multiply {n : ℕ} (q : 𝒜 n)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hq : ∀ x : U.unop, (q : A) ∉ x.1.asHomogeneousIdeal)
    (f : (sheafInType 𝒜 n).1.obj U) :
    divide 𝒜 q U hq (multiply 𝒜 q U f) = f := by
  apply Subtype.ext
  funext x
  change Localization.mk (1 : A)
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) *
    (Localization.mk (q : A) 1 * f.1 x) = f.1 x
  have hunit : Localization.mk (1 : A)
        (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) *
      Localization.mk (q : A) 1 = 1 := by
    simp only [Localization.mk_eq_mk']
    exact IsLocalization.mk'_mul_mk'_eq_one 1
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x))
  rw [← mul_assoc, hunit, one_mul]

set_option backward.isDefEq.respectTransparency.types false in
/-- On an open set where `q` does not vanish, division by `q` trivializes `𝒪(-n)`. -/
def sectionLinearEquiv {n : ℕ} (q : 𝒜 n)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hq : ∀ x : U.unop, (q : A) ∉ x.1.asHomogeneousIdeal) :
    sectionModule 𝒜 0 U ≃ₗ[(ringSheaf 𝒜).obj.obj U] sectionModule 𝒜 n U where
  toFun := divide 𝒜 q U hq
  invFun := multiply 𝒜 q U
  left_inv := multiply_divide 𝒜 q U hq
  right_inv := divide_multiply 𝒜 q U hq
  map_add' f g := by
    apply Subtype.ext
    funext x
    change Localization.mk (1 : A)
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) * (f.1 x + g.1 x) =
        Localization.mk (1 : A)
          (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) * f.1 x +
        Localization.mk (1 : A)
          (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) * g.1 x
    exact mul_add _ _ _
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change Localization.mk (1 : A)
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) *
        ((a.1 x).val * f.1 x) =
      (a.1 x).val * (Localization.mk (1 : A)
        (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x)) * f.1 x)
    ring

/-- The corresponding isomorphism of section modules on a nonvanishing open set. -/
def sectionModuleIso {n : ℕ} (q : 𝒜 n)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hq : ∀ x : U.unop, (q : A) ∉ x.1.asHomogeneousIdeal) :
    sectionModule 𝒜 0 U ≅ sectionModule 𝒜 n U :=
  { hom := ModuleCat.ofHom (sectionLinearEquiv 𝒜 q U hq).toLinearMap
    inv := ModuleCat.ofHom (sectionLinearEquiv 𝒜 q U hq).symm.toLinearMap
    hom_inv_id := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (sectionLinearEquiv 𝒜 q U hq).symm_apply_apply f
    inv_hom_id := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (sectionLinearEquiv 𝒜 q U hq).apply_symm_apply f }

set_option backward.isDefEq.respectTransparency.types false in
/-- On an object over `D₊(q)`, the degree-zero and degree-`-n` section modules are
canonically isomorphic. -/
def basicOpenSectionIso {n : ℕ} (q : 𝒜 n)
    (Y : (Over (ProjectiveSpectrum.basicOpen 𝒜 (q : A)))ᵒᵖ) :
    (SheafOfModules.unit ((ringSheaf 𝒜).over
      (ProjectiveSpectrum.basicOpen 𝒜 (q : A)))).val.obj Y ≅
      ((sheafOfModules 𝒜 n).over
        (ProjectiveSpectrum.basicOpen 𝒜 (q : A))).val.obj Y :=
  DegreeZero.sectionModuleIso 𝒜 (op Y.unop.left) ≪≫
    sectionModuleIso 𝒜 q (op Y.unop.left) (fun x => Y.unop.hom.le x.2)

set_option backward.isDefEq.respectTransparency.types false in
/-- The negative twist is trivial after restriction to the basic open where its homogeneous
trivializing element is nonzero. -/
def basicOpenUnitIso {n : ℕ} (q : 𝒜 n) :
    SheafOfModules.unit ((ringSheaf 𝒜).over
        (ProjectiveSpectrum.basicOpen 𝒜 (q : A))) ≅
      (sheafOfModules 𝒜 n).over (ProjectiveSpectrum.basicOpen 𝒜 (q : A)) :=
  { hom := ⟨(PresheafOfModules.isoMk (basicOpenSectionIso 𝒜 q) (by
        intro U V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        funext x
        rfl)).hom⟩
    inv := ⟨(PresheafOfModules.isoMk (basicOpenSectionIso 𝒜 q) (by
        intro U V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        funext x
        rfl)).inv⟩
    hom_inv_id := by
      apply SheafOfModules.hom_ext
      exact (PresheafOfModules.isoMk (basicOpenSectionIso 𝒜 q)).hom_inv_id
    inv_hom_id := by
      apply SheafOfModules.hom_ext
      exact (PresheafOfModules.isoMk (basicOpenSectionIso 𝒜 q)).inv_hom_id }

end HomogeneousShift

section Invertible

set_option backward.isDefEq.respectTransparency.types false in
/-- Homogeneous degree-`n` elements whose basic opens cover `Proj` give a local trivialization
atlas for `𝒪(-n)`. -/
def localTrivializationsOfBasicOpenCover {n : ℕ} {I : Type u} (q : I → 𝒜 n)
    (hq : ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (q i : A) = ⊤) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} (sheafOfModules 𝒜 n) where
  I := I
  X i := ProjectiveSpectrum.basicOpen 𝒜 (q i : A)
  coversTop := (Opens.coversTop_iff (ProjectiveSpectrum 𝒜)
    (fun i => ProjectiveSpectrum.basicOpen 𝒜 (q i : A))).2 hq
  iso i := TauCeti.SheafOfModules.freePUnitIsoUnit
      ((ringSheaf 𝒜).over (ProjectiveSpectrum.basicOpen 𝒜 (q i : A))) ≪≫
    HomogeneousShift.basicOpenUnitIso 𝒜 (q i)

/-- A degree-`n` family covering `Proj` proves that the constructed `𝒪(-n)` is invertible. -/
theorem isInvertible_of_basicOpenCover {n : ℕ} {I : Type u} (q : I → 𝒜 n)
    (hq : ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (q i : A) = ⊤) :
    TauCeti.SheafOfModules.IsInvertible.{u, u, u} (sheafOfModules 𝒜 n) :=
  (localTrivializationsOfBasicOpenCover 𝒜 q hq).isInvertible

/-- The invertibility result transported to Mathlib's scheme-module presentation of `Proj`. -/
theorem schemeSheafOfModules_isInvertible_of_basicOpenCover {n : ℕ} {I : Type u}
    (q : I → 𝒜 n) (hq : ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (q i : A) = ⊤) :
    TauCeti.SheafOfModules.IsInvertible.{u, u, u} (schemeSheafOfModules 𝒜 n) := by
  change TauCeti.SheafOfModules.IsInvertible (sheafOfModules 𝒜 n)
  exact isInvertible_of_basicOpenCover 𝒜 q hq

/-- A power of a degree-one homogeneous element, bundled in its resulting degree. -/
def degreeOnePower (q : 𝒜 1) (n : ℕ) : 𝒜 n :=
  ⟨(q : A) ^ n, by simpa using SetLike.pow_mem_graded n q.2⟩

/-- Positive powers of a degree-one basic-open cover are again a cover. -/
theorem iSup_basicOpen_degreeOnePower_eq_top {I : Type u} (q : I → 𝒜 1)
    (hq : ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (q i : A) = ⊤) (n : ℕ) (hn : 0 < n) :
    ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (degreeOnePower 𝒜 (q i) n : A) = ⊤ := by
  calc
    _ = ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (q i : A) := by
      congr 1
      funext i
      simpa only [degreeOnePower] using
        (ProjectiveSpectrum.basicOpen_pow 𝒜 (q i : A) n hn)
    _ = ⊤ := hq

/-- If degree-one homogeneous elements cover `Proj`, every negative twist is invertible. -/
theorem isInvertible_of_degreeOneCover {I : Type u} (q : I → 𝒜 1)
    (hq : ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (q i : A) = ⊤) (n : ℕ) :
    TauCeti.SheafOfModules.IsInvertible.{u, u, u} (sheafOfModules 𝒜 n) := by
  rcases n with _ | n
  · let q₀ : PUnit → 𝒜 0 := fun _ => ⟨1, SetLike.one_mem_graded 𝒜⟩
    apply isInvertible_of_basicOpenCover 𝒜 q₀
    simp [q₀]
  · apply isInvertible_of_basicOpenCover 𝒜 (fun i => degreeOnePower 𝒜 (q i) (n + 1))
    exact iSup_basicOpen_degreeOnePower_eq_top 𝒜 q hq (n + 1) (Nat.zero_lt_succ n)

end Invertible

end ProjectiveSpectrum.NegativeTwist

end AlgebraicGeometry
