/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLineBundleInvertible
public import Other.TauCeti.SheafOfModules.Free
public import Other.TauCeti.SheafOfModules.LocalTriviality

/-!
# Generating sections of holomorphic sheaves of modules

This is the analytic counterpart of `AlgebraicGeometry.Scheme.Modules.Generates`
(`Other/AlgebraicGeometry/InvertibleSheafRationalSection.lean`): the same definitions and
proofs, for sheaves of modules over the holomorphic structure sheaf of the analytic space.

* `holRes` — restriction of a section.
* `HolomorphicGenerates s` — on every smaller open, multiplication by the restriction of `s` is
  a bijection from holomorphic functions to sections.
* `HolomorphicGenerates.exists_isUnit_smul_eq` — two generating sections on the same open differ
  by a unit of the holomorphic structure sheaf. This is the frame-change statement used to
  compare two trivializations of the same analytic line bundle.
* `HolomorphicGenerates.map_iso` — generation is preserved by an isomorphism of sheaves of
  modules, so a trivialization may be transported along the isomorphism
  `(moduleAnalytification X d).obj L ≅ E.sectionSheafOfModules`.
* `holomorphicUnitIsoSection`, `holomorphicGenerates_unitIsoSection`,
  `nonempty_holomorphicTrivializingCover_of_isInvertible` — an invertible holomorphic sheaf of
  modules has a cover with a generating section on each member; in particular
  `E.sectionSheafOfModules` does, through `E.sectionLocalTrivializations`.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance holomorphicSheafGeneratorsTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable {M N : SheafOfModules (holomorphicRingSheaf X d)}

/-- Restriction of a section of a holomorphic sheaf of modules. -/
abbrev holRes (M : SheafOfModules (holomorphicRingSheaf X d))
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U) (s : M.val.obj (op U)) :
    M.val.obj (op V) :=
  M.val.map (homOfLE h).op s

@[simp]
lemma holRes_rfl {U : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op U)) :
    holRes M le_rfl s = s := by
  change M.val.map (𝟙 (op U)) s = s
  rw [M.val.map_id]
  rfl

lemma holRes_holRes {U V W : Opens (TopCat.of (ComplexPoint X))} (hVU : V ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op U)) :
    holRes M hWV (holRes M hVU s) = holRes M (hWV.trans hVU) s :=
  (M.val.map_comp_apply (homOfLE hVU).op (homOfLE hWV).op s).symm

lemma holRes_smul {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) (s : M.val.obj (op U)) :
    holRes M h (r • s) = (holomorphicRingSheaf X d).obj.map (homOfLE h).op r • holRes M h s :=
  M.val.map_smul _ _ _

/-- A section `s` generates the holomorphic sheaf of modules `M` on `U`. -/
def HolomorphicGenerates {U : Opens (TopCat.of (ComplexPoint X))} (s : M.val.obj (op U)) : Prop :=
  ∀ (V : Opens (TopCat.of (ComplexPoint X))) (h : V ≤ U),
    Function.Bijective fun r : (holomorphicRingSheaf X d).obj.obj (op V) ↦ r • holRes M h s

namespace HolomorphicGenerates

variable {U : Opens (TopCat.of (ComplexPoint X))} {s : M.val.obj (op U)}

lemma bijective (hs : HolomorphicGenerates s) :
    Function.Bijective fun r : (holomorphicRingSheaf X d).obj.obj (op U) ↦ r • s := by
  simpa using hs U le_rfl

/-- The restriction of a generating section generates on the smaller open. -/
lemma restrict (hs : HolomorphicGenerates s) {V : Opens (TopCat.of (ComplexPoint X))}
    (h : V ≤ U) : HolomorphicGenerates (holRes M h s) := by
  intro W hW
  have := hs W (hW.trans h)
  rwa [← holRes_holRes h hW s] at this

lemma exists_smul_eq (hs : HolomorphicGenerates s) {V : Opens (TopCat.of (ComplexPoint X))}
    (h : V ≤ U) (t : M.val.obj (op V)) :
    ∃ r : (holomorphicRingSheaf X d).obj.obj (op V), r • holRes M h s = t := (hs V h).surjective t

lemma smul_left_injective (hs : HolomorphicGenerates s)
    {V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U) :
    Function.Injective fun r : (holomorphicRingSheaf X d).obj.obj (op V) ↦ r • holRes M h s :=
  (hs V h).injective

/-- Two generating sections on the same open differ by a unit of the holomorphic structure
sheaf: the frame change between two trivializations. -/
lemma exists_isUnit_smul_eq (hs : HolomorphicGenerates s) {t : M.val.obj (op U)}
    (ht : HolomorphicGenerates t) :
    ∃ u : (holomorphicRingSheaf X d).obj.obj (op U), IsUnit u ∧ u • s = t := by
  obtain ⟨u, hu⟩ := hs.exists_smul_eq le_rfl t
  obtain ⟨v, hv⟩ := ht.exists_smul_eq le_rfl s
  rw [holRes_rfl] at hu hv
  have h2 : v * u = 1 := hs.bijective.injective (by
    show (v * u) • s = (1 : (holomorphicRingSheaf X d).obj.obj (op U)) • s
    rw [mul_smul, hu, hv, one_smul])
  have h3 : u * v = 1 := ht.bijective.injective (by
    show (u * v) • t = (1 : (holomorphicRingSheaf X d).obj.obj (op U)) • t
    rw [mul_smul, hv, hu, one_smul])
  exact ⟨u, ⟨⟨u, v, h3, h2⟩, rfl⟩, hu⟩

end HolomorphicGenerates

/-- Generation is preserved by an isomorphism of holomorphic sheaves of modules. -/
lemma HolomorphicGenerates.map_iso {U : Opens (TopCat.of (ComplexPoint X))}
    {s : M.val.obj (op U)} (hs : HolomorphicGenerates s) (e : M ≅ N) :
    HolomorphicGenerates (e.hom.val.app (op U) s) := by
  intro V h
  have hres : holRes N h (e.hom.val.app (op U) s) = e.hom.val.app (op V) (holRes M h s) :=
    (PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op s).symm
  have hbij : Function.Bijective (e.hom.val.app (op V)) :=
    ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation (R := holomorphicRingSheaf X d) (op V)).map e.hom)
  have hfun :
      (fun r : (holomorphicRingSheaf X d).obj.obj (op V) ↦
        r • holRes N h (e.hom.val.app (op U) s)) =
      (fun x ↦ e.hom.val.app (op V) x) ∘
        (fun r : (holomorphicRingSheaf X d).obj.obj (op V) ↦ r • holRes M h s) := by
    funext r
    rw [hres]
    exact ((e.hom.val.app (op V)).hom.map_smul r (holRes M h s)).symm
  rw [hfun]
  exact hbij.comp (hs V h)

/-- The section of `M` over `U` corresponding to `1` under a trivialization of `M` on `U`. -/
def holomorphicUnitIsoSection {U : Opens (TopCat.of (ComplexPoint X))}
    (e : SheafOfModules.unit ((holomorphicRingSheaf X d).over U) ≅ M.over U) :
    M.val.obj (op U) :=
  e.hom.val.app (op (Over.mk (𝟙 U))) (1 : (holomorphicRingSheaf X d).obj.obj (op U))

/-- The section corresponding to `1` under a trivialization generates. -/
theorem holomorphicGenerates_unitIsoSection {U : Opens (TopCat.of (ComplexPoint X))}
    (e : SheafOfModules.unit ((holomorphicRingSheaf X d).over U) ≅ M.over U) :
    HolomorphicGenerates (holomorphicUnitIsoSection e) := by
  intro V h
  have hbij : Function.Bijective (e.hom.val.app (op (Over.mk (homOfLE h)))) :=
    ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation (R := (holomorphicRingSheaf X d).over U)
        (op (Over.mk (homOfLE h)))).map e.hom)
  have hmu : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) := Over.homMk (homOfLE h) (by simp)
  have hone : e.hom.val.app (op (Over.mk (homOfLE h)))
      (1 : (holomorphicRingSheaf X d).obj.obj (op V)) =
      holRes M h (holomorphicUnitIsoSection e) := by
    have hnat := PresheafOfModules.naturality_apply e.hom.val hmu.op
      (1 : (holomorphicRingSheaf X d).obj.obj (op U))
    have h1 : (SheafOfModules.unit ((holomorphicRingSheaf X d).over U)).val.map hmu.op
        (1 : (holomorphicRingSheaf X d).obj.obj (op U)) =
        (1 : (holomorphicRingSheaf X d).obj.obj (op V)) :=
      PresheafOfModules.unit_map_one _ hmu.op
    rw [h1] at hnat
    exact hnat
  have hsmul : ∀ r : (holomorphicRingSheaf X d).obj.obj (op V),
      e.hom.val.app (op (Over.mk (homOfLE h))) r =
        r • holRes M h (holomorphicUnitIsoSection e) := by
    intro r
    have hlin := (e.hom.val.app (op (Over.mk (homOfLE h)))).hom.map_smul r
      (1 : (holomorphicRingSheaf X d).obj.obj (op V))
    rw [← hone]
    refine Eq.trans ?_ hlin
    congr 1
    exact (mul_one r).symm
  have hfun : (fun r : (holomorphicRingSheaf X d).obj.obj (op V) ↦
      r • holRes M h (holomorphicUnitIsoSection e)) =
      ⇑(ConcreteCategory.hom (e.hom.val.app (op (Over.mk (homOfLE h))))) := by
    funext r
    exact (hsmul r).symm
  rw [hfun]
  exact hbij

/-- A trivializing cover of a holomorphic sheaf of modules: an open cover of the analytic space
together with a generating section on each member. -/
structure HolomorphicTrivializingCover (M : SheafOfModules (holomorphicRingSheaf X d)) where
  /-- The index type of the cover. -/
  ι : Type
  /-- The members of the cover. -/
  opens : ι → Opens (TopCat.of (ComplexPoint X))
  /-- The members cover the analytic space. -/
  covers (z : ComplexPoint X) : ∃ i, z ∈ opens i
  /-- The chosen local frame on each member. -/
  gen (i : ι) : M.val.obj (op (opens i))
  /-- Each chosen local frame generates. -/
  gen_generates (i : ι) : HolomorphicGenerates (gen i)

namespace HolomorphicTrivializingCover

/-- The trivializing cover attached to a rank-one local trivialization atlas. -/
def ofLocalTrivializations (M : SheafOfModules (holomorphicRingSheaf X d))
    (t : TauCeti.SheafOfModules.LocalTrivializations M) : HolomorphicTrivializingCover M where
  ι := t.I
  opens := t.X
  covers z := ((Opens.coversTop_iff _ t.X).mp t.coversTop).exists_mem z
  gen i := holomorphicUnitIsoSection ((TauCeti.SheafOfModules.freePUnitIsoUnit _).symm ≪≫ t.iso i)
  gen_generates _ := holomorphicGenerates_unitIsoSection _

/-- A trivializing cover transports along an isomorphism of holomorphic sheaves of modules. -/
def transport (c : HolomorphicTrivializingCover M) (e : M ≅ N) :
    HolomorphicTrivializingCover N where
  ι := c.ι
  opens := c.opens
  covers := c.covers
  gen i := e.hom.val.app (op (c.opens i)) (c.gen i)
  gen_generates i := (c.gen_generates i).map_iso e

@[simp]
lemma transport_opens (c : HolomorphicTrivializingCover M) (e : M ≅ N) (i : c.ι) :
    (c.transport e).opens i = c.opens i := rfl

@[simp]
lemma transport_gen (c : HolomorphicTrivializingCover M) (e : M ≅ N) (i : c.ι) :
    (c.transport e).gen i = e.hom.val.app (op (c.opens i)) (c.gen i) := rfl

/-- An identity `u • a = b` between restrictions of sections transports along an isomorphism of
holomorphic sheaves of modules. -/
theorem _root_.AlgebraicGeometry.ComplexPoint.smul_holRes_map_iso (e : M ≅ N)
    {U V W : Opens (TopCat.of (ComplexPoint X))} (hWU : W ≤ U) (hWV : W ≤ V)
    (u : (holomorphicRingSheaf X d).obj.obj (op W)) (a : M.val.obj (op U)) (b : M.val.obj (op V))
    (h : u • holRes M hWU a = holRes M hWV b) :
    u • holRes N hWU (e.hom.val.app (op U) a) = holRes N hWV (e.hom.val.app (op V) b) := by
  have hU : holRes N hWU (e.hom.val.app (op U) a) = e.hom.val.app (op W) (holRes M hWU a) :=
    (PresheafOfModules.naturality_apply e.hom.val (homOfLE hWU).op a).symm
  have hV : holRes N hWV (e.hom.val.app (op V) b) = e.hom.val.app (op W) (holRes M hWV b) :=
    (PresheafOfModules.naturality_apply e.hom.val (homOfLE hWV).op b).symm
  rw [hU, hV, ← h]
  exact ((e.hom.val.app (op W)).hom.map_smul u (holRes M hWU a)).symm

/-- **Frame change.** On an open contained in a member of each of two trivializing covers of the
same holomorphic sheaf of modules, the two local frames differ by a unit of the holomorphic
structure sheaf, i.e. by a nowhere-vanishing holomorphic function. -/
theorem exists_isUnit_frameChange (c c' : HolomorphicTrivializingCover M) (i : c.ι) (i' : c'.ι)
    {V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ c.opens i) (h' : V ≤ c'.opens i') :
    ∃ u : (holomorphicRingSheaf X d).obj.obj (op V), IsUnit u ∧
      u • holRes M h (c.gen i) = holRes M h' (c'.gen i') :=
  ((c.gen_generates i).restrict h).exists_isUnit_smul_eq ((c'.gen_generates i').restrict h')

end HolomorphicTrivializingCover

/-- An invertible holomorphic sheaf of modules has a trivializing cover with a generating
section on each member. -/
theorem nonempty_holomorphicTrivializingCover_of_isInvertible
    (M : SheafOfModules (holomorphicRingSheaf X d))
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    Nonempty (HolomorphicTrivializingCover M) := by
  have := hM
  exact ⟨HolomorphicTrivializingCover.ofLocalTrivializations M
    (TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M)⟩

end AlgebraicGeometry.ComplexPoint
