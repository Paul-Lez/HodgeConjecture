/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionCorrectedLifts
public import Other.AlgebraicGeometry.UnitExtensionClassOfMiddleHom

/-!
# The morphism of extensions attached to a system of corrected lifts

From `CorrectedLifts E E'` we build a morphism `E.middle ⟶ E'.middle` under the holomorphic
unit sheaf and over the constant integer sheaf, by gluing the local isomorphisms of the two
split presentations. Consequently `E` and `E'` have the same class in `Ext¹(ℤ, 𝒪ˣ)`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open HolomorphicUnitExtension

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance unitExtensionMiddleHomTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

namespace CorrectedLifts

variable {E E' : HolomorphicUnitExtension X d} (c : CorrectedLifts E E')

/-- Every germ of the middle sheaf of `E` is the germ of a local model at its own point. -/
theorem exists_germ_sourceModel (x : ComplexPoint X) (σ : E.middle.presheaf.stalk x) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (hxU : x ∈ U) (hU : U ≤ c.opens x) (n : ℤ)
      (a : (holomorphicUnitSheaf X d).obj.obj (op U)),
      E.middle.presheaf.germ U x hxU (c.sourceModel x hU n a) = σ := by
  obtain ⟨V, hxV, s, rfl⟩ := E.middle.presheaf.exists_germ_eq σ
  obtain ⟨U, hxU, hUV, hUx, n, a, ha⟩ := c.exists_sourceModel x s x hxV (c.mem_opens x)
  refine ⟨U, hxU, hUx, n, a, ?_⟩
  rw [← ha]
  exact germ_sres hUV s x hxU

theorem existsUnique_stalkValue (x : ComplexPoint X) (σ : E.middle.presheaf.stalk x) :
    ∃! τ : E'.middle.presheaf.stalk x,
      ∀ (U : Opens (TopCat.of (ComplexPoint X))) (hxU : x ∈ U) (hU : U ≤ c.opens x) (n : ℤ)
        (a : (holomorphicUnitSheaf X d).obj.obj (op U)),
        E.middle.presheaf.germ U x hxU (c.sourceModel x hU n a) = σ →
          τ = E'.middle.presheaf.germ U x hxU (c.targetModel x hU n a) := by
  obtain ⟨U₀, hxU₀, hU₀, n₀, a₀, h₀⟩ := c.exists_germ_sourceModel x σ
  refine ⟨E'.middle.presheaf.germ U₀ x hxU₀ (c.targetModel x hU₀ n₀ a₀), ?_, ?_⟩
  · intro U hxU hU n a hUa
    exact c.germ_targetModel_eq x hxU₀ hxU hU₀ hU n₀ n a₀ a (h₀.trans hUa.symm)
  · intro τ hτ
    exact hτ U₀ hxU₀ hU₀ n₀ a₀ h₀

/-- The value of the comparison map on a germ of the middle sheaf of `E`. -/
def stalkValue (x : ComplexPoint X) (σ : E.middle.presheaf.stalk x) : E'.middle.presheaf.stalk x :=
  (c.existsUnique_stalkValue x σ).exists.choose

theorem stalkValue_eq (x : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))} (hxU : x ∈ U)
    (hU : U ≤ c.opens x) (n : ℤ) (a : (holomorphicUnitSheaf X d).obj.obj (op U))
    {σ : E.middle.presheaf.stalk x}
    (h : E.middle.presheaf.germ U x hxU (c.sourceModel x hU n a) = σ) :
    c.stalkValue x σ = E'.middle.presheaf.germ U x hxU (c.targetModel x hU n a) :=
  (c.existsUnique_stalkValue x σ).exists.choose_spec U hxU hU n a h

theorem stalkValue_zero (x : ComplexPoint X) : c.stalkValue x 0 = 0 := by
  have hs : c.sourceModel x (le_refl (c.opens x)) 0 0 = 0 := by
    unfold sourceModel
    rw [map_zero, zero_smul, add_zero]
  have ht : c.targetModel x (le_refl (c.opens x)) 0 0 = 0 := by
    unfold targetModel
    rw [map_zero, zero_smul, add_zero]
  have hσ : E.middle.presheaf.germ (c.opens x) x (c.mem_opens x)
      (c.sourceModel x (le_refl (c.opens x)) 0 0) = 0 := by
    rw [hs, map_zero]
  rw [c.stalkValue_eq x (c.mem_opens x) (le_refl (c.opens x)) 0 0 hσ, ht, map_zero]

theorem stalkValue_add (x : ComplexPoint X) (σ σ' : E.middle.presheaf.stalk x) :
    c.stalkValue x (σ + σ') = c.stalkValue x σ + c.stalkValue x σ' := by
  obtain ⟨U, hxU, hU, n, a, ha⟩ := c.exists_germ_sourceModel x σ
  obtain ⟨U', hxU', hU', n', a', ha'⟩ := c.exists_germ_sourceModel x σ'
  have hWU : U ⊓ U' ≤ U := inf_le_left
  have hWU' : U ⊓ U' ≤ U' := inf_le_right
  have hxW : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
  have hb : E.middle.presheaf.germ (U ⊓ U') x hxW
      (c.sourceModel x (hWU.trans hU) n (sres (holomorphicUnitSheaf X d) hWU a)) = σ := by
    rw [← c.sres_sourceModel x hU hWU n a]
    exact (germ_sres hWU _ x hxW).trans ha
  have hb' : E.middle.presheaf.germ (U ⊓ U') x hxW
      (c.sourceModel x (hWU'.trans hU') n' (sres (holomorphicUnitSheaf X d) hWU' a')) = σ' := by
    rw [← c.sres_sourceModel x hU' hWU' n' a']
    exact (germ_sres hWU' _ x hxW).trans ha'
  have hsum : E.middle.presheaf.germ (U ⊓ U') x hxW
      (c.sourceModel x (hWU.trans hU) (n + n')
        (sres (holomorphicUnitSheaf X d) hWU a + sres (holomorphicUnitSheaf X d) hWU' a')) =
      σ + σ' := by
    rw [← c.sourceModel_add x (hWU.trans hU) n n', germ_add, hb, hb']
  rw [c.stalkValue_eq x hxW (hWU.trans hU) (n + n') _ hsum,
    c.stalkValue_eq x hxW (hWU.trans hU) n _ hb,
    c.stalkValue_eq x hxW (hWU.trans hU) n' _ hb', ← germ_add, c.targetModel_add]

/-- The comparison map on stalks. -/
def stalkHom (x : ComplexPoint X) : E.middle.presheaf.stalk x ⟶ E'.middle.presheaf.stalk x :=
  AddCommGrpCat.ofHom
    { toFun := c.stalkValue x
      map_zero' := c.stalkValue_zero x
      map_add' := c.stalkValue_add x }

@[simp]
theorem stalkHom_apply (x : ComplexPoint X) (σ : E.middle.presheaf.stalk x) :
    c.stalkHom x σ = c.stalkValue x σ := rfl

/-- The comparison map computed on a local model based at another point. -/
theorem stalkValue_rebase (x y : ComplexPoint X) {U : Opens (TopCat.of (ComplexPoint X))}
    (hUx : U ≤ c.opens x) (hyU : y ∈ U) (n : ℤ)
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) :
    c.stalkValue y (E.middle.presheaf.germ U y hyU (c.sourceModel x hUx n a)) =
      E'.middle.presheaf.germ U y hyU (c.targetModel x hUx n a) := by
  have hWU : U ⊓ c.opens y ≤ U := inf_le_left
  have hWy : U ⊓ c.opens y ≤ c.opens y := inf_le_right
  have hWx : U ⊓ c.opens y ≤ c.opens x := hWU.trans hUx
  have hyW : y ∈ U ⊓ c.opens y := ⟨hyU, c.mem_opens y⟩
  obtain ⟨b, hs, ht⟩ : ∃ b : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ c.opens y)),
      c.sourceModel y hWy n b = sres E.middle hWU (c.sourceModel x hUx n a) ∧
        c.targetModel y hWy n b = sres E'.middle hWU (c.targetModel x hUx n a) := by
    refine ⟨sres (holomorphicUnitSheaf X d) hWU a +
      n • E.localLifts.transition E.shortExact x y (U ⊓ c.opens y)
        (hWx.trans (c.le_opens x)) (hWy.trans (c.le_opens y)), ?_, ?_⟩
    · rw [c.sres_sourceModel]
      exact (c.sourceModel_base x y hWx hWy n _).symm
    · rw [c.sres_targetModel]
      exact (c.targetModel_base x y hWx hWy n _).symm
  have hσ : E.middle.presheaf.germ (U ⊓ c.opens y) y hyW (c.sourceModel y hWy n b) =
      E.middle.presheaf.germ U y hyU (c.sourceModel x hUx n a) := by
    rw [hs]
    exact germ_sres hWU _ y hyW
  rw [c.stalkValue_eq y hyW hWy n b hσ, ht]
  exact germ_sres hWU _ y hyW

/-- The stalk maps are locally represented by sections. -/
theorem stalkHom_rep (V : Opens (TopCat.of (ComplexPoint X))) (s : E.middle.presheaf.obj (op V))
    (x : ComplexPoint X) (_hx : x ∈ V) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U) (hUV : U ≤ V)
      (t : E'.middle.presheaf.obj (op U)), ∀ (y : ComplexPoint X) (hy : y ∈ U),
        E'.middle.presheaf.germ U y hy t =
          c.stalkHom y (E.middle.presheaf.germ V y (hUV hy) s) := by
  obtain ⟨U, hxU, hUV, hUx, n, a, ha⟩ := c.exists_sourceModel x s x _hx (c.mem_opens x)
  refine ⟨U, hxU, hUV, c.targetModel x hUx n a, ?_⟩
  intro y hy
  have hg : E.middle.presheaf.germ V y (hUV hy) s =
      E.middle.presheaf.germ U y hy (c.sourceModel x hUx n a) := by
    rw [← ha]
    exact (germ_sres hUV s y hy).symm
  rw [stalkHom_apply, hg, c.stalkValue_rebase x y hUx hy n a]

/-- The comparison morphism of middle sheaves. -/
def middleHom : E.middle ⟶ E'.middle :=
  TopCat.Sheaf.homOfStalkMaps E.middle E'.middle c.stalkHom c.stalkHom_rep

theorem germ_middleHom (V : Opens (TopCat.of (ComplexPoint X)))
    (s : E.middle.presheaf.obj (op V)) (x : ComplexPoint X) (hx : x ∈ V) :
    E'.middle.presheaf.germ V x hx (c.middleHom.hom.app (op V) s) =
      c.stalkValue x (E.middle.presheaf.germ V x hx s) :=
  TopCat.Sheaf.germ_homOfStalkMaps_app E.middle E'.middle c.stalkHom c.stalkHom_rep V s x hx

theorem stalkValue_inclusion (x : ComplexPoint X) {V : Opens (TopCat.of (ComplexPoint X))}
    (hx : x ∈ V) (a : (holomorphicUnitSheaf X d).obj.obj (op V)) :
    c.stalkValue x (E.middle.presheaf.germ V x hx (E.inclusion.hom.app (op V) a)) =
      E'.middle.presheaf.germ V x hx (E'.inclusion.hom.app (op V) a) := by
  have hWV : V ⊓ c.opens x ≤ V := inf_le_left
  have hWx : V ⊓ c.opens x ≤ c.opens x := inf_le_right
  have hxW : x ∈ V ⊓ c.opens x := ⟨hx, c.mem_opens x⟩
  have hs : c.sourceModel x hWx 0 (sres (holomorphicUnitSheaf X d) hWV a) =
      sres E.middle hWV (E.inclusion.hom.app (op V) a) := by
    unfold sourceModel
    rw [zero_smul, add_zero]
    exact (sres_hom E.inclusion hWV a).symm
  have ht : c.targetModel x hWx 0 (sres (holomorphicUnitSheaf X d) hWV a) =
      sres E'.middle hWV (E'.inclusion.hom.app (op V) a) := by
    unfold targetModel
    rw [zero_smul, add_zero]
    exact (sres_hom E'.inclusion hWV a).symm
  have hσ : E.middle.presheaf.germ (V ⊓ c.opens x) x hxW
      (c.sourceModel x hWx 0 (sres (holomorphicUnitSheaf X d) hWV a)) =
      E.middle.presheaf.germ V x hx (E.inclusion.hom.app (op V) a) := by
    rw [hs]
    exact germ_sres hWV _ x hxW
  rw [c.stalkValue_eq x hxW hWx 0 _ hσ, ht]
  exact germ_sres hWV _ x hxW

theorem projection_stalkValue (x : ComplexPoint X) (σ : E.middle.presheaf.stalk x) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map E'.projection.hom (c.stalkValue x σ) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map E.projection.hom σ := by
  obtain ⟨U, hxU, hU, n, a, ha⟩ := c.exists_germ_sourceModel x σ
  rw [c.stalkValue_eq x hxU hU n a ha, ← ha, ← germ_hom, ← germ_hom, c.map_sourceModel,
    c.map_targetModel]

theorem inclusion_middleHom : E.inclusion ≫ c.middleHom = E'.inclusion := by
  refine Sheaf.hom_ext (NatTrans.ext ?_)
  funext V
  obtain ⟨V⟩ := V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply TopCat.Presheaf.section_ext E'.middle V
  intro x hx
  show E'.middle.presheaf.germ V x hx
      (c.middleHom.hom.app (op V) (E.inclusion.hom.app (op V) a)) = _
  rw [c.germ_middleHom, c.stalkValue_inclusion]

theorem middleHom_projection : c.middleHom ≫ E'.projection = E.projection := by
  refine Sheaf.hom_ext (NatTrans.ext ?_)
  funext V
  obtain ⟨V⟩ := V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply TopCat.Presheaf.section_ext (constantIntegerSheaf X) V
  intro x hx
  show (constantIntegerSheaf X).presheaf.germ V x hx
      (E'.projection.hom.app (op V) (c.middleHom.hom.app (op V) s)) = _
  rw [germ_hom, c.germ_middleHom, c.projection_stalkValue, ← germ_hom]

include c in
/-- **Corrected lifts force equal classes.** -/
theorem cohomologyClass_eq : E.cohomologyClass = E'.cohomologyClass :=
  CategoryTheory.ShortComplex.ShortExact.extClass_eq_of_middleHom E.shortExact E'.shortExact
    c.middleHom c.inclusion_middleHom c.middleHom_projection

end CorrectedLifts

end AlgebraicGeometry.ComplexPoint
