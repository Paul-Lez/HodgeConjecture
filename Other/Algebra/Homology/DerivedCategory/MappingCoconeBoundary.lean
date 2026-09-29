/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality
public import Other.Algebra.Homology.DegreewiseSplitConnecting

/-!
# Boundary classes under the canonical short-exact-sequence cone comparison

For a degreewise split short exact sequence, the positive cone inclusion is homotopic
to the connecting cocycle followed by the explicit shifted lift. Thus the inverse of the
canonical cone comparison sends each boundary class to the usual connecting class,
with positive sign. This controls the boundary image independently of any choice of
a completion of a morphism of distinguished triangles.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace CochainComplex.mappingCocone
variable {C : Type*} [Category* C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ))

lemma shiftedLiftShortComplex_f_fst_v (n : ℤ) :
    (shiftedLiftShortComplex S).f n ≫ (mappingCone.fst S.g).1.v n (n + 1) rfl =
      S.f.f (n + 1) := by
  simp [shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

lemma shiftedLiftShortComplex_f_snd_v (n : ℤ) :
    (shiftedLiftShortComplex S).f n ≫ (mappingCone.snd S.g).v n n (add_zero n) = 0 := by
  simp [shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

variable (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting)

/-- The splitting supplies an explicit homotopy from the cone boundary inclusion. -/
def inrHomotopyHomOfDegreewiseSplit :
    Homotopy (mappingCone.inr S.g) (homOfDegreewiseSplit S σ ≫ shiftedLiftShortComplex S) := by
  apply mappingCone.liftHomotopy S.g _ _ (Cochain.mk (fun p q h =>
    (σ p).s ≫ (S.X₂.XIsoOfEq (by omega : p = q)).hom)) 0
  · ext n _ rfl
    simp only [Cochain.comp_v _ _ _ n n (n + 1) (add_zero n) rfl,
      Cochain.ofHom_v, mappingCone.inr_f_fst_v, Cochain.add_v, Cochain.neg_v,
      HomologicalComplex.comp_f, Category.assoc, shiftedLiftShortComplex_f_fst_v]
    rw [δ_v 0 1 rfl _ n (n + 1) rfl n (n + 1) (by omega) rfl]
    simp only [Cochain.mk_v, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Int.negOnePow_one, Units.neg_smul, one_smul,
      homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit, Cocycle.mk_coe]
    have hr := (σ (n + 1)).r_f
    have hs := (σ n).s_g
    dsimp only [ShortComplex.map, HomologicalComplex.eval] at hr hs
    erw [Category.comp_id, Category.comp_id, Category.assoc, Category.assoc, hr, Preadditive.comp_sub,
      Preadditive.comp_sub, Category.comp_id, ← S.g.comm_assoc, ← Category.assoc (σ n).s, hs,
      Category.id_comp]
    abel
  · ext n
    simp only [δ_zero, Cochain.add_v, zero_add,
      Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n), Cochain.ofHom_v,
      mappingCone.inr_f_snd_v, Cochain.mk_v, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, HomologicalComplex.comp_f, Category.assoc,
      shiftedLiftShortComplex_f_snd_v, comp_zero, add_zero]
    erw [Category.id_comp]
    exact (σ n).s_g.symm

include σ in
/-- The canonical cone inverse maps the positive boundary inclusion to the usual LES boundary. -/
lemma homologyMap_inr_comp_shortExactHomologyIsoCone_inv
    (hS : S.ShortExact) (n m : ℤ) (h : 1 + n = m) :
    HomologicalComplex.homologyMap (mappingCone.inr S.g) n ≫
      (shortExactHomologyIsoCone S hS n m h).inv =
        hS.δ n m (by change n + 1 = m; omega) := by
  let := quasiIso_shiftedLiftShortComplex S hS
  have ht := (inrHomotopyHomOfDegreewiseSplit S σ).homologyMap_eq n
  change HomologicalComplex.homologyMap (mappingCone.inr S.g) n ≫
    (inv (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n) ≫
      ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n m h).hom.app S.X₁) = _
  rw [ht, HomologicalComplex.homologyMap_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  exact homology_shiftMap_homOfDegreewiseSplit_eq_δ S σ hS n m (by omega)

end CochainComplex.mappingCocone
