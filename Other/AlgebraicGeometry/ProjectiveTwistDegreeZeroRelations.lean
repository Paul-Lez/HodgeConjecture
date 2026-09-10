/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.FiniteFreeAnalytification
public import Other.AlgebraicGeometry.GAGATwistPresentation
public import Other.AlgebraicGeometry.ProjectiveTwistDegreeZero

/-!
# Algebraization of degree-zero projective-twist relations

Finite sums of the presentation-induced zero twist are finite free sheaves.  Combining this
identification with the degree-zero comparison for finite free morphisms algebraizes every
relation between such sums.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint.ProjectiveTwist

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (P : ProjectiveSpace.Presentation X.hom)

/-- A finite sum of algebraic zero twists is the corresponding finite free module sheaf. -/
def algebraicFreeZeroIso (r : ℕ) :
    SheafOfModules.free (R := X.left.ringCatSheaf) (Fin r) ≅ algebraicSum X P 0 r :=
  IsColimit.coconePointsIsoOfNatIso
      (SheafOfModules.isColimitFreeCofan (R := X.left.ringCatSheaf) (Fin r))
      (coproductIsCoproduct (fun _ : Fin r ↦ algebraic X P 0))
      (Discrete.natIso fun _ ↦ algebraicZeroIso X P)

/-- A finite sum of analytic zero twists is the corresponding finite free holomorphic module
sheaf. The definition factors through algebraic analytification, making its compatibility with
`sumAnalytificationIso` definitional up to category laws. -/
def analyticFreeZeroIso (r : ℕ) :
    SheafOfModules.free (R := holomorphicRingSheaf X d) (Fin r) ≅ analyticSum X d P 0 r :=
  (unitFreeAnalytificationIso X d (Fin r)).symm ≪≫
    (moduleAnalytification X d).mapIso (algebraicFreeZeroIso X P r) ≪≫
      sumAnalytificationIso X d P 0 r

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every analytic relation between finite sums of the zero projective twist is the
analytification of an algebraic relation. -/
theorem analyticTwistRelationsAlgebraize_zero [IsProjective X.hom]
    [PreconnectedSpace (ComplexPoint X)] (relationRank generatorRank : ℕ)
    (f : analyticSum X d P 0 relationRank ⟶
      analyticSum X d P 0 generatorRank) :
    ∃ g : algebraicSum X P 0 relationRank ⟶
        algebraicSum X P 0 generatorRank,
      analyticRelation X d P g = f := by
  let eR := algebraicFreeZeroIso X P relationRank
  let eG := algebraicFreeZeroIso X P generatorRank
  let eRₐₙ := analyticFreeZeroIso X d P relationRank
  let eGₐₙ := analyticFreeZeroIso X d P generatorRank
  obtain ⟨a, ha⟩ := finiteFreeHom_analytification_surjective X d
    (Fin relationRank) (Fin generatorRank) (eRₐₙ.hom ≫ f ≫ eGₐₙ.inv)
  refine ⟨eR.inv ≫ a ≫ eG.hom, ?_⟩
  rw [← cancel_epi eRₐₙ.hom, ← cancel_mono eGₐₙ.inv]
  dsimp only [analyticRelation]
  dsimp only [eR, eG, eRₐₙ, eGₐₙ, analyticFreeZeroIso] at ha ⊢
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp] at ha ⊢
  simpa only [Category.assoc, ← (moduleAnalytification X d).map_comp_assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Iso.hom_inv_id,
    Iso.symm_hom, Iso.symm_inv, Category.comp_id, Category.id_comp, Functor.map_id] using ha

end AlgebraicGeometry.ComplexPoint.ProjectiveTwist
