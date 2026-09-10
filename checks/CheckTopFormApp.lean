import Other.AlgebraicGeometry.ExplicitEllipticSurfaceTopFormCech

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

#check SheafOfModules.unitHomEquiv
#check SheafOfModules.unitHomEquiv_apply_coe
#check PresheafOfModules.unitHomEquiv
#check PresheafOfModules.unitHomEquiv_apply_coe
#check PresheafOfModules.sheafificationCompToSheaf
#check holomorphicDeRhamOSheafToAdditiveIso
#check moduleSectionsOfTop
#check holomorphicTopFormMultiplicationSheaf
#check PresheafOfModules.sheafificationAdjunction
#check PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
#check PresheafOfModules.Sheafify.map_smul_eq
#print PresheafOfModules.Sheafify.map_smul_eq
set_option pp.universes true in
#check holomorphicDeRhamOSheaf
set_option pp.universes true in
#check PresheafOfModules.sheafificationAdjunction

variable (X : Over (Spec (.of ℂ))) (d p : ℕ)
  [SmoothOfRelativeDimension d X.hom]

set_option pp.universes false in
set_option pp.all false in
example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (s : (holomorphicDeRhamSheaf X d p).obj.obj (.op ⊤))
    (a : OpenHolomorphicFunctions X d U) :
    (holomorphicTopFormMultiplicationSheaf X d p s).hom.app U a =
      (holomorphicDeRhamOSheafToAdditiveIso X d p).hom.hom.app U
        ((show (holomorphicRingSheaf X d).obj.obj U from a) •
          (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
            (holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app U
              ((holomorphicDeRhamSheaf X d p).obj.map
                (homOfLE (le_top : U.unop ≤ ⊤)).op s))) := by
  change _ = _
  simp only [holomorphicTopFormMultiplicationSheaf, Category.assoc,
    NatTrans.comp_app, ConcreteCategory.comp_apply]
  change (((holomorphicDeRhamOSheaf X d p).unitHomEquiv.symm
    (moduleSectionsOfTop X d
      ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s))).val.app U) a = _
  change (show (holomorphicRingSheaf X d).obj.obj U from a) •
    (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
      (moduleSectionsOfTop X d
        ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s)).val U) = _
  dsimp only [moduleSectionsOfTop, PresheafOfModules.sectionsMk]
  rw [← ConcreteCategory.comp_apply,
    (holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.naturality]
  rfl

example (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (s : (holomorphicDeRhamSheaf X d p).obj.obj (.op ⊤))
    (a : OpenHolomorphicFunctions X d U)
    (w : HolomorphicForm X d U p)
    (hs : (holomorphicDeRhamSheaf X d p).obj.map
              (homOfLE (le_top : U.unop ≤ ⊤)).op s =
            (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
              (holomorphicDeRhamPresheaf X d p)).app U w) :
    (holomorphicTopFormMultiplicationSheaf X d p s).hom.app U a =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app U
          (holomorphicFormFunctionMul X d U p a w) := by
  rw [show (holomorphicTopFormMultiplicationSheaf X d p s).hom.app U a =
      (holomorphicDeRhamOSheafToAdditiveIso X d p).hom.hom.app U
        ((show (holomorphicRingSheaf X d).obj.obj U from a) •
          (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
            (holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app U
              ((holomorphicDeRhamSheaf X d p).obj.map
                (homOfLE (le_top : U.unop ≤ ⊤)).op s))) by
    change _ = _
    simp only [holomorphicTopFormMultiplicationSheaf]
    change (((holomorphicDeRhamOSheaf X d p).unitHomEquiv.symm
      (moduleSectionsOfTop X d
        ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s))).val.app U) a = _
    change (show (holomorphicRingSheaf X d).obj.obj U from a) •
      (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
        (moduleSectionsOfTop X d
          ((holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.app (.op ⊤) s)).val U) = _
    dsimp only [moduleSectionsOfTop, PresheafOfModules.sectionsMk]
    rw [← ConcreteCategory.comp_apply,
      (holomorphicDeRhamOSheafToAdditiveIso X d p).inv.hom.naturality]
    rfl]
  rw [hs]
  dsimp [holomorphicDeRhamOSheafToAdditiveIso,
    PresheafOfModules.sheafificationCompToSheaf]
  change (show (holomorphicRingSheaf X d).obj.obj U from a) •
      (show ↑((holomorphicDeRhamOSheaf X d p).val.obj U) from
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app U w) =
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)).app U
        (holomorphicFormFunctionMul X d U p a w)
  let hφinj : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)) :=
    ((Opens.grothendieckTopology (TopCat.of (ComplexPoint X))).W_toSheafify
      (holomorphicDeRhamPresheaf X d p)).isLocallyInjective
  let hφsurj : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)) :=
    ((Opens.grothendieckTopology (TopCat.of (ComplexPoint X))).W_toSheafify
      (holomorphicDeRhamPresheaf X d p)).isLocallySurjective
  have h :=
    @PresheafOfModules.Sheafify.map_smul_eq
      (Opens (TopCat.of (ComplexPoint X))) _
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicRingSheaf X d).obj
      (holomorphicRingSheaf X d)
      (𝟙 (holomorphicRingSheaf X d).obj)
      (inferInstance) (inferInstance)
      (holomorphicDeRhamOPresheaf X d p)
      (holomorphicDeRhamSheaf X d p)
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p))
      hφinj hφsurj
      U
      (show (holomorphicRingSheaf X d).obj.obj U from a)
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)).app U w)
      U (𝟙 U) a (by simp) w (by
        exact ((holomorphicDeRhamSheaf X d p).obj.map_id_apply U _).symm)
  exact ((holomorphicDeRhamSheaf X d p).obj.map_id_apply U _).symm.trans h

end AlgebraicGeometry.ComplexPoint
