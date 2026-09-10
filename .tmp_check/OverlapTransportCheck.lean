import Other.AlgebraicGeometry.ExplicitEllipticCMHolomorphicFunctions
import Other.AlgebraicGeometry.ExplicitEllipticCurveCechResidueBridge

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

#check Iso.hom_inv_id_apply
#check Iso.inv_hom_id_apply

example :
    (curveCMOverlap.ι.appIso ⊤).inv ≫
        curveVariety.left.presheaf.map
          (eqToHom curveCMOverlap.ι_image_top.symm).op =
      curveCMOverlap.topIso.hom := by
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv,
    Scheme.Opens.topIso]
  change curveVariety.left.presheaf.map
      (eqToHom curveCMOverlap.ι_image_top.symm).op =
    curveVariety.left.presheaf.map
      (eqToHom curveCMOverlap.ι_image_top.symm).op
  rfl

end AlgebraicGeometry.ExplicitEllipticCandidate
