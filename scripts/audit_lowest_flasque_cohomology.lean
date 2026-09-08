import HodgeConjecture.Other.AlgebraicTopology.LowestFlasqueCohomology

/-! Audit of all principal declarations in the canonical lowest-degree flasque comparison.
Run with `lake env lean scripts/audit_lowest_flasque_cohomology.lean`. -/

#print axioms TopCat.Sheaf.IsFlasque.shortExact_map_forget
#print axioms TopCat.Sheaf.IsFlasque.kernelImageShortComplex
#print axioms TopCat.Sheaf.IsFlasque.kernelImageShortComplex_shortExact
#print axioms TopCat.Sheaf.IsFlasque.imageCokernelShortComplex
#print axioms TopCat.Sheaf.IsFlasque.imageCokernelShortComplex_shortExact
#print axioms TopCat.Sheaf.IsFlasque.image_isFlasque
#print axioms TopCat.Sheaf.IsFlasque.forget_preservesCokernel
#print axioms TopCat.Sheaf.kernelBoundaryToCyclesIso
#print axioms TopCat.Sheaf.forget_preservesLeftHomologyOf_lowest
#print axioms TopCat.Sheaf.sectionCohomologyPresheaf_isSheaf_lowest
#print axioms TopCat.Sheaf.sectionCohomologyPresheafToSheaf_isIso_lowest
#print axioms TopCat.Sheaf.sectionCohomologyToSheafSection_isIso_lowest
#print axioms TopCat.Sheaf.lowestSectionCohomologyIso
#print axioms TopCat.Sheaf.lowestSectionCohomologyIso_hom
#print axioms TopCat.Sheaf.lowestGlobalSectionCohomologyIso
#print axioms TopCat.Sheaf.lowestGlobalSectionCohomologyIso_hom

#check @TopCat.Sheaf.forget_preservesLeftHomologyOf_lowest
#check @TopCat.Sheaf.sectionCohomologyPresheaf_isSheaf_lowest
#check @TopCat.Sheaf.sectionCohomologyToSheafSection_isIso_lowest
#check @TopCat.Sheaf.lowestGlobalSectionCohomologyIso
#check @TopCat.Sheaf.lowestGlobalSectionCohomologyIso_hom
