/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Free
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality
public import Other.Oka.AnalyticSpace.Coherent
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules
public import Other.TauCeti.SheafOfModules.LocalTriviality

/-!
# Coherence of invertible sheaves

An invertible sheaf over a coherent structure sheaf is coherent. This applies in particular to
the structure sheaf of a complex analytic space once Oka's coherence theorem is available.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- An invertible sheaf over a coherent structure sheaf is coherent. -/
theorem isCoherent_of_isInvertible (Y : LocallyRingedSpace.{u})
    (M : SheafOfModules.{u} Y.ringSheaf)
    [hY : (SheafOfModules.unit Y.ringSheaf).IsCoherent]
    [TauCeti.SheafOfModules.IsInvertible.{u, u, u} M] : M.IsCoherent := by
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  let (i : t.I) :
      (SheafOfModules.unit (Y.ringSheaf.over (t.X i))).IsCoherent :=
    SheafOfModules.IsCoherent.over (SheafOfModules.unit Y.ringSheaf) (t.X i)
  let (i : t.I) :
      (SheafOfModules.free (R := Y.ringSheaf.over (t.X i)) PUnit).IsCoherent :=
    SheafOfModules.IsCoherent.freePUnit
  let (i : t.I) : (M.over (t.X i)).IsCoherent :=
    SheafOfModules.IsCoherent.of_iso.{u, u, u}
      (M := SheafOfModules.free (R := Y.ringSheaf.over (t.X i)) PUnit) (t.iso i)
  exact SheafOfModules.IsCoherent.of_coversTop M t.X t.coversTop

end AlgebraicGeometry.LocallyRingedSpace

namespace ComplexAnalytic

/-- An invertible sheaf on a complex analytic space is coherent. -/
theorem AnalyticSpace.isCoherent_of_isInvertible (X : AnalyticSpace.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf)
    [TauCeti.SheafOfModules.IsInvertible.{u, u, u} M] : M.IsCoherent := by
  letI : (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf).IsCoherent :=
    X.isCoherentStructureSheaf
  exact X.toLocallyRingedSpace.isCoherent_of_isInvertible M

end ComplexAnalytic
