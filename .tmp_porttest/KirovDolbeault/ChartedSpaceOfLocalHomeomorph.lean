import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# `ChartedSpace` from a surjective local homeomorphism

If `f : X → Y` is a surjective local homeomorphism (e.g. a covering map),
then `Y` inherits a `ChartedSpace X Y` structure: at each `y : Y`, the
chart is the inverse of a partial homeomorphism agreeing with `f` near a
chosen preimage of `y`.

We do not register this as an instance — the constructor
`chartedSpaceOfIsLocalHomeomorph` is intended to be supplied explicitly
in contexts like `Jacobians.ZLatticeQuotient`.

Candidate for Mathlib upstreaming.
-/

namespace IsLocalHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A partial homeomorphism agreeing with `f` near `x`, chosen by
`Classical.choose`. -/
noncomputable def chartAtPreimageKirov {f : X → Y} (hf : IsLocalHomeomorph f)
    (x : X) : OpenPartialHomeomorph X Y :=
  Classical.choose (hf x)

lemma mem_source_chartAtPreimageKirov {f : X → Y} (hf : IsLocalHomeomorph f)
    (x : X) : x ∈ (chartAtPreimageKirov hf x).source :=
  (Classical.choose_spec (hf x)).1

lemma eq_chartAtPreimageKirov {f : X → Y} (hf : IsLocalHomeomorph f) (x : X) :
    f = chartAtPreimageKirov hf x :=
  (Classical.choose_spec (hf x)).2

-- `IsLocalHomeomorph.chartedSpace` is now in Mathlib (c5ea003+) with a different internal
-- construction. We provide a variant `chartedSpaceOfAtPreimage` built from `chartAtPreimageKirov`
-- so that downstream proofs using `show`/`change` against `P.symm` remain valid.
/-- Charted space structure on `Y` induced by a surjective local homeomorphism `f : X → Y`,
with charts explicitly `(chartAtPreimageKirov hf _).symm`. This construction is definitionally
transparent: `chartAt y = (chartAtPreimageKirov hf (Classical.choose (hs y))).symm`.
(The Mathlib `IsLocalHomeomorph.chartedSpace` uses a different construction;
this variant is kept for proofs that case-split on the chart atlas directly.) -/
@[implicit_reducible]
noncomputable def chartedSpaceOfAtPreimage {f : X → Y} (hf : IsLocalHomeomorph f)
    (hs : Function.Surjective f) : ChartedSpace X Y where
  atlas := Set.range fun y : Y =>
    (chartAtPreimageKirov hf (Classical.choose (hs y))).symm
  chartAt y := (chartAtPreimageKirov hf (Classical.choose (hs y))).symm
  mem_chart_source y := by
    set x := Classical.choose (hs y) with hx
    have hfx : f x = y := Classical.choose_spec (hs y)
    show y ∈ (chartAtPreimageKirov hf x).target
    have hxs : x ∈ (chartAtPreimageKirov hf x).source := mem_source_chartAtPreimageKirov hf x
    have := (chartAtPreimageKirov hf x).map_source hxs
    rwa [← eq_chartAtPreimageKirov hf x, hfx] at this
  chart_mem_atlas y := ⟨y, rfl⟩

end IsLocalHomeomorph
