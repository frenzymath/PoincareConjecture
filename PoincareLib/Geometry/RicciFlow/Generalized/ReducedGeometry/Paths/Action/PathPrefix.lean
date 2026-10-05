import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.PathRestriction

/-!
# Restriction retaining the prescribed initial endpoint

The prefix used in Morgan-Tian Proposition 6.30, pp. 118-119,
retains the actual curve, velocity and prescribed initial endpoint.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

/-- Restrict an actual path to a prefix while retaining its prescribed
initial endpoint, Definition 6.2 and Proposition 6.30, pp. 106, 118-119. -/
def prefixPath (p : M14BackwardPath G T τ₁ τ₂ x y) (b : ℝ)
    (hab : τ₁ < b) (hb : b ≤ τ₂) : M14BackwardPath G T τ₁ b x (p.curve b) :=
  { restrictPath p τ₁ b le_rfl hab hb with
    base_time := p.base_time
    curve_start := p.curve_start }

end PoincareMT.M14
