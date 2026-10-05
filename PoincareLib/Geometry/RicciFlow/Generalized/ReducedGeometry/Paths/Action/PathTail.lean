import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.PathRestriction

/-!
# Restriction retaining the prescribed final endpoint

The tail used to splice a competing prefix into an actual full path,
Morgan-Tian Definition 6.2 and Proposition 6.30, pp. 106, 118-119.
The curve and velocity are unchanged; the original endpoint witness
is retained in the path type.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

/-- Restrict an actual path to a tail while retaining its prescribed
final endpoint, Definition 6.2 and Proposition 6.30, pp. 106, 118-119. -/
def tailPath (p : M14BackwardPath G T τ₁ τ₂ x y) (a : ℝ)
    (ha : τ₁ ≤ a) (hab : a < τ₂) : M14BackwardPath G T a τ₂ (p.curve a) y :=
  { restrictPath p a τ₂ ha hab le_rfl with
    endpoint_time := p.endpoint_time
    curve_end := p.curve_end }

end PoincareMT.M14
