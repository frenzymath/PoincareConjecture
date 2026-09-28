import PoincareConjecture.Proofs.M14.Sec6_1_PathRestriction










set_option autoImplicit false

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}



def tailPath (p : M14BackwardPath G T τ₁ τ₂ x y) (a : ℝ)
    (ha : τ₁ ≤ a) (hab : a < τ₂) : M14BackwardPath G T a τ₂ (p.curve a) y :=
  { restrictPath p a τ₂ ha hab le_rfl with
    endpoint_time := p.endpoint_time
    curve_end := p.curve_end }

end PoincareConjecture.M14
