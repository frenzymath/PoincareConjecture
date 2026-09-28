import PoincareConjecture.Proofs.M14.Sec6_1_PathRestriction

set_option autoImplicit false

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

def prefixPath (p : M14BackwardPath G T τ₁ τ₂ x y) (b : ℝ)
    (hab : τ₁ < b) (hb : b ≤ τ₂) : M14BackwardPath G T τ₁ b x (p.curve b) :=
  { restrictPath p τ₁ b le_rfl hab hb with
    base_time := p.base_time
    curve_start := p.curve_start }

end PoincareConjecture.M14
