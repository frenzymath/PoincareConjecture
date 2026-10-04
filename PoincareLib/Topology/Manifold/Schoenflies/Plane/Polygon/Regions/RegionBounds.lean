import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.HalfspaceExterior
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.Regions

/-!
# Vertex linear bounds for polygon regions

The supporting-line ingredient in Munkres (1960), Lemma 2.3, p. 195.
Points strictly below every vertex lie in the canonical exterior; the
closed inside obeys every such weak supporting bound. The proofs work
for arbitrary polygons in real normed spaces without a Jordan input.
See `smale/derivations/2026-09-21-region-linear-bounds.md` for the derivation.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- A point below a linear lower bound for every vertex is outside the polygon;
the supporting-line exterior step for Munkres, Lemma 2.3, p. 195. -/
theorem polygonExterior_of_lt_vertex_bound (p : Polygon E n) (X : E →L[ℝ] ℝ)
    (hX : Function.Surjective X) (c : ℝ) (hvertices : ∀ i, c ≤ X (p i))
    {x : E} (hx : X x < c) : x ∈ polygonExterior p := by
  have hHull : convexHull ℝ (range p) ⊆ {z | c ≤ X z} :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hvertices i)
      ((convex_Ici (𝕜 := ℝ) c).linear_preimage X.toLinearMap)
  have hC : p.boundary ℝ ⊆ {z | c ≤ X z} :=
    (polygon_boundary_subset_convexHull p).trans hHull
  refine ⟨?_, not_isBounded_compl_component_of_lt_linear_bound X hX c hC hx⟩
  intro hxC
  exact (not_lt_of_ge (show c ≤ X x from hC hxC)) hx

/-- The closed inside obeys every linear lower bound on the vertices;
the supporting-line constraint used in Munkres, Lemma 2.3, p. 195. -/
theorem closure_polygonInterior_subset_linear_lower_bound (p : Polygon E n)
    (X : E →L[ℝ] ℝ) (hX : Function.Surjective X) (c : ℝ)
    (hvertices : ∀ i, c ≤ X (p i)) :
    closure (polygonInterior p) ⊆ {x | c ≤ X x} := by
  apply closure_minimal ?_ (isClosed_le continuous_const X.continuous)
  intro x hx
  by_contra hle
  have hxO := polygonExterior_of_lt_vertex_bound p X hX c hvertices (lt_of_not_ge hle)
  exact hxO.2 hx.2

end Poincare.Manifold.Schoenflies.Plane
