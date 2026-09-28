import PoincareConjecture.Proofs.M25.Topology3D.Plane.HalfspaceExterior
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.Regions











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}



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



theorem closure_polygonInterior_subset_linear_lower_bound (p : Polygon E n)
    (X : E →L[ℝ] ℝ) (hX : Function.Surjective X) (c : ℝ)
    (hvertices : ∀ i, c ≤ X (p i)) :
    closure (polygonInterior p) ⊆ {x | c ≤ X x} := by
  apply closure_minimal ?_ (isClosed_le continuous_const X.continuous)
  intro x hx
  by_contra hle
  have hxO := polygonExterior_of_lt_vertex_bound p X hX c hvertices (lt_of_not_ge hle)
  exact hxO.2 hx.2

end PoincareConjecture.M25.Topology3D
