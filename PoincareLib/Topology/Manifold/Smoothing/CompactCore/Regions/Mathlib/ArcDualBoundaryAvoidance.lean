import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.Mathlib.FiniteContactEdgeVertex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricDualSubcomplex

/-!
# Actual arc joints avoid the whole old-frontier carrier

Fullness and finite complete contact force an original edge vertex
outside the retained boundary. The edge is therefore not a boundary
face, and the exact dual/subcomplex intersection is empty. Both whole
endpoint feet are subsets of that same boundary carrier.
See Wall013, section 4, Hudson 1969, pp. 8--10, 58--63.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

/-- Every actual arc-edge dual misses the entire retained boundary
carrier. Its actual outside-boundary vertex is also returned for
the original interior-point and joint-disk construction. This proves
avoidance of both whole endpoint feet. See Wall013, section 4. -/
theorem arc_edge_dual_disjoint_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A D : SimplicialComplex ℝ E) [Fintype K.faces]
    (hAK : A ≤ K) (hDK : D ≤ K)
    (hfull : ∀ t ∈ K.faces, (∀ p ∈ t, p ∈ D.vertices) → t ∈ D.faces)
    (hfinite : (A.space ∩ D.space).Finite)
    {s : Finset E} (hs : s ∈ A.faces) (hcard : s.card = 2) :
    Disjoint (K.barycentricDualBlock s).space D.space ∧ ∃ p ∈ s, p ∉ D.vertices := by
  classical
  let : Fintype D.faces := ((Set.toFinite K.faces).subset (fun _ hs => hDK hs)).fintype
  obtain ⟨p, hps, hpD⟩ :=
    exists_edge_vertex_outside_of_finite_contact hAK hfull hfinite hs hcard
  have hsD : s ∉ D.faces := fun h => hpD (D.face_subset_vertices h hps)
  refine ⟨?_, p, hps, hpD⟩
  rw [disjoint_iff_inter_eq_empty, K.barycentricDualBlock_space_inter_subcomplex D hDK]
  exact D.barycentricDualBlock_space_eq_empty_of_not_face (A.nonempty_of_mem_faces hs) hsD

end Geometry.SimplicialComplex
