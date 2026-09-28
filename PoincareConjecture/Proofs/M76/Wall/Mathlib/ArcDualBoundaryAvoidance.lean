import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteContactEdgeVertex
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

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
