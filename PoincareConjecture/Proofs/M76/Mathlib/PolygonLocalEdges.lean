import PoincareConjecture.Proofs.M76.Mathlib.PolygonEdgeIntersections
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem isClosed_edgeSet (P : Polygon E n) (i : Fin n) : IsClosed (P.edgeSet ℝ i) := by
  rw [P.edgeSet_eq_convexHull]
  exact (P.edgeVertices i).finite_toSet.isClosed_convexHull ℝ

theorem isClosed_boundary (P : Polygon E n) : IsClosed (P.boundary ℝ) :=
  isClosed_iUnion_of_finite P.isClosed_edgeSet

theorem eventually_boundary_iff_incident_edges (P : Polygon E n) (q : E) :
    ∀ᶠ x in 𝓝 q, x ∈ P.boundary ℝ ↔ ∃ i, q ∈ P.edgeSet ℝ i ∧ x ∈ P.edgeSet ℝ i := by
  have h (i : Fin n) : ∀ᶠ x in 𝓝 q, x ∈ P.edgeSet ℝ i → q ∈ P.edgeSet ℝ i := by
    by_cases hq : q ∈ P.edgeSet ℝ i
    · exact Eventually.of_forall fun _ _ => hq
    · filter_upwards [(P.isClosed_edgeSet i).isOpen_compl.mem_nhds hq] with x hx
      exact fun hi => (hx hi).elim
  filter_upwards [Filter.eventually_all.mpr h] with x hx
  constructor
  · intro hxb
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxb
    exact ⟨i, hx i hi, hi⟩
  · rintro ⟨i, _, hi⟩
    exact mem_iUnion.mpr ⟨i, hi⟩

theorem vertex_mem_edgeSet_iff (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (i j : Fin n) :
    P i ∈ P.edgeSet ℝ j ↔ i = j ∨ i = finRotate n j := by
  have hv : P i ∈ (P.simplicialComplex hP).vertices := by
    rw [P.simplicialComplex_vertices]
    exact mem_range_self i
  rw [P.edgeSet_eq_convexHull,
    (P.simplicialComplex hP).vertex_mem_convexHull_iff hv (P.edgeVertices_mem_faces hP j)]
  simp only [edgeVertices, Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff]

theorem eventually_boundary_iff_adjacent_edges (P : Polygon E n)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin n) :
    ∀ᶠ x in 𝓝 (P i), x ∈ P.boundary ℝ ↔
      x ∈ P.edgeSet ℝ ((finRotate n).symm i) ∪ P.edgeSet ℝ i := by
  filter_upwards [P.eventually_boundary_iff_incident_edges (P i)] with x hx
  rw [hx]
  constructor
  · rintro ⟨j, hj, hxj⟩
    rw [P.vertex_mem_edgeSet_iff hP hinj] at hj
    rcases hj with rfl | hj
    · exact Or.inr hxj
    · have hji : j = (finRotate n).symm i := by rw [hj, Equiv.symm_apply_apply]
      exact Or.inl (hji ▸ hxj)
  · rintro (hp | hn)
    · refine ⟨_, ?_, hp⟩
      exact (P.vertex_mem_edgeSet_iff hP hinj i _).mpr
        (Or.inr (Equiv.apply_symm_apply _ _).symm)
    · exact ⟨i, (P.vertex_mem_edgeSet_iff hP hinj i i).mpr (Or.inl rfl), hn⟩

theorem eventually_boundary_iff_single_edge (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) {q : E}
    (hqv : q ∉ range P) {i : Fin (n + 3)} (hqi : q ∈ P.edgeSet ℝ i) :
    ∀ᶠ x in 𝓝 q, x ∈ P.boundary ℝ ↔ x ∈ P.edgeSet ℝ i := by
  filter_upwards [P.eventually_boundary_iff_incident_edges q] with x hx
  rw [hx]
  constructor
  · rintro ⟨j, hqj, hxj⟩
    have hji := P.eq_of_mem_edgeSets_of_not_vertex hP hinj hqv hqj hqi
    exact hji ▸ hxj
  · intro hxi
    exact ⟨i, hqi, hxi⟩

end Polygon
