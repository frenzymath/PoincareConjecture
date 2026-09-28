import PoincareConjecture.Proofs.M76.Mathlib.PureEdgeComplexPolygon
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem ncard_link_neighbors_eq_triangle_cofaces (K : SimplicialComplex ℝ E)
    (q : E) (v : (K.link q).vertices) :
    ((K.link q).vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ ({q, (v : E)} : Finset E) ⊆ t}.ncard := by
  have hqv : q ≠ (v : E) := fun h => v.property.2.1 (Finset.mem_singleton.mpr h)
  have hdisj : Disjoint ({q} : Finset E) {v.val} := by
    simpa only [Finset.disjoint_singleton_left, Finset.mem_singleton] using hqv
  rw [(K.link q).ncard_edgeGraph_neighborSet v]
  have hlink : (K.link q).faceLink {v.val} = K.faceLink {q, v.val} := by
    calc
      _ = (K.faceLink {q}).faceLink {v.val} :=
        congrArg (fun J : SimplicialComplex ℝ E => J.faceLink {v.val})
          (K.faceLink_singleton_eq_link q).symm
      _ = K.faceLink {q, v.val} := by
        simpa only [Finset.singleton_union] using K.faceLink_faceLink _ _ hdisj
  rw [hlink, K.ncard_faceLink_vertices_eq_cofaces, Finset.card_pair hqv]

theorem exists_surface_link_polygon (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (q : E) (hconn : (K.link q).vertexAbstractComplex.edgeGraph.Connected) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (K.link q).space := by
  have hpureL : ∀ s ∈ (K.link q).faces,
      ∃ t ∈ (K.link q).faces, t.card = 2 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, htc, hst⟩ := hpure (insert q s) hs.2.2
    have hqt : q ∈ t := hst (Finset.mem_insert_self q s)
    have hcard : (t.erase q).card = 2 := by
      rw [Finset.card_erase_of_mem hqt, htc]
    have hne : (t.erase q).Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨t.erase q, ⟨K.down_closed ht (Finset.erase_subset _ _) hne,
      Finset.notMem_erase _ _, ?_⟩, hcard, ?_⟩
    · simpa only [Finset.insert_erase hqt] using ht
    · intro v hv
      exact Finset.mem_erase.mpr
        ⟨fun hvq => hs.2.1 (hvq ▸ hv), hst (Finset.mem_insert_of_mem hv)⟩
  apply (K.link q).exists_polygon_of_pure_edges (finite_link_faces hK q) hpureL hconn
  intro v
  rw [K.ncard_link_neighbors_eq_triangle_cofaces]
  have hqv : q ≠ (v : E) := fun h => v.property.2.1 (Finset.mem_singleton.mpr h)
  exact hcofaces {q, v.val} v.property.2.2 (Finset.card_pair hqv)

end Geometry.SimplicialComplex
