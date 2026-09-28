import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangulationData
import PoincareConjecture.Proofs.M76.Mathlib.PolygonDiagonalStrings
import PoincareConjecture.Proofs.M76.Mathlib.PolygonDiagonalPartition
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialCompatibleUnion

set_option autoImplicit false

open Set Geometry

namespace Polygon

theorem exists_triangulation_of_split {m n : ℕ} (u : Fin (m + 2) → ℝ × ℝ)
    (v : Fin (n + 2) → ℝ × ℝ)
    (hP : (mk (Fin.append u v)).HasSimplicialEdges)
    (hinj : Function.Injective (Fin.append u v))
    (hdiagonal : openSegment ℝ (u 0) (v 0) ⊆ (mk (Fin.append u v)).inside)
    (C D : SimplicialComplex ℝ (ℝ × ℝ))
    (hC : (mk (Fin.snoc u (v 0))).IsTriangulation C)
    (hD : (mk (Fin.snoc v (u 0))).IsTriangulation D) :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), (mk (Fin.append u v)).IsTriangulation K := by
  classical
  obtain ⟨_, hcover, hinter⟩ := region_partition_split u v hP hinj hdiagonal
  let d : Finset (ℝ × ℝ) := {u 0, v 0}
  have hdC : d ∈ C.faces := by
    have heq : (mk (Fin.snoc u (v 0))).edgeVertices (Fin.last (m + 2)) = d := by
      apply Finset.coe_injective
      rw [edgeVertices_snoc_last]
      simp [d, pair_comm]
    exact heq ▸ hC.edge_mem (Fin.last (m + 2))
  have hdD : d ∈ D.faces := by
    have heq : (mk (Fin.snoc v (u 0))).edgeVertices (Fin.last (n + 2)) = d := by
      apply Finset.coe_injective
      rw [edgeVertices_snoc_last]
      simp [d]
    exact heq ▸ hD.edge_mem (Fin.last (n + 2))
  have hCD : C.space ∩ D.space ⊆ convexHull ℝ (d : Set (ℝ × ℝ)) := by
    rw [hC.space_eq, hD.space_eq, hinter]
    simp only [d, Finset.coe_pair, convexHull_pair, Subset.rfl]
  have hcross := fun s hs t ht => C.cross_inter_subset_of_common_face D d hdC hdD hCD
    (s := s) (t := t) hs ht
  let K := C.unionOfCompatible D hcross
  refine ⟨K, ?_⟩
  constructor
  · exact C.finite_faces_unionOfCompatible D hcross hC.finite_faces hD.finite_faces
  · rw [C.space_unionOfCompatible, hC.space_eq, hD.space_eq]
    exact hcover.symm
  · intro x hx
    rcases hx with hx | hx
    · exact (range_split_subset u v).1 (hC.vertices_subset hx)
    · exact (range_split_subset u v).2 (hD.vertices_subset hx)
  · intro i
    change _ ∈ C.faces ∪ D.faces
    induction i using Fin.addCases with
    | left i =>
      rw [← edgeVertices_split_left u v i]
      exact Or.inl (hC.edge_mem i.castSucc)
    | right i =>
      rw [← edgeVertices_split_right u v i]
      exact Or.inr (hD.edge_mem i.castSucc)
  · intro s hs
    rcases hs with hs | hs
    · obtain ⟨t, ht, hst, hcard⟩ := hC.pure s hs
      exact ⟨t, Or.inl ht, hst, hcard⟩
    · obtain ⟨t, ht, hst, hcard⟩ := hD.pure s hs
      exact ⟨t, Or.inr ht, hst, hcard⟩

end Polygon
