import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskConnectedLink
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskEdgeCofaces
import PoincareConjecture.Proofs.M76.Mathlib.SurfaceLinkPolygon










set_option autoImplicit false

open Set
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [DecidableEq E] in


theorem ncard_triangle_cofaces_eq_two_of_local_disk_at_vertex
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : E} (hps : p ∈ s) {d rim : Set E}
    (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim) (hdK : d ⊆ K.space)
    (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space)) :
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
  have hpK : p ∈ K.space := K.subset_space hs hps
  have hpU : p ∈ U := (Set.ext_iff.mp hUeq ⟨p, hpK⟩).mpr hpd
  obtain ⟨x, hxs, hxU⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
      hU ⟨p, subset_convexHull ℝ _ hps, hpU⟩
  have hxK : x ∈ K.space := K.convexHull_subset_space hs (intrinsicInterior_subset hxs)
  have hxd : x ∈ d \ rim := (Set.ext_iff.mp hUeq ⟨x, hxK⟩).mp hxU
  exact K.ncard_triangle_cofaces_eq_two_of_local_disk hK hbound hs hs2 hxs hd hdK hxd hopen




theorem exists_link_polygon_of_local_finitePLDisk
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {p : E} (hp : p ∈ K.vertices) {d rim : Set E}
    (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim) (hdK : d ⊆ K.space)
    (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space)) :
    ∃ (n : ℕ) (Q : Polygon E (n + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ Q.boundary ℝ = (K.link p).space := by
  classical
  let L := K.link p
  have hL : L.faces.Finite := finite_link_faces hK p
  have hconn : IsConnected L.space :=
    K.isConnected_link_of_local_finitePLBallPair (by simp) hK hp hd hdK hpd hopen
  have hdegree (v : L.vertices) :
      (L.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
    rw [K.ncard_link_neighbors_eq_triangle_cofaces]
    have hpv : p ≠ (v : E) := fun h => v.property.2.1 (Finset.mem_singleton.mpr h)
    exact K.ncard_triangle_cofaces_eq_two_of_local_disk_at_vertex hK hbound
      v.property.2.2 (Finset.card_pair hpv) (Finset.mem_insert_self _ _) hd hdK hpd hopen
  have hpure : ∀ s ∈ L.faces, ∃ t ∈ L.faces, t.card = 2 ∧ s ⊆ t := by
    intro s hs
    have hscard : s.card ≤ 2 := by
      have h := hbound (insert p s) hs.2.2
      rw [Finset.card_insert_of_notMem hs.2.1] at h
      omega
    by_cases hs2 : s.card = 2
    · exact ⟨s, hs, hs2, Finset.Subset.rfl⟩
    · have hs1 : s.card = 1 := by
        have := Finset.card_pos.mpr (L.nonempty_of_mem_faces hs)
        omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs1
      let vL : L.vertices := ⟨v, hs⟩
      obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hdegree vL]; norm_num)
      have hwlink := (L.edgeGraph_adj_iff_mem_faceLink vL w).mp hw
      have hvw : v ≠ w.val := fun h => hw.1 (Subtype.ext h)
      refine ⟨{v, w.val}, ?_, Finset.card_pair hvw, ?_⟩
      · simpa only [Finset.singleton_union] using hwlink.2.2
      · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  exact L.exists_polygon_of_pure_edges hL hpure
    (L.connected_edgeGraph_of_isConnected hL hconn) hdegree

end Geometry.SimplicialComplex
