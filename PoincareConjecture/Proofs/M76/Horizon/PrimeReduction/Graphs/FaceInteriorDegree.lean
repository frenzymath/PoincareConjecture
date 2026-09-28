import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.PlaneHeight
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.TwoSegmentGermDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskEdgeCofaces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.TransverseEdgeFaceGerm
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.TransverseTriangleInteriorSection












set_option autoImplicit false

open Set Geometry Filter Module
open scoped Topology

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)



theorem exists_two_segment_section_of_transverse_face
    (P : SimplicialComplex ℝ V3) (hP : P.faces.Finite)
    (hbound : ∀ a ∈ P.faces, a.card ≤ 3)
    {a : Finset V3} (ha : a ∈ P.faces) {w : V3}
    (hwa : w ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
    (A : V3 →ᵃ[ℝ] ℝ) (hwzero : A w = 0) (hne : ∃ v ∈ a, A v ≠ 0)
    (hdisk : ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q))) :
    ∃ u v : V3, u ≠ w ∧ v ≠ w ∧
      segment ℝ w u ∩ segment ℝ w v = {w} ∧
      ∀ᶠ x in 𝓝 w, x ∈ P.space ∩ {y | A y = 0} ↔
        x ∈ segment ℝ w u ∪ segment ℝ w v := by
  classical
  have hac := hbound a ha
  have hapos := Finset.card_pos.mpr (P.nonempty_of_mem_faces ha)
  have haone : a.card ≠ 1 := by
    intro h
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
    have hwv : w = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        intrinsicInterior_subset hwa
    obtain ⟨v', hv', hvzero⟩ := hne
    have hv'v := Finset.mem_singleton.mp hv'
    exact hvzero (hv'v.trans hwv.symm ▸ hwzero)
  have hsection : ∃ u v : V3, u ≠ w ∧ v ≠ w ∧
      segment ℝ w u ∩ segment ℝ w v = {w} ∧
      ∀ᶠ x in 𝓝 w, x ∈ P.space ∩ {y | A y = 0} ↔
        x ∈ segment ℝ w u ∪ segment ℝ w v := by
    by_cases ha2 : a.card = 2
    · obtain ⟨d, q, hd, hdP, hwd, hopen⟩ := hdisk
      obtain ⟨b, c, hbc, hset⟩ := ncard_eq_two.mp
        (P.ncard_triangle_cofaces_eq_two_of_local_disk hP hbound ha ha2 hwa hd hdP hwd hopen)
      have hb : b ∈ P.faces ∧ b.card = 3 ∧ a ⊆ b := by
        change b ∈ {b | b ∈ P.faces ∧ b.card = 3 ∧ a ⊆ b}
        rw [hset]
        exact Or.inl rfl
      have hc : c ∈ P.faces ∧ c.card = 3 ∧ a ⊆ c := by
        change c ∈ {b | b ∈ P.faces ∧ b.card = 3 ∧ a ⊆ b}
        rw [hset]
        exact Or.inr rfl
      have hexhaust (z : Finset V3) (hz : z ∈ P.faces) (haz : a ⊆ z) : z ⊆ b ∨ z ⊆ c := by
        have hlow := Finset.card_le_card haz
        have hupper := hbound z hz
        by_cases hz2 : z.card = 2
        · have he : a = z := Finset.eq_of_subset_of_card_le haz (by omega)
          exact Or.inl (he ▸ hb.2.2)
        · have hmem : z ∈ {b | b ∈ P.faces ∧ b.card = 3 ∧ a ⊆ b} := ⟨hz, by omega, haz⟩
          rw [hset] at hmem
          exact hmem.elim (fun h => Or.inl (h ▸ Finset.Subset.rfl))
            (fun h => Or.inr (h ▸ Finset.Subset.rfl))
      exact P.exists_transverse_edge_two_segment_germ hP ha ha2 hb.1 hc.1 hb.2.1 hc.2.1
        hb.2.2 hc.2.2 hbc hexhaust A hwa hwzero hne
    · exact P.exists_transverse_triangle_interior_two_segment_germ hP hbound
        (by simp) ha (by omega) A hwa hwzero hne
  exact hsection



theorem ncard_face_graph_neighbors_of_local_disks_outside_protection
    (P J T G : SimplicialComplex ℝ V3) (hP : P.faces.Finite)
    (hbound : ∀ a ∈ P.faces, a.card ≤ 3)
    (hdisks : ∀ w ∈ P.space, w ∈ interior J.space →
      ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
        w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)))
    {t : Finset V3} (ht : t ∈ T.faces) (ht3 : t.card = 3)
    (hG : G.faces.Finite) (hGs : G.space = P.space ∩ convexHull ℝ (t : Set V3))
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    {Z : Set V3}
    (hpos : ∀ a ∈ P.faces, convexHull ℝ (a : Set V3) ⊆ Z ∨
      affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
        (convexHull ℝ (t : Set V3)))
    {w : V3} (hwG : w ∈ G.vertices) (hwJ : w ∈ interior J.space) (hwZ : w ∉ Z)
    (hwt : w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2 := by
  classical
  let V := affineSpan ℝ (t : Set V3)
  have hVdim : finrank ℝ V.direction = 2 := T.finrank_faceDirection_of_card ht ht3
  have hwV : w ∈ V := convexHull_subset_affineSpan _ (intrinsicInterior_subset hwt)
  have hVtop : V ≠ ⊤ := by
    intro h
    rw [h, AffineSubspace.direction_top, finrank_top] at hVdim
    norm_num at hVdim
  obtain ⟨A, _, hAV⟩ := V.exists_defining_height_of_finrank_two (by simp) hVdim ⟨w, hwV⟩
  have hwzero : A w = 0 := (hAV w).mpr hwV
  have hwP : w ∈ P.space := (hGs.subset (G.vertices_subset_space hwG)).1
  obtain ⟨a, ha, hwa⟩ := P.exists_face_intrinsicInterior_of_finite hP hwP
  have hspan : affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ := by
    rcases hpos a ha with hfront | hspan | hdisj
    · exact False.elim (hwZ (hfront (intrinsicInterior_subset hwa)))
    · exact hspan
    · exact False.elim (disjoint_left.mp hdisj hwa (intrinsicInterior_subset hwt))
  have hne : ∃ v ∈ a, A v ≠ 0 := V.exists_nonzero_height_vertex_of_span_union_eq_top
    hVtop A hAV (subset_affineSpan ℝ _) hspan
  have hsection := P.exists_two_segment_section_of_transverse_face hP hbound ha hwa
    A hwzero hne (hdisks w hwP hwJ)
  obtain ⟨u, v, hu, hv, hinter, hsection⟩ := hsection
  have htarget : ∀ᶠ x in 𝓝 w, x ∈ convexHull ℝ (t : Set V3) ↔ A x = 0 := by
    filter_upwards [Set.eventually_mem_iff_mem_affineSpan_of_intrinsicInterior hwt] with x hx
    rw [affineSpan_convexHull] at hx
    exact hx.trans (hAV x).symm
  apply G.ncard_neighborSet_eq_two_of_local_segments hG hGc hwG hu hv hinter.subset
  filter_upwards [hsection, htarget] with x hx hxt
  rw [hGs, mem_inter_iff, hxt]
  exact hx



theorem ncard_face_graph_neighbors_of_local_disks
    (P J T G : SimplicialComplex ℝ V3) (hP : P.faces.Finite)
    (hbound : ∀ a ∈ P.faces, a.card ≤ 3)
    (hdisks : ∀ w ∈ P.space, w ∈ interior J.space →
      ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
        w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)))
    {t : Finset V3} (ht : t ∈ T.faces) (ht3 : t.card = 3)
    (hG : G.faces.Finite) (hGs : G.space = P.space ∩ convexHull ℝ (t : Set V3))
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hpos : ∀ a ∈ P.faces, convexHull ℝ (a : Set V3) ⊆ frontier J.space ∨
      affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
        (convexHull ℝ (t : Set V3)))
    {w : V3} (hwG : w ∈ G.vertices) (hwJ : w ∈ interior J.space)
    (hwt : w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2 := by
  exact P.ncard_face_graph_neighbors_of_local_disks_outside_protection J T G hP
    hbound hdisks ht ht3 hG hGs hGc hpos hwG hwJ (fun h => h.2 hwJ) hwt

end Geometry.SimplicialComplex
