import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FaceInteriorDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.TransverseFaceGraph

set_option autoImplicit false
open Set Geometry Filter Module
open scoped Topology

namespace Geometry.SimplicialComplex
local notation "V3" => (Fin 3 → ℝ)

private theorem two_segment_germ_of_transverse_triangle
    (P T : SimplicialComplex ℝ V3) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hPc : ∀ a ∈ P.faces, a.card ≤ 3) (hTc : ∀ t ∈ T.faces, t.card ≤ 3)
    {a t : Finset V3} (ha : a ∈ P.faces) (ht : t ∈ T.faces) (ht3 : t.card = 3)
    {w : V3} (hwa : w ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
    (hwt : w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)))
    (hspan : affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤)
    (hdisk : ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q))) :
    ∃ u v : V3, u ≠ w ∧ v ≠ w ∧ segment ℝ w u ∩ segment ℝ w v = {w} ∧
      ∀ᶠ x in 𝓝 w, x ∈ P.space ∩ T.space ↔
        x ∈ segment ℝ w u ∪ segment ℝ w v := by
  let V := affineSpan ℝ (t : Set V3)
  have hVdim : finrank ℝ V.direction = 2 := T.finrank_faceDirection_of_card ht ht3
  have hwV : w ∈ V := convexHull_subset_affineSpan _ (intrinsicInterior_subset hwt)
  have hVtop : V ≠ ⊤ := by
    intro hh
    rw [hh,AffineSubspace.direction_top,finrank_top] at hVdim
    norm_num at hVdim
  obtain ⟨L,_,hLV⟩ := V.exists_defining_height_of_finrank_two (by simp) hVdim ⟨w,hwV⟩
  have hnonzero : ∃ v ∈ a, L v ≠ 0 := V.exists_nonzero_height_vertex_of_span_union_eq_top
    hVtop L hLV (subset_affineSpan ℝ _) hspan
  obtain ⟨u,v,hu,hv,hint,hgerm⟩ := P.exists_two_segment_section_of_transverse_face
    hP hPc ha hwa L ((hLV w).mpr hwV) hnonzero hdisk
  obtain ⟨U,hU,hwU,hTU⟩ := T.exists_open_eq_affineSpan_of_triangle_interior hT hTc ht ht3 hwt
  refine ⟨u,v,hu,hv,hint,?_⟩
  filter_upwards [hgerm,hU.mem_nhds hwU] with x hx hxU
  have hTx : x ∈ T.space ↔ L x = 0 := by
    have hh : x ∈ T.space ↔ x ∈ V :=
      ⟨fun h => (hTU.subset ⟨h,hxU⟩).1,fun h => (hTU.symm.subset ⟨h,hxU⟩).1⟩
    exact hh.trans (hLV x).symm
  simpa only [mem_inter_iff,hTx,mem_setOf_eq] using hx

theorem ncard_surface_intersection_neighbors_of_local_disks
    (P T G : SimplicialComplex ℝ V3)
    (hP : P.faces.Finite) (hT : T.faces.Finite) (hG : G.faces.Finite)
    (hPc : ∀ a ∈ P.faces, a.card ≤ 3) (hTc : ∀ t ∈ T.faces, t.card ≤ 3)
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2) (hGs : G.space = P.space ∩ T.space)
    {Z : Set V3} (hZ : Disjoint Z T.space)
    (hposition : ∀ a ∈ P.faces, convexHull ℝ (a : Set V3) ⊆ Z ∨
      ∀ t ∈ T.faces, affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
          (convexHull ℝ (t : Set V3)))
    (hdisksP : ∀ w ∈ P.space ∩ T.space,
      ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
        w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)))
    (hdisksT : ∀ w ∈ P.space ∩ T.space,
      ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ T.space ∧
        w ∈ d \ q ∧ IsOpen ((Subtype.val : T.space → V3) ⁻¹' (d \ q)))
    (w : G.vertices) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 2 := by
  have hw : (w : V3) ∈ P.space ∩ T.space := hGs.subset (G.vertices_subset_space w.property)
  obtain ⟨a,ha,hwa⟩ := P.exists_face_intrinsicInterior_of_finite hP hw.1
  obtain ⟨t,ht,hwt⟩ := T.exists_face_intrinsicInterior_of_finite hT hw.2
  have hspan : affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ := by
    rcases hposition a ha with hp | hp
    · exact False.elim (disjoint_left.mp hZ (hp (intrinsicInterior_subset hwa)) hw.2)
    rcases hp t ht with hp | hd
    · exact hp
    · exact False.elim (disjoint_left.mp hd hwa (intrinsicInterior_subset hwt))
  have hthree : a.card = 3 ∨ t.card = 3 := by
    by_contra hn
    have hac : a.card ≤ 2 := by have := hPc a ha; omega
    have htc : t.card ≤ 2 := by have := hTc t ht; omega
    have hjoin : affineSpan ℝ (a : Set V3) ⊔ affineSpan ℝ (t : Set V3) = ⊤ := by
      rw [←AffineSubspace.span_union]
      exact hspan
    have hrank := (affineSpan ℝ (a : Set V3)).finrank_inf_add_ambient_of_mem_of_sup_top
      (affineSpan ℝ (t : Set V3))
      (convexHull_subset_affineSpan _ (intrinsicInterior_subset hwa))
      (convexHull_subset_affineSpan _ (intrinsicInterior_subset hwt)) hjoin
    have ha1 := finrank_affineSpan_finset_le (P.nonempty_of_mem_faces ha) (d:=1) hac
    have ht1 := finrank_affineSpan_finset_le (T.nonempty_of_mem_faces ht) (d:=1) htc
    have hdim : finrank ℝ V3 = 3 := by simp
    omega
  have hgerm : ∃ u v : V3, u ≠ w ∧ v ≠ w ∧
      segment ℝ (w : V3) u ∩ segment ℝ (w : V3) v = {(w : V3)} ∧
      ∀ᶠ x in 𝓝 (w : V3), x ∈ P.space ∩ T.space ↔
        x ∈ segment ℝ (w : V3) u ∪ segment ℝ (w : V3) v := by
    rcases hthree with ha3 | ht3
    · simpa only [inter_comm] using two_segment_germ_of_transverse_triangle T P hT hP
        hTc hPc ht ha ha3 hwt hwa (by simpa only [union_comm] using hspan) (hdisksT w hw)
    · exact two_segment_germ_of_transverse_triangle P T hP hT hPc hTc ha ht ht3
        hwa hwt hspan (hdisksP w hw)
  obtain ⟨u,v,hu,hv,hint,hgerm⟩ := hgerm
  exact G.ncard_neighborSet_eq_two_of_local_segments hG hGc w.property hu hv hint.subset
    (by simpa only [hGs] using hgerm)

end Geometry.SimplicialComplex
