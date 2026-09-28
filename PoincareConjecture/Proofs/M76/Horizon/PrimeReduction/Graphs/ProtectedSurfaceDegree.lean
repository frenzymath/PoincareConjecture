import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FaceInteriorDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ProtectedVertexDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ProtectedEdgeDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.SignedTriangleInterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.MovedLocalDisk
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)

theorem ncard_graph_degree_after_face_affine_motion_on_protected_subcomplex
    (K K₀ G : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (hK₀K : K₀ ≤ K)
    (hG : G.faces.Finite) (hGbound : ∀ s ∈ G.faces, s.card ≤ 2)
    {p u v : V3} (hp₀ : p ∈ K₀.space) (hpG : p ∈ G.vertices)
    {d rim : Set V3} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdK : d ⊆ K.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space))
    (A : V3 →ᵃ[ℝ] ℝ) (hu : u ≠ p) (hv : v ≠ p)
    (hinter : segment ℝ p u ∩ segment ℝ p v ⊆ {p})
    (hlocal : ∀ᶠ x in 𝓝 p,
      x ∈ K.space ∩ {y | A y = 0} ↔ x ∈ segment ℝ p u ∪ segment ℝ p v)
    (hneg : p ∈ closure (K.space ∩ {x | A x < 0}))
    (hpos : p ∈ closure (K.space ∩ {x | 0 < A x}))
    (f : V3 ≃ₜ V3) (hf : K.AffineOnFaces f) (hfix : EqOn f id K₀.space)
    (hposv : ∀ w ∈ K.vertices, 0 < A w → 0 < A (f w))
    (hnegv : ∀ w ∈ K.vertices, A w < 0 → A (f w) < 0)
    (hGlocal : ∀ᶠ x in 𝓝 p,
      x ∈ G.space ↔ x ∈ f '' K.space ∩ {y | A y = 0}) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hpG⟩).ncard = 2 := by
  classical
  have hpK : p ∈ K.space := hdK hpd.1
  have hpA : A p = 0 :=
    ((mem_of_mem_nhds hlocal).mpr (Or.inl (left_mem_segment ℝ p u))).2
  have hfp : f p = p := hfix hp₀
  obtain ⟨a, ha, hpa⟩ := K.exists_face_intrinsicInterior_of_finite hK hpK
  have ha₀ : a ∈ K₀.faces :=
    K.face_mem_subcomplex_of_intrinsicInterior K₀ hK₀K ha hpa hp₀
  have hfixa : EqOn f id (convexHull ℝ (a : Set V3)) :=
    hfix.mono (K₀.convexHull_subset_space ha₀)
  by_cases ha1 : a.card = 1
  · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ha1
    have hpw : p = w := by
      simpa only [hw, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff]
        using intrinsicInterior_subset hpa
    have hpvert : p ∈ K.vertices := by
      rw [hpw]
      exact K.face_subset_vertices ha (by simp [hw])
    exact K.ncard_graph_degree_after_face_affine_motion_at_fixed_vertex G hK hbound
      hG hGbound hpvert hpG hd hdK hpd hopen A hu hv hinter hlocal hneg hpos
      hf f.injective.injOn hfp hposv hnegv hGlocal
  by_cases hne : ∃ w ∈ a, A w ≠ 0
  · let M := hf.embeddedImage f.injective.injOn
    have hM : M.faces.Finite := hf.embeddedImage_finite f.injective.injOn hK
    have hMs : M.space = f '' K.space := hf.embeddedImage_space f.injective.injOn
    have hMbound (s : Finset V3) (hs : s ∈ M.faces) : s.card ≤ 3 := by
      rw [hf.embeddedImage_faces] at hs
      obtain ⟨b, hb, rfl⟩ := hs
      exact Finset.card_image_le.trans (hbound b hb)
    have hfa : a.image f = a := by
      calc
        a.image f = a.image id := Finset.image_congr (fun w hw =>
          hfixa (subset_convexHull ℝ (a : Set V3) hw))
        _ = a := Finset.image_id
    have haM : a ∈ M.faces := by
      rw [hf.embeddedImage_faces]
      exact ⟨a, ha, hfa⟩
    obtain ⟨d', rim', hd', hd'M, hpd', hopen'⟩ :=
      K.exists_moved_disk_neighborhood M hK f hf hMs hd hdK hpd hopen
    have hpd'M : p ∈ d' \ rim' := by simpa only [hfp] using hpd'
    obtain ⟨u', v', hu', hv', hinter', hsection⟩ :=
      M.exists_two_segment_section_of_transverse_face hM hMbound haM hpa A hpA hne
        ⟨d', rim', hd', hd'M, hpd'M, hopen'⟩
    apply G.ncard_neighborSet_eq_two_of_local_segments hG hGbound hpG hu' hv' hinter'.subset
    filter_upwards [hGlocal, hsection] with x hx hs
    exact hx.trans (by simpa only [hMs] using hs)
  · have hzero : ∀ w ∈ a, A w = 0 := by simpa only [not_exists, not_and, not_not] using hne
    have ha3 : a.card ≠ 3 := fun h => hne
      (K.exists_nonzero_height_vertex_of_triangle_interior_sign hK hbound ha h hpa A hpos)
    have ha2 : a.card = 2 := by
      have := hbound a ha
      have := Finset.card_pos.mpr (K.nonempty_of_mem_faces ha)
      omega
    exact K.ncard_graph_degree_after_face_affine_motion_at_fixed_edge G hK hbound
      hG hGbound ha ha2 hpG hpa hd hdK hpd hopen A hzero hneg hpos f hf hfixa
      hposv hnegv hGlocal

end Geometry.SimplicialComplex
