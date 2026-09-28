import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.AffineLinkSectionDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FaceAffinePolygonSignPreservation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskSignedLink











set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem ncard_graph_degree_after_face_affine_motion_at_fixed_vertex
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hG : G.faces.Finite) (hGbound : ∀ s ∈ G.faces, s.card ≤ 2)
    {p u v : E} (hp : p ∈ K.vertices) (hpG : p ∈ G.vertices)
    {d rim : Set E} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdK : d ⊆ K.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space))
    (A : E →ᵃ[ℝ] ℝ) (hu : u ≠ p) (hv : v ≠ p)
    (hinter : segment ℝ p u ∩ segment ℝ p v ⊆ {p})
    (hlocal : ∀ᶠ x in 𝓝 p,
      x ∈ K.space ∩ {y | A y = 0} ↔ x ∈ segment ℝ p u ∪ segment ℝ p v)
    (hneg : p ∈ closure (K.space ∩ {x | A x < 0}))
    (hpos : p ∈ closure (K.space ∩ {x | 0 < A x}))
    {f : E → E} (hf : K.AffineOnFaces f) (hfi : InjOn f K.space) (hfp : f p = p)
    (hposv : ∀ w ∈ K.vertices, 0 < A w → 0 < A (f w))
    (hnegv : ∀ w ∈ K.vertices, A w < 0 → A (f w) < 0)
    (hGlocal : ∀ᶠ x in 𝓝 p,
      x ∈ G.space ↔ x ∈ f '' K.space ∩ {y | A y = 0}) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hpG⟩).ncard = 2 := by
  obtain ⟨n, Q, hQi, hQ, hQs, _, hn, hpos', hz, he, hnv, hpv⟩ :=
    K.exists_signed_link_polygon_of_local_disk_and_section hK hbound hp hd hdK hpd hopen
      A hu hv hinter hlocal hneg hpos
  let L := K.link p
  have hL : L.faces.Finite := finite_link_faces hK p
  have hLK : L.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact K.convexHull_subset_space hs.1 hxs
  have hLbound (s : Finset E) (hs : s ∈ L.faces) : s.card ≤ 2 := by
    have h := hbound (insert p s) hs.2.2
    rw [Finset.card_insert_of_notMem hs.2.1] at h
    omega
  have hfL : L.AffineOnFaces f := fun s hs => hf s hs.1
  have hcount := L.ncard_face_affine_polygon_image_zero_eq_two hL hLbound Q hQ hQi hQs A A
    hfL (hfi.mono hLK) hn.isPreconnected hpos'.isPreconnected
    (fun w hw => hposv w hw.1) (fun w hw => hnegv w hw.1)
    (fun w hw => hz w (L.vertices_subset_space hw)) he hnv hpv
  let M := hf.embeddedImage hfi
  have hM : M.faces.Finite := hf.embeddedImage_finite hfi hK
  have hMs : M.space = f '' K.space := hf.embeddedImage_space hfi
  have hpM : p ∈ M.vertices := by
    rw [hf.embeddedImage_vertices hfi]
    exact ⟨p, hp, hfp⟩
  have hMl : (M.link p).space = f '' L.space := by
    have h := hf.embeddedImage_link_space hfi hp
    change (M.link (f p)).space = f '' L.space at h
    simpa only [hfp] using h
  have hcountM : ((M.link p).space ∩ {x | A x = 0}).ncard = 2 := by
    rw [hMl]
    exact hcount
  have hpA : A p = 0 :=
    ((mem_of_mem_nhds hlocal).mpr (Or.inl (left_mem_segment ℝ p u))).2
  apply M.ncard_graph_degree_of_affine_link_section_ncard G hM hG hpM hpG hGbound A hpA hcountM
  simpa only [hMs] using hGlocal

end Geometry.SimplicialComplex
