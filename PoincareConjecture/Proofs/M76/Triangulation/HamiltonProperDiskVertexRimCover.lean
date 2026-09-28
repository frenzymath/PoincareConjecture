import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBoundaryEdges
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskLowerIncidence









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}



theorem HamiltonProperDiskTriangulation.incident_edge_subset_vertex_rim
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2) (hps : (p : E) ∈ s) :
    T.diskDualBase s ⊆ T.dualRegionRim {(p : E)} ∩ D ∧
      T.dualRegion s ⊆ T.dualRegionRim {(p : E)} := by
  have hne : {(p : E)} ≠ s := by
    intro heq
    have h := congrArg Finset.card heq
    rw [Finset.card_singleton, hcard] at h
    omega
  have hsub := T.dualRegion_subset_rim_of_ssubset p.property hs
    ((Finset.singleton_subset_iff.mpr hps).ssubset_of_ne hne)
  exact ⟨fun _ hx => ⟨hsub hx.1, hx.2⟩, hsub⟩



theorem HamiltonProperDiskTriangulation.vertex_outer_base_eq_iUnion_edges
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    T.diskVertexBlock p ∩ ((T.vertexBlock p).link p).space =
      ⋃ s ∈ T.disk.faces, ⋃ (_ : s.card = 2), ⋃ (_ : (p : E) ∈ s), T.diskDualBase s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  let N := T.vertexBlock p
  let L := T.disk.barycentricDualBlock {(p : E)}
  have hLN : L ≤ N := T.ambient.barycentricDualBlock_mono_of_subcomplex
    T.disk T.disk_le {(p : E)}
  have hstar : L.closedStar p = L := by
    simpa only [L, Finset.centroid_singleton, id_eq] using
      T.disk.barycentricDualBlock_closedStar_faceCentroid p.property
  have hlink : (L.link p).space = L.space ∩ (N.link p).space :=
    N.link_space_eq_inter_of_closedStar_eq L hLN p hstar
  ext x
  constructor
  · intro hx
    have hxL : x ∈ (L.link p).space := hlink.symm.subset hx
    obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hxL
    obtain ⟨a, ha, hfaces, hchain, hfa⟩ :=
      (T.disk.barycentricSubdivision_faces_of_face_chains f).mp hf.1.1
    have hdata (u : Finset E) (hu : u ∈ a) : (p : E) ∈ u ∧ u ≠ {(p : E)} := by
      have hcu : u.centroid ℝ id ∈ f := by
        rw [hfa]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      obtain ⟨v, hv, hpv, hvu⟩ := hf.1.2 _ hcu
      have he : (⟨v, hv⟩ : T.disk.faces) = ⟨u, hfaces u hu⟩ :=
        T.disk.faceCentroid_injective hvu
      have hvu' : v = u := congrArg Subtype.val he
      refine ⟨hvu' ▸ hpv (Finset.mem_singleton_self _), ?_⟩
      intro hueq
      apply hf.2.1
      simpa only [hueq, Finset.centroid_singleton, id_eq] using hcu
    obtain ⟨v, hv, hminimal⟩ := a.exists_min_image Finset.card ha
    have hleast (u : Finset E) (hu : u ∈ a) : v ⊆ u := by
      rcases hchain v hv u hu with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h (hminimal u hu)).symm.subset
    have hnot : ¬ v ⊆ {(p : E)} := fun h => (hdata v hv).2
      (Finset.Subset.antisymm h (Finset.singleton_subset_iff.mpr (hdata v hv).1))
    obtain ⟨q, hqv, hqnot⟩ := Finset.not_subset.mp hnot
    have hqp : q ≠ (p : E) := by simpa only [Finset.mem_singleton] using hqnot
    let s : Finset E := {(p : E), q}
    have hps : (p : E) ∈ s := Finset.mem_insert_self _ _
    have hsv : s ⊆ v := Finset.insert_subset_iff.mpr
      ⟨(hdata v hv).1, Finset.singleton_subset_iff.mpr hqv⟩
    have hs : s ∈ T.disk.faces := T.disk.down_closed (hfaces v hv) hsv ⟨p, hps⟩
    have hcard : s.card = 2 := by simp only [s, Finset.card_pair (Ne.symm hqp)]
    have hfedge : f ∈ (T.disk.barycentricDualBlock s).faces := by
      refine ⟨hf.1.1, ?_⟩
      intro y hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp (hfa ▸ hy)
      exact ⟨u, hfaces u hu, hsv.trans (hleast u hu), huy⟩
    have hxbase : x ∈ T.diskDualBase s := by
      rw [T.diskDualBase_eq_dual]
      exact (T.disk.barycentricDualBlock s).convexHull_subset_space hfedge hxf
    exact mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr ⟨hcard, hps, hxbase⟩⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨hcard, hps, hx⟩ := mem_iUnion₂.mp hx
    have hxN : x ∈ N.space := SimplicialComplex.space_subset_of_le
      (T.ambient.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hps)) hx.1.1
    exact ⟨(T.diskVertexBlock_eq_inter p).symm.subset ⟨hxN, hx.2⟩,
      T.edge_dual_subset_vertex_link p hs hcard hps hx.1.1⟩




theorem HamiltonProperDiskTriangulation.vertex_base_rim_eq_edges_union_frontier
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    T.dualRegionRim {(p : E)} ∩ D =
      (⋃ s ∈ T.disk.faces, ⋃ (_ : s.card = 2), ⋃ (_ : (p : E) ∈ s), T.diskDualBase s) ∪
        (T.diskVertexBlock p ∩ frontier R) := by
  rw [T.vertex_base_rim_eq, T.vertex_outer_base_eq_iUnion_edges]



theorem HamiltonProperDiskTriangulation.nonboundary_base_contact_empty
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E}
    (hs : s ∈ T.disk.faces) (hsF : s ∉ T.boundary.faces) :
    T.diskDualBase s ∩ frontier R = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2.2 (T.dualBlock_subset_interior hs hsF hx.1.1.1)

end PoincareConjecture.M76.HamiltonIndexOne
