import PoincareConjecture.Proofs.M76.Rigidity.OriginalIncidentEdgeLink









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in


theorem vertex_outer_base_eq_iUnion_edges (p : (T.marked 2).vertices) :
    T.diskDualBase {(p : T.index → ℝ × V3)} ∩ ((T.vertexBlock p).link p).space =
      ⋃ s ∈ (T.marked 2).faces, ⋃ (_ : s.card = 2),
        ⋃ (_ : (p : T.index → ℝ × V3) ∈ s), T.diskDualBase s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let N := T.vertexBlock p
  let L := (T.marked 2).barycentricDualBlock {(p : T.index → ℝ × V3)}
  have hLN : L ≤ N := T.ambient.barycentricDualBlock_mono_of_subcomplex
    (T.marked 2) (T.marked_le 2) {(p : T.index → ℝ × V3)}
  have hstar : L.closedStar p = L := by
    simpa only [L, Finset.centroid_singleton, id_eq] using
      (T.marked 2).barycentricDualBlock_closedStar_faceCentroid p.property
  have hlink : (L.link p).space = L.space ∩ (N.link p).space :=
    N.link_space_eq_inter_of_closedStar_eq L hLN p hstar
  have hbase : T.diskDualBase {(p : T.index → ℝ × V3)} = L.space :=
    T.dualRegion_inter_disk {(p : T.index → ℝ × V3)}
  ext x
  constructor
  · intro hx
    have hxL : x ∈ (L.link p).space := hlink.symm.subset ⟨hbase.subset hx.1, hx.2⟩
    obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hxL
    obtain ⟨a, ha, hfaces, hchain, hfa⟩ :=
      ((T.marked 2).barycentricSubdivision_faces_of_face_chains f).mp hf.1.1
    have hdata (u : Finset (T.index → ℝ × V3)) (hu : u ∈ a) :
        (p : T.index → ℝ × V3) ∈ u ∧ u ≠ {(p : T.index → ℝ × V3)} := by
      have hcu : u.centroid ℝ id ∈ f := by
        rw [hfa]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      obtain ⟨v, hv, hpv, hvu⟩ := hf.1.2 _ hcu
      have he : (⟨v, hv⟩ : (T.marked 2).faces) = ⟨u, hfaces u hu⟩ :=
        (T.marked 2).faceCentroid_injective hvu
      have hvu' : v = u := congrArg Subtype.val he
      refine ⟨hvu' ▸ hpv (Finset.mem_singleton_self _), ?_⟩
      intro hueq
      apply hf.2.1
      simpa only [hueq, Finset.centroid_singleton, id_eq] using hcu
    obtain ⟨v, hv, hminimal⟩ := a.exists_min_image Finset.card ha
    have hleast (u : Finset (T.index → ℝ × V3)) (hu : u ∈ a) : v ⊆ u := by
      rcases hchain v hv u hu with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h (hminimal u hu)).symm.subset
    have hnot : ¬ v ⊆ {(p : T.index → ℝ × V3)} := fun h => (hdata v hv).2
      (Finset.Subset.antisymm h (Finset.singleton_subset_iff.mpr (hdata v hv).1))
    obtain ⟨q, hqv, hqnot⟩ := Finset.not_subset.mp hnot
    have hqp : q ≠ (p : T.index → ℝ × V3) := by
      simpa only [Finset.mem_singleton] using hqnot
    let s : Finset (T.index → ℝ × V3) := {(p : T.index → ℝ × V3), q}
    have hps : (p : T.index → ℝ × V3) ∈ s := Finset.mem_insert_self _ _
    have hsv : s ⊆ v := Finset.insert_subset_iff.mpr
      ⟨(hdata v hv).1, Finset.singleton_subset_iff.mpr hqv⟩
    have hs : s ∈ (T.marked 2).faces :=
      (T.marked 2).down_closed (hfaces v hv) hsv ⟨p, hps⟩
    have hcard : s.card = 2 := by simp only [s, Finset.card_pair (Ne.symm hqp)]
    have hfedge : f ∈ ((T.marked 2).barycentricDualBlock s).faces := by
      refine ⟨hf.1.1, ?_⟩
      intro y hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp (hfa ▸ hy)
      exact ⟨u, hfaces u hu, hsv.trans (hleast u hu), huy⟩
    have hxbase : x ∈ T.diskDualBase s :=
      (T.dualRegion_inter_disk s).symm.subset
        (((T.marked 2).barycentricDualBlock s).convexHull_subset_space hfedge hxf)
    exact mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr ⟨hcard, hps, hxbase⟩⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨hcard, hps, hx⟩ := mem_iUnion₂.mp hx
    have hxN : x ∈ N.space := SimplicialComplex.space_subset_of_le
      (T.ambient.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hps)) hx.1.1
    exact ⟨(T.vertex_base_eq_inter p).symm.subset ⟨hxN, hx.2⟩,
      T.edge_dual_subset_vertex_link p hs hcard hps hx.1.1⟩

open Classical in


theorem vertex_base_rim_eq_edges_union_frontier (p : (T.marked 2).vertices) :
    T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space =
      (⋃ s ∈ (T.marked 2).faces, ⋃ (_ : s.card = 2),
        ⋃ (_ : (p : T.index → ℝ × V3) ∈ s), T.diskDualBase s) ∪
          (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) := by
  rw [T.vertex_base_rim_eq, T.vertex_outer_base_eq_iUnion_edges]

end PoincareConjecture.M76.OriginalProperDiskTriangulation
