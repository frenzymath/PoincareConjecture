import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.IncidentEdgeLink

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "I" => Icc (-1 : ℝ) 1

open Classical in


theorem vertex_outer_base_eq_iUnion_edges (p : (T.marked 2).vertices) :
    T.surfaceBase {(p : E)} ∩ ((T.vertexBlock p).link p).space =
      ⋃ s ∈ (T.marked 2).faces, ⋃ (_ : s.card = 2),
        ⋃ (_ : (p : E) ∈ s), T.surfaceBase s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let N := T.vertexBlock p
  let L := (T.marked 2).barycentricDualBlock {(p : E)}
  have hLN : L ≤ N := T.ambient.barycentricDualBlock_mono_of_subcomplex
    (T.marked 2) (T.marked_le 2) {(p : E)}
  have hstar : L.closedStar p = L := by
    simpa only [L, Finset.centroid_singleton, id_eq] using
      (T.marked 2).barycentricDualBlock_closedStar_faceCentroid p.property
  have hlink : (L.link p).space = L.space ∩ (N.link p).space :=
    N.link_space_eq_inter_of_closedStar_eq L hLN p hstar
  have hbase : T.surfaceBase {(p : E)} = L.space :=
    T.dualRegion_inter_surface {(p : E)}
  ext x
  constructor
  · intro hx
    have hxL : x ∈ (L.link p).space := hlink.symm.subset ⟨hbase.subset hx.1, hx.2⟩
    obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hxL
    obtain ⟨a, ha, hfaces, hchain, hfa⟩ :=
      ((T.marked 2).barycentricSubdivision_faces_of_face_chains f).mp hf.1.1
    have hdata (u : Finset E) (hu : u ∈ a) :
        (p : E) ∈ u ∧ u ≠ {(p : E)} := by
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
    have hleast (u : Finset E) (hu : u ∈ a) : v ⊆ u := by
      rcases hchain v hv u hu with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h (hminimal u hu)).symm.subset
    have hnot : ¬ v ⊆ {(p : E)} := fun h => (hdata v hv).2
      (Finset.Subset.antisymm h (Finset.singleton_subset_iff.mpr (hdata v hv).1))
    obtain ⟨q, hqv, hqnot⟩ := Finset.not_subset.mp hnot
    have hqp : q ≠ (p : E) := by
      simpa only [Finset.mem_singleton] using hqnot
    let s : Finset E := {(p : E), q}
    have hps : (p : E) ∈ s := Finset.mem_insert_self _ _
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
    have hxbase : x ∈ T.surfaceBase s :=
      (T.dualRegion_inter_surface s).symm.subset
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
    T.dualRegionRim {(p : E)} ∩ (T.marked 2).space =
      (⋃ s ∈ (T.marked 2).faces, ⋃ (_ : s.card = 2),
        ⋃ (_ : (p : E) ∈ s), T.surfaceBase s) ∪
          (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) := by
  rw [T.vertex_base_rim_eq, T.vertex_outer_base_eq_iUnion_edges]


end Geometry.SimplicialComplex.CoorientedSurfaceStars

