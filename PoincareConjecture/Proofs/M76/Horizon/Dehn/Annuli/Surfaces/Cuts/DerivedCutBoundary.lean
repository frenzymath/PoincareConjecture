import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DerivedComplementLinks










set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]



theorem closedFaceComplement_space_eq_unmarked_duals
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).space =
      ⋃ v ∈ K.vertices \ L.vertices, (K.barycentricDualBlock {v}).space := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨v, hv, hvL, hvs⟩ := (K.closedFaceComplement_derived_face_iff L hpure).mp hs
    rw [← K.barycentricDualBlock_singleton_eq_closedStar hv] at hvs
    exact mem_iUnion₂.mpr ⟨v, ⟨hv, hvL⟩, (K.barycentricDualBlock {v}).convexHull_subset_space
      hvs hxs⟩
  · intro hx
    obtain ⟨v, ⟨hv, hvL⟩, hxv⟩ := mem_iUnion₂.mp hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxv
    rw [K.barycentricDualBlock_singleton_eq_closedStar hv] at hs
    exact mem_space_iff.mpr ⟨s,
      K.unmarked_vertex_star_le_closedFaceComplement L hpure hv hvL hs, hxs⟩


theorem vertex_dual_inter_closedFaceComplement
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) (v : E) :
    (K.barycentricDualBlock {v}).space ∩
      (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).space =
      ⋃ u ∈ K.vertices \ L.vertices, (K.barycentricDualBlock {v, u}).space := by
  rw [K.closedFaceComplement_space_eq_unmarked_duals L hpure]
  ext x
  constructor
  · rintro ⟨hxv, hx⟩
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    apply mem_iUnion₂.mpr
    refine ⟨u, hu, ?_⟩
    have h := (K.barycentricDualBlock_space_inter {v} {u}).subset ⟨hxv, hxu⟩
    simpa only [Finset.singleton_union] using h
  · intro hx
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have h := (K.barycentricDualBlock_space_inter {v} {u}).symm.subset
      (show x ∈ (K.barycentricDualBlock ({v} ∪ {u})).space by
        simpa only [Finset.singleton_union] using hxu)
    exact ⟨h.1, mem_iUnion₂.mpr ⟨u, hu, h.2⟩⟩

omit [DecidableEq E] in


theorem derived_cut_boundary_space
    (L : SimplicialComplex ℝ E) :
    ((K.barycentricNeighborhood L) ⊓ K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).space =
      (K.barycentricNeighborhood L).space ∩
        (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact ⟨mem_space_iff.mpr ⟨s, hs.1, hxs⟩, mem_space_iff.mpr ⟨s, hs.2, hxs⟩⟩
  · intro x hx
    obtain ⟨s, hsN, hsC, hxs⟩ := K.barycentricSubdivision.exists_common_face_of_mem_subcomplexes
      (K.barycentricNeighborhood L)
      (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L))
      (K.barycentricNeighborhood_le L)
      (K.barycentricSubdivision.closedFaceComplement_le (K.barycentricNeighborhood L)) hx
    exact mem_space_iff.mpr ⟨s, ⟨hsN, hsC⟩, hxs⟩



theorem derived_cut_boundary_eq_mixed_duals
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    ((K.barycentricNeighborhood L) ⊓ K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).space =
      ⋃ v ∈ L.vertices, ⋃ u ∈ K.vertices \ L.vertices,
        (K.barycentricDualBlock {v, u}).space := by
  rw [K.derived_cut_boundary_space, K.barycentricNeighborhood_space_eq_iUnion_dualBlocks]
  ext x
  constructor
  · rintro ⟨hxN, hxC⟩
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxN
    exact mem_iUnion₂.mpr ⟨v, hv,
      (K.vertex_dual_inter_closedFaceComplement L hpure v).subset ⟨hxv, hxC⟩⟩
  · intro hx
    obtain ⟨v, hv, hx⟩ := mem_iUnion₂.mp hx
    have h := (K.vertex_dual_inter_closedFaceComplement L hpure v).symm.subset hx
    exact ⟨mem_iUnion₂.mpr ⟨v, hv, h.1⟩, h.2⟩

omit [DecidableEq E] in
private theorem centroid_mem_dual_of_subset {s t : Finset E}
    (ht : t ∈ K.faces) (hst : s ⊆ t) :
    t.centroid ℝ id ∈ (K.barycentricDualBlock s).space := by
  have hv : t.centroid ℝ id ∈ K.barycentricSubdivision.vertices :=
    (K.mem_barycentricSubdivision_vertices_iff _).mpr ⟨t, ht, rfl⟩
  apply (K.barycentricDualBlock s).subset_space (s := {t.centroid ℝ id}) ?_
    (Finset.mem_singleton_self _)
  exact ⟨hv, fun x hx ↦ ⟨t, ht, hst, (Finset.mem_singleton.mp hx).symm⟩⟩

omit [DecidableEq E] in
private theorem mem_triangle_dual_eq_centroid
    (hdim : ∀ t ∈ K.faces, t.card ≤ 3) {t : Finset E} (htc : t.card = 3)
    {x : E} (hx : x ∈ (K.barycentricDualBlock t).space) : x = t.centroid ℝ id := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  have hverts : (s : Set E) ⊆ {t.centroid ℝ id} := by
    intro y hy
    obtain ⟨u, hu, htu, huy⟩ := hs.2 y hy
    have htu' : t = u := Finset.eq_of_subset_of_card_le htu (by simpa [htc] using hdim u hu)
    exact huy.symm.trans (congrArg (fun s : Finset E ↦ s.centroid ℝ id) htu'.symm)
  simpa only [convexHull_singleton, mem_singleton_iff] using convexHull_mono hverts hxs




theorem marked_edge_dual_inter_closedFaceComplement
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hfull : ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 2)
    {s : Finset E} (hs : s ∈ L.faces) (hsc : s.card = 2) :
    (K.barycentricDualBlock s).space ∩
      (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).space =
      (fun t : Finset E ↦ t.centroid ℝ id) ''
        {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t} := by
  classical
  have hdim (t : Finset E) (ht : t ∈ K.faces) : t.card ≤ 3 := by
    obtain ⟨u, _, huc, htu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  rw [K.closedFaceComplement_space_eq_unmarked_duals L hpure]
  ext x
  constructor
  · rintro ⟨hxs, hx⟩
    obtain ⟨v, ⟨hvK, hvL⟩, hxv⟩ := mem_iUnion₂.mp hx
    have hvs : v ∉ s := fun hvs ↦ hvL
      (L.down_closed hs (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty _))
    have hxsv := (K.barycentricDualBlock_space_inter s {v}).subset ⟨hxs, hxv⟩
    have hsvcard : (s ∪ {v}).card = 3 := by
      simp only [Finset.union_singleton, Finset.card_insert_of_notMem hvs, hsc]
    have hsv : s ∪ {v} ∈ K.faces := by
      by_contra hnot
      have he := K.barycentricDualBlock_space_eq_empty_of_not_face
        (show (s ∪ {v}).Nonempty from ⟨v, by simp⟩) hnot
      exact (he ▸ hxsv : x ∈ (∅ : Set E)).elim
    exact ⟨s ∪ {v}, ⟨hsv, hsvcard, Finset.subset_union_left⟩,
      (K.mem_triangle_dual_eq_centroid hdim hsvcard hxsv).symm⟩
  · rintro ⟨t, ⟨ht, htc, hst⟩, rfl⟩
    obtain ⟨v, hvt, hvL⟩ : ∃ v ∈ t, v ∉ L.vertices := by
      by_contra hn
      push Not at hn
      have hc := hLcard t (hfull t ht hn)
      omega
    have hvK : v ∈ K.vertices := K.down_closed ht
      (Finset.singleton_subset_iff.mpr hvt) (Finset.singleton_nonempty _)
    exact ⟨K.centroid_mem_dual_of_subset ht hst,
      mem_iUnion₂.mpr ⟨v, ⟨hvK, hvL⟩,
        K.centroid_mem_dual_of_subset ht (Finset.singleton_subset_iff.mpr hvt)⟩⟩

end Geometry.SimplicialComplex
