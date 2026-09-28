import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeOverlap

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K L : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype L.faces]

omit [Fintype L.faces] in
open Classical in

theorem boundary_edge_dual_subset_vertex_link (hLK : L ≤ K)
    {p : E} (hp : p ∈ L.vertices) {s : Finset E} (hsc : s.card = 2) (hps : p ∈ s) :
    (K.barycentricDualBlock s).space ⊆
      ((K.barycentricDualBlock {p}).link p).space := by
  classical
  have hstrict : ({p} : Finset E) ⊂ s := by
    apply (Finset.singleton_subset_iff.mpr hps).ssubset_of_ne
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton, hsc] at hc
    omega
  simpa only [Finset.centroid_singleton, id_eq] using
    space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset (hLK hp) hstrict)

open Classical in

theorem boundary_vertex_rim_eq_iUnion_edges (hLK : L ≤ K)
    {p : E} (hp : p ∈ L.vertices) :
    (L.barycentricDualBlock {p}).space ∩
        ((K.barycentricDualBlock {p}).link p).space =
      ⋃ s ∈ L.faces, ⋃ (_ : s.card = 2), ⋃ (_ : p ∈ s),
        (L.barycentricDualBlock s).space := by
  classical
  let N := K.barycentricDualBlock {p}
  let M := L.barycentricDualBlock {p}
  have hMN : M ≤ N := K.barycentricDualBlock_mono_of_subcomplex L hLK {p}
  have hstar : M.closedStar p = M := by
    simpa only [M, Finset.centroid_singleton, id_eq] using
      L.barycentricDualBlock_closedStar_faceCentroid hp
  have hlink : (M.link p).space = M.space ∩ (N.link p).space :=
    N.link_space_eq_inter_of_closedStar_eq M hMN p hstar
  ext x
  constructor
  · intro hx
    have hxM : x ∈ (M.link p).space := hlink.symm.subset hx
    obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hxM
    obtain ⟨a, ha, hfaces, hchain, hfa⟩ :=
      (L.barycentricSubdivision_faces_of_face_chains f).mp hf.1.1
    have hdata (u : Finset E) (hu : u ∈ a) : p ∈ u ∧ u ≠ {p} := by
      have hcu : u.centroid ℝ id ∈ f := by
        rw [hfa]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      obtain ⟨v, hv, hpv, hvu⟩ := hf.1.2 _ hcu
      have he : (⟨v, hv⟩ : L.faces) = ⟨u, hfaces u hu⟩ :=
        L.faceCentroid_injective hvu
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
    have hnot : ¬ v ⊆ {p} := fun h => (hdata v hv).2
      (Finset.Subset.antisymm h (Finset.singleton_subset_iff.mpr (hdata v hv).1))
    obtain ⟨q, hqv, hqnot⟩ := Finset.not_subset.mp hnot
    have hqp : q ≠ p := by simpa only [Finset.mem_singleton] using hqnot
    let s : Finset E := {p, q}
    have hps : p ∈ s := Finset.mem_insert_self _ _
    have hsv : s ⊆ v := Finset.insert_subset_iff.mpr
      ⟨(hdata v hv).1, Finset.singleton_subset_iff.mpr hqv⟩
    have hs : s ∈ L.faces := L.down_closed (hfaces v hv) hsv ⟨p, hps⟩
    have hcard : s.card = 2 := by simp only [s, Finset.card_pair (Ne.symm hqp)]
    have hfedge : f ∈ (L.barycentricDualBlock s).faces := by
      refine ⟨hf.1.1, ?_⟩
      intro y hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp (hfa ▸ hy)
      exact ⟨u, hfaces u hu, hsv.trans (hleast u hu), huy⟩
    exact mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr
      ⟨hcard, hps, (L.barycentricDualBlock s).convexHull_subset_space hfedge hxf⟩⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨hcard, hps, hx⟩ := mem_iUnion₂.mp hx
    refine ⟨space_subset_of_le
      (L.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hps)) hx, ?_⟩
    exact K.boundary_edge_dual_subset_vertex_link L hLK hp hcard hps
      (space_subset_of_le (K.barycentricDualBlock_mono_of_subcomplex L hLK s) hx)

end Geometry.SimplicialComplex
