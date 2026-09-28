import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalGerm
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.PlaneHeight
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.MaximalFaceAffineGerm








set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]




theorem exists_two_segment_germ_of_degree_two
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hbound : ∀ a ∈ G.faces, a.card ≤ 2) {p : E} (hp : p ∈ G.space)
    (hdegree : ∀ hpv : p ∈ G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hpv⟩).ncard = 2) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧
      segment ℝ p u ∩ segment ℝ p v ⊆ {p} ∧
      ∀ᶠ x in 𝓝 p, x ∈ G.space ↔ x ∈ segment ℝ p u ∪ segment ℝ p v := by
  by_cases hpv : p ∈ G.vertices
  · apply G.exists_two_segment_germ_of_link_vertices_ncard hG hbound hpv
    exact (G.ncard_edgeGraph_neighborSet ⟨p, hpv⟩).symm.trans (hdegree hpv)
  obtain ⟨s, hs, hps⟩ := G.exists_face_intrinsicInterior_of_finite hG hp
  have hs2 : s.card = 2 := by
    have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
    have hle := hbound s hs
    have hnot : s.card ≠ 1 := by
      intro hc
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
      have hpv' : p = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff]
          using intrinsicInterior_subset hps
      exact hpv (hpv' ▸ hs)
    omega
  have hmax : ∀ t ∈ G.faces, s ⊆ t → t = s := by
    intro t ht hst
    exact (Finset.eq_of_subset_of_card_le hst (by simpa only [hs2] using hbound t ht)).symm
  obtain ⟨U, hU, hpU, hlocal⟩ :=
    G.exists_open_eq_affineSpan_of_maximal_face hG hs hmax hps
  have hgerm : ∀ᶠ x in 𝓝 p, x ∈ G.space ↔ x ∈ convexHull ℝ (s : Set E) := by
    filter_upwards [hU.mem_nhds hpU,
      Set.eventually_mem_iff_mem_affineSpan_of_intrinsicInterior hps] with x hxU hx
    have hmem : x ∈ G.space ↔ x ∈ (affineSpan ℝ (s : Set E) : Set E) := by
      constructor
      · intro hxG
        exact (hlocal.subset ⟨hxG, hxU⟩).1
      · intro hxspan
        exact (hlocal.symm.subset ⟨hxspan, hxU⟩).1
    rw [affineSpan_convexHull] at hx
    exact hmem.trans hx.symm
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hs2
  have hu : u ≠ p := by
    intro heq
    apply hpv
    subst u
    exact G.down_closed hs (by simp) (Finset.singleton_nonempty p)
  have hv : v ≠ p := by
    intro heq
    apply hpv
    subst v
    exact G.down_closed hs (by simp) (Finset.singleton_nonempty p)
  have hpseg : p ∈ segment ℝ u v := by
    simpa only [Finset.coe_pair, convexHull_pair] using intrinsicInterior_subset hps
  have hbt : Wbtw ℝ u p v := mem_segment_iff_wbtw.mp hpseg
  have hsplit : segment ℝ p u ∪ segment ℝ p v = segment ℝ u v := by
    rw [segment_symm ℝ p u, hbt.segment_union]
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · rw [segment_symm ℝ p u, hbt.segment_inter_eq_endpoint]
  · simpa only [hsplit, Finset.coe_pair, convexHull_pair] using hgerm

end Geometry.SimplicialComplex
