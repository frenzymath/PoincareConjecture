import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.TwoSegmentGermDegree

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem exists_two_segment_germ_of_link_section_ncard
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    (hcount : ((K.link 0).space ∩ {x | L x = 0}).ncard = 2) :
    ∃ u v : E, u ≠ 0 ∧ v ≠ 0 ∧
      segment ℝ 0 u ∩ segment ℝ 0 v ⊆ {0} ∧
      ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ∩ {y | L y = 0} ↔
        x ∈ segment ℝ 0 u ∪ segment ℝ 0 v := by
  obtain ⟨u, v, huv, hset⟩ := ncard_eq_two.mp hcount
  have hu : u ∈ (K.link 0).space ∩ {x | L x = 0} := hset.symm ▸ Or.inl rfl
  have hv : v ∈ (K.link 0).space ∩ {x | L x = 0} := hset.symm ▸ Or.inr rfl
  have hu0 : u ≠ 0 := fun h => K.zero_notMem_link_space (h ▸ hu.1)
  have hv0 : v ≠ 0 := fun h => K.zero_notMem_link_space (h ▸ hv.1)
  have hsegments (w : E) (hw : w ∈ (K.link 0).space) (hwL : L w = 0) :
      segment ℝ 0 w ⊆ K.space ∩ {x | L x = 0} := by
    obtain ⟨s, hs, hws⟩ := mem_space_iff.mp hw
    have hz : (0 : E) ∈ convexHull ℝ ((insert 0 s : Finset E) : Set E) :=
      subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
    have hw' : w ∈ convexHull ℝ ((insert 0 s : Finset E) : Set E) :=
      convexHull_mono (Finset.subset_insert _ _) hws
    have hsub := (convex_convexHull ℝ ((insert 0 s : Finset E) : Set E)).segment_subset hz hw'
    have hlevel : Convex ℝ {x | L x = 0} := (convex_singleton (0 : ℝ)).linear_preimage L
    intro x hx
    exact ⟨K.convexHull_subset_space hs.2.2 (hsub hx),
      hlevel.segment_subset (map_zero L) hwL hx⟩
  refine ⟨u, v, hu0, hv0, ?_, ?_⟩
  · rintro x ⟨hxu, hxv⟩
    by_cases hx0 : x = 0
    · exact hx0
    · exact (huv (K.injOn_normalize_link hu.1 hv.1
        ((NormedSpace.normalize_eq_of_mem_segment_zero hxu hx0).symm.trans
          (NormedSpace.normalize_eq_of_mem_segment_zero hxv hx0)))).elim
  · obtain ⟨ε, hε, hball⟩ := K.exists_ball_inter_space_subset_closedStar hK hzero
    filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with x hxball
    constructor
    · rintro ⟨hxK, hxL⟩
      by_cases hx0 : x = 0
      · exact Or.inl (hx0.symm ▸ left_mem_segment ℝ 0 u)
      obtain ⟨w, hw, r, hr, hxr⟩ := exists_linkPoint_smul (hball ⟨hxK, hxball⟩) hx0
      have hwL : L w = 0 := by
        change L x = 0 at hxL
        rw [hxr, map_smul, smul_eq_mul] at hxL
        exact (mul_eq_zero.mp hxL).resolve_left hr.1.ne'
      have hxseg : x ∈ segment ℝ 0 w := hxr.symm ▸
        (convex_segment (0 : E) w).smul_mem_of_zero_mem
          (left_mem_segment ℝ 0 w) (right_mem_segment ℝ 0 w) ⟨hr.1.le, hr.2⟩
      have hwm : w ∈ ({u, v} : Set E) := hset ▸ And.intro hw hwL
      rcases hwm with rfl | rfl
      · exact Or.inl hxseg
      · exact Or.inr hxseg
    · intro hx
      exact hx.elim (fun h => hsegments u hu.1 hu.2 h) (fun h => hsegments v hv.1 hv.2 h)

theorem ncard_graph_degree_of_link_section_ncard
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hG : G.faces.Finite)
    (hzeroK : (0 : E) ∈ K.vertices) (hzeroG : (0 : E) ∈ G.vertices)
    (hbound : ∀ a ∈ G.faces, a.card ≤ 2) (L : E →ₗ[ℝ] ℝ)
    (hcount : ((K.link 0).space ∩ {x | L x = 0}).ncard = 2)
    (hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ G.space ↔ x ∈ K.space ∩ {y | L y = 0}) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨0, hzeroG⟩).ncard = 2 := by
  obtain ⟨u, v, hu, hv, hinter, hsection⟩ :=
    K.exists_two_segment_germ_of_link_section_ncard hK hzeroK L hcount
  apply G.ncard_neighborSet_eq_two_of_local_segments_zero hG hbound hzeroG hu hv hinter
  filter_upwards [hlocal, hsection] with x hx hs
  exact hx.trans hs

end Geometry.SimplicialComplex
