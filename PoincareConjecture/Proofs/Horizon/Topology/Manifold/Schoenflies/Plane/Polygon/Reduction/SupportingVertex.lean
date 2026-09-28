import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.SupportingFrame
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.LocalSides












set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane




theorem IsSimplePolygon.exists_supporting_vertex_away_edge {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {p : Polygon E n} (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) (i : Fin n) :
    ∃ e : E ≃L[ℝ] (ℝ × ℝ), ∃ k : Fin n,
      k ≠ i ∧ k ≠ finRotate n i ∧
      (∀ j, (e (p k)).1 ≤ (e (p j)).1) ∧
      (∀ j, (e (p j)).1 = (e (p k)).1 → (e (p k)).2 ≤ (e (p j)).2) ∧
      LinearIndependent ℝ ![p ((finRotate n).symm k) - p k, p (finRotate n k) - p k] := by
  classical
  obtain ⟨w, hwi, hwr⟩ := Fin.exists_ne_and_ne_of_two_lt i (finRotate n i) hp.three_le
  have hwseg : p w ∉ segment ℝ (p i) (p (finRotate n i)) := by
    intro hw
    have he := (hp.vertex_mem_edgeSet_iff w i).mp ((polygon_edgeSet_eq_segment p i).symm ▸ hw)
    exact he.elim hwi hwr
  have hnot : ¬ SameRay ℝ (p w - p i) (p (finRotate n i) - p w) :=
    fun hs => hwseg (mem_segment_iff_sameRay.mpr hs)
  obtain ⟨e, hleft, hright⟩ := exists_continuousLinearEquiv_fst_neg_pos hdim hnot
  have hwiX : (e (p w)).1 < (e (p i)).1 := by
    simpa only [map_sub, Prod.fst_sub, sub_neg] using hleft
  have hwrX : (e (p w)).1 < (e (p (finRotate n i))).1 := by
    simpa only [map_sub, Prod.fst_sub, sub_pos] using hright
  let : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨k, hmin, htie⟩ := exists_lexicographic_min fun j => e (p j)
  have hki : k ≠ i := by
    intro he
    exact (hmin w).not_gt (he ▸ hwiX)
  have hkr : k ≠ finRotate n i := by
    intro he
    exact (hmin w).not_gt (he ▸ hwrX)
  refine ⟨e, k, hki, hkr, hmin, htie, ?_⟩
  let j := (finRotate n).symm k
  have hjk : finRotate n j = k := (finRotate n).apply_symm_apply k
  have ha : p j ≠ p k := by simpa only [hjk] using hp.hasNondegenerateEdges j
  have hb : p (finRotate n k) ≠ p k := (hp.hasNondegenerateEdges k).symm
  have hjne : j ≠ k := fun he => ha (congrArg p he)
  have hneighbors : j ≠ finRotate n k := finRotate_symm_ne_apply_of_three_le hp.three_le k
  have hsegj : segment ℝ (p k) (p j) = p.edgeSet ℝ j := by
    rw [polygon_edgeSet_eq_segment, hjk, segment_symm]
  have hsegk : segment ℝ (p k) (p (finRotate n k)) = p.edgeSet ℝ k :=
    (polygon_edgeSet_eq_segment p k).symm
  have hinter : segment ℝ (p k) (p j) ∩ segment ℝ (p k) (p (finRotate n k)) ⊆ {p k} := by
    rw [hsegj, hsegk]
    intro z hz
    have hends := hp.edges_inter j k hjne hz
    rw [hjk] at hends
    rcases hends.1 with hzj | hzk
    · rcases hends.2 with hzk | hzl
      · exact hzk
      · exact False.elim (hneighbors (hp.vertices_injective (hzj.symm.trans hzl)))
    · exact hzk
  have hfst (l : Fin n) : 0 ≤ (e (p l - p k)).1 := by
    simpa only [map_sub, Prod.fst_sub, sub_nonneg] using hmin l
  have hsnd (l : Fin n) (hl : (e (p l - p k)).1 = 0) : 0 ≤ (e (p l - p k)).2 := by
    have hl' : (e (p l)).1 = (e (p k)).1 := by
      simpa only [map_sub, Prod.fst_sub, sub_eq_zero] using hl
    simpa only [map_sub, Prod.snd_sub, sub_nonneg] using htie l hl'
  exact linearIndependent_of_lex_nonnegative e
    (not_sameRay_sub_of_segments_inter_subset_singleton ha hb hinter)
    (hfst j) (hfst (finRotate n k)) (hsnd j) (hsnd (finRotate n k))

end Poincare.Manifold.Schoenflies.Plane
