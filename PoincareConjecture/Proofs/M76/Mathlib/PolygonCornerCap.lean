import PoincareConjecture.Proofs.M76.Mathlib.PlanarSegmentCap
import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges










set_option autoImplicit false

open Set

namespace Polygon

private theorem eq_endpoint_of_mem_two_edges {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {i j : Fin (n + 3)} (hne : j ≠ i) {q : ℝ × ℝ}
    (hqj : q ∈ P.edgeSet ℝ j) (hqi : q ∈ P.edgeSet ℝ i) :
    q = P i ∨ q = P (finRotate (n + 3) i) := by
  by_cases hv : q ∈ range P
  · obtain ⟨k, rfl⟩ := hv
    exact Or.imp (congrArg P) (congrArg P) ((P.vertex_mem_edgeSet_iff hP hinj k i).mp hqi)
  · exact (hne (P.eq_of_mem_edgeSets_of_not_vertex hP hinj hv hqj hqi)).elim





theorem disjoint_boundary_corner_cap {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin (n + 3))
    (hprev : P ((finRotate (n + 3)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 3) i) = (0, 1)) {h : ℝ} (hh : h ≤ 1)
    (hvertices : ∀ j, ¬ (0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 < h)) :
    Disjoint {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < h} (P.boundary ℝ) := by
  apply Set.disjoint_left.mpr
  intro q hq hqb
  obtain ⟨j, hqj⟩ := mem_iUnion.mp hqb
  have hseg : segment ℝ (P j) (P (finRotate (n + 3) j)) = P.edgeSet ℝ j := by
    rw [edgeSet, affineSegment_eq_segment]
  have hji : j ≠ i := by
    rintro rfl
    have hmem : q ∈ segment ℝ (0, 0) (0, 1) := by
      simpa only [edgeSet, affineSegment_eq_segment, hcenter, hnext] using hqj
    have hx : q.1 = 0 := by
      simpa only [segment_same, mem_singleton_iff] using
        (Prod.segment_subset (𝕜 := ℝ) (0, 0) (0, 1) hmem).1
    exact hq.1.ne' hx
  have hjprev : j ≠ (finRotate (n + 3)).symm i := by
    rintro rfl
    have hmem : q ∈ segment ℝ (1, 0) (0, 0) := by
      simpa only [edgeSet, affineSegment_eq_segment, Equiv.apply_symm_apply,
        hprev, hcenter] using hqj
    have hy : q.2 = 0 := by
      simpa only [segment_same, mem_singleton_iff] using
        (Prod.segment_subset (𝕜 := ℝ) (1, 0) (0, 0) hmem).2
    exact hq.2.1.ne' hy
  have horigin : (0, 0) ∉ P.edgeSet ℝ j := by
    rw [← hcenter, P.vertex_mem_edgeSet_iff hP hinj]
    rintro (hij | hij)
    · exact hji hij.symm
    · apply hjprev
      simpa only [Equiv.symm_apply_apply] using
        (congrArg (finRotate (n + 3)).symm hij).symm
  have havoid : ∀ r ∈ segment ℝ (P j) (P (finRotate (n + 3) j)),
      ¬ ((r.1 = 0 ∧ 0 ≤ r.2 ∧ r.2 < h) ∨ (r.2 = 0 ∧ 0 ≤ r.1 ∧ r.1 < h)) := by
    intro r hr haxis
    have hrj : r ∈ P.edgeSet ℝ j := hseg ▸ hr
    rcases haxis with ⟨hx, hry, hrh⟩ | ⟨hy, hrx, hrh⟩
    · have hri : r ∈ P.edgeSet ℝ i := by
        rw [edgeSet, affineSegment_eq_segment, hcenter, hnext]
        refine ⟨1 - r.2, r.2, by linarith, hry, by ring, ?_⟩
        ext <;> simp [hx]
      rcases eq_endpoint_of_mem_two_edges P hP hinj hji hrj hri with heq | heq
      · exact horigin (by simpa only [heq, hcenter] using hrj)
      · have hy1 : r.2 = 1 := by rw [heq, hnext]
        linarith
    · have hri : r ∈ P.edgeSet ℝ ((finRotate (n + 3)).symm i) := by
        rw [edgeSet, affineSegment_eq_segment, Equiv.apply_symm_apply, hprev, hcenter]
        refine ⟨r.1, 1 - r.1, hrx, by linarith, by ring, ?_⟩
        ext <;> simp [hy]
      rcases eq_endpoint_of_mem_two_edges P hP hinj hjprev hrj hri with heq | heq
      · have hx1 : r.1 = 1 := by rw [heq, hprev]
        linarith
      · exact horigin (by simpa only [heq, Equiv.apply_symm_apply, hcenter] using hrj)
  rcases PlanarSegment.endpoint_mem_cap_of_inter (hseg.symm ▸ hqj) hq.1 hq.2.1 hq.2.2 havoid with
    hj | hj
  · exact hvertices j hj
  · exact hvertices (finRotate (n + 3) j) hj

end Polygon
