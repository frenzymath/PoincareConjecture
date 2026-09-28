import PoincareConjecture.Proofs.M76.Mathlib.PolygonCornerDiagonal
import PoincareConjecture.Proofs.M76.Mathlib.PlanarUnitBase










set_option autoImplicit false

open Set

namespace Polygon

open Fin.NatCast

private theorem prev_ne_add {n : ℕ} (i : Fin (n + 4)) (k : ℕ) (hk : k + 1 < n + 4) :
    i - 1 ≠ i + (↑k : Fin (n + 4)) := by
  intro heq
  have heq' := congrArg (fun x : Fin (n + 4) => x + 1) heq
  have hz : (↑k : Fin (n + 4)) + 1 = 0 := add_left_cancel
    (show i + ((↑k : Fin (n + 4)) + 1) = i + 0 by
      simpa only [sub_add_cancel, add_assoc, add_zero] using heq'.symm)
  have hval := congrArg Fin.val hz
  change (k % (n + 4) + 1 % (n + 4)) % (n + 4) = 0 at hval
  rw [Nat.mod_eq_of_lt (by omega : k < n + 4),
    Nat.mod_eq_of_lt (by omega : 1 < n + 4), Nat.mod_eq_of_lt hk] at hval
  omega

private theorem neighbors_not_edge {n : ℕ} (i j : Fin (n + 4)) :
    ¬ (((finRotate (n + 4)).symm i = j ∨ (finRotate (n + 4)).symm i = finRotate (n + 4) j) ∧
      (finRotate (n + 4) i = j ∨ finRotate (n + 4) i = finRotate (n + 4) j)) := by
  rintro ⟨hp | hp, hn | hn⟩
  · apply prev_ne_add i 1 (by omega)
    simpa only [finRotate_symm_apply, finRotate_apply, Nat.cast_one] using hp.trans hn.symm
  · have hji := (finRotate (n + 4)).injective hn
    apply prev_ne_add i 0 (by omega)
    simpa only [finRotate_symm_apply, Nat.cast_zero, add_zero] using hp.trans hji.symm
  · apply prev_ne_add i 2 (by omega)
    have heq := hp.trans (congrArg (finRotate (n + 4)) hn.symm)
    simpa only [finRotate_symm_apply, finRotate_apply, add_assoc, one_add_one_eq_two,
      Nat.cast_ofNat] using heq
  · apply prev_ne_add i 1 (by omega)
    simpa only [finRotate_symm_apply, finRotate_apply, Nat.cast_one] using hp.trans hn.symm




theorem disjoint_boundary_empty_triangle_base {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 4))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin (n + 4))
    (hprev : P ((finRotate (n + 4)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 4) i) = (0, 1))
    (hvertices : ∀ j, ¬ (0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 ≤ 1)) :
    Disjoint {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 = 1} (P.boundary ℝ) := by
  have hcap := P.disjoint_boundary_corner_cap hP hinj i hprev hcenter hnext le_rfl
    (fun j hj => hvertices j ⟨hj.1, hj.2.1, hj.2.2.le⟩)
  apply Set.disjoint_left.mpr
  intro q hq hqb
  have hqv : q ∉ range P := by
    rintro ⟨k, rfl⟩
    exact hvertices k ⟨hq.1, hq.2.1, hq.2.2.le⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hqb
  have hseg : segment ℝ (P j) (P (finRotate (n + 4) j)) = P.edgeSet ℝ j := by
    rw [edgeSet, affineSegment_eq_segment]
  have hqseg := hseg.symm ▸ hj
  have hqopen : q ∈ openSegment ℝ (P j) (P (finRotate (n + 4) j)) :=
    mem_openSegment_of_ne_left_right
      (fun h => hqv ⟨j, h⟩) (fun h => hqv ⟨finRotate (n + 4) j, h⟩) hqseg
  have hmiss : ∀ r ∈ segment ℝ (P j) (P (finRotate (n + 4) j)),
      ¬ (0 < r.1 ∧ 0 < r.2 ∧ r.1 + r.2 < 1) := by
    intro r hr hrc
    exact Set.disjoint_left.mp hcap hrc (mem_iUnion.mpr ⟨j, hseg ▸ hr⟩)
  obtain ⟨hja, hjb⟩ := PlanarSegment.endpoint_heights_eq_of_miss_cap hqopen hq.1 hq.2.1 hq.2.2 hmiss
  have hbase := PlanarSegment.unit_base_subset_of_inter hja hjb
    (fun h => hvertices j ⟨h.1, h.2, hja.le⟩)
    (fun h => hvertices (finRotate (n + 4) j) ⟨h.1, h.2, hjb.le⟩)
    hqseg hq.1 hq.2.1 hq.2.2
  have hpa : P ((finRotate (n + 4)).symm i) ∈ P.edgeSet ℝ j := by
    rw [hprev, ← hseg]
    exact hbase (left_mem_segment ℝ _ _)
  have hpc : P (finRotate (n + 4) i) ∈ P.edgeSet ℝ j := by
    rw [hnext, ← hseg]
    exact hbase (right_mem_segment ℝ _ _)
  exact neighbors_not_edge i j
    ⟨(P.vertex_mem_edgeSet_iff hP hinj _ j).mp hpa,
      (P.vertex_mem_edgeSet_iff hP hinj _ j).mp hpc⟩




theorem empty_triangle_base_subset_inside {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 4))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin (n + 4))
    (hprev : P ((finRotate (n + 4)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 4) i) = (0, 1))
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L (P j) ≤ 0) (hdir : 0 < L (-1, -1))
    (hvertices : ∀ j, ¬ (0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 ≤ 1)) :
    {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 = 1} ⊆ P.inside := by
  have hcap := P.corner_cap_subset_inside hP hinj i hprev hcenter hnext L hL hdir zero_lt_one le_rfl
    (fun j hj => hvertices j ⟨hj.1, hj.2.1, hj.2.2.le⟩)
  have hbase := P.disjoint_boundary_empty_triangle_base hP hinj i hprev hcenter hnext hvertices
  intro q hq
  have hsegment : openSegment ℝ (0, 0) q ⊆ P.inside := by
    have hsub := openSegment_zero_subset_cap hq.1 hq.2.1
    rw [hq.2.2] at hsub
    exact hsub.trans hcap
  have hqcl : q ∈ closure P.inside := closure_mono hsegment
    (segment_subset_closure_openSegment (right_mem_segment ℝ (0, 0) q))
  rw [closure_eq_self_union_frontier, P.frontier_inside hP hinj] at hqcl
  exact hqcl.resolve_right (Set.disjoint_left.mp hbase hq)



theorem opposite_edge_subset_inside_of_empty_triangle {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 4)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (i : Fin (n + 4))
    (hprev : P ((finRotate (n + 4)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 4) i) = (0, 1))
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L (P j) ≤ 0) (hdir : 0 < L (-1, -1))
    (hvertices : ∀ j, ¬ (0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 ≤ 1)) :
    openSegment ℝ (P ((finRotate (n + 4)).symm i)) (P (finRotate (n + 4) i)) ⊆ P.inside := by
  rw [hprev, hnext]
  intro q hq
  apply P.empty_triangle_base_subset_inside hP hinj i hprev hcenter hnext L hL hdir hvertices
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
  change 0 < a * 1 + b * 0 ∧ 0 < a * 0 + b * 1 ∧
    (a * 1 + b * 0) + (a * 0 + b * 1) = 1
  simpa only [mul_one, mul_zero, add_zero, zero_add] using And.intro ha (And.intro hb hab)





theorem exists_diagonal_of_normalized_corner {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 4))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin (n + 4))
    (hprev : P ((finRotate (n + 4)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 4) i) = (0, 1))
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L (P j) ≤ 0) (hdir : 0 < L (-1, -1)) :
    ∃ a b : Fin (n + 4), a ≠ b ∧ b ≠ finRotate (n + 4) a ∧
      a ≠ finRotate (n + 4) b ∧ openSegment ℝ (P a) (P b) ⊆ P.inside := by
  by_cases hex : ∃ j, 0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 ≤ 1
  · obtain ⟨j, hji, hjprev, hjnext, hd⟩ :=
      P.exists_corner_diagonal_of_triangle_vertex hP hinj i hprev hcenter hnext L hL hdir hex
    refine ⟨i, j, hji.symm, hjnext, ?_, hd⟩
    intro hij
    apply hjprev
    simpa only [Equiv.symm_apply_apply] using
      (congrArg (finRotate (n + 4)).symm hij).symm
  · have hvertices := not_exists.mp hex
    refine ⟨(finRotate (n + 4)).symm i, finRotate (n + 4) i, ?_, ?_, ?_,
      P.opposite_edge_subset_inside_of_empty_triangle hP hinj i hprev hcenter hnext L hL hdir
        hvertices⟩
    · intro heq
      exact neighbors_not_edge i ((finRotate (n + 4)).symm i) ⟨Or.inl rfl, Or.inl heq.symm⟩
    · intro heq
      exact neighbors_not_edge i ((finRotate (n + 4)).symm i) ⟨Or.inl rfl, Or.inr heq⟩
    · intro heq
      exact neighbors_not_edge i (finRotate (n + 4) i) ⟨Or.inr heq, Or.inl rfl⟩

end Polygon
