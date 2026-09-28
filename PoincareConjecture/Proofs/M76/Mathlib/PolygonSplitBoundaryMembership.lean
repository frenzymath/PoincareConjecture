import PoincareConjecture.Proofs.M76.Mathlib.PolygonDiagonalPartition
import PoincareConjecture.Proofs.M76.Mathlib.FrontierPieceMembership









set_option autoImplicit false

open Set

namespace Polygon




theorem boundary_membership_split {m n : ℕ} (u : Fin (m + 2) → ℝ × ℝ)
    (v : Fin (n + 2) → ℝ × ℝ)
    (hP : (mk (Fin.append u v)).HasSimplicialEdges)
    (hinj : Function.Injective (Fin.append u v))
    (hd : openSegment ℝ (u 0) (v 0) ⊆ (mk (Fin.append u v)).inside) :
    (∀ x ∈ closure (mk (Fin.snoc u (v 0))).inside,
      x ∈ (mk (Fin.append u v)).boundary ℝ ↔
        x ∈ (mk (Fin.snoc u (v 0))).boundary ℝ ∧ x ∉ openSegment ℝ (u 0) (v 0)) ∧
    (∀ x ∈ closure (mk (Fin.snoc v (u 0))).inside,
      x ∈ (mk (Fin.append u v)).boundary ℝ ↔
        x ∈ (mk (Fin.snoc v (u 0))).boundary ℝ ∧ x ∉ openSegment ℝ (u 0) (v 0)) := by
  have hchord : segment ℝ (u 0) (v 0) ∩ (mk (Fin.append u v)).boundary ℝ ⊆ {u 0, v 0} := by
    rintro x ⟨hx, hxb⟩
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with rfl | rfl | hx
    · simp
    · simp
    · exact ((hd hx).1 hxb).elim
  obtain ⟨hsQ, hsR⟩ := hasSimplicialEdges_split u v hP hinj hchord
  obtain ⟨hiQ, hiR⟩ := injective_split u v hinj
  obtain ⟨_, hcover, _⟩ := region_partition_split u v hP hinj hd
  have hfP : frontier (closure (mk (Fin.append u v)).inside) =
      (mk (Fin.append u v)).boundary ℝ := by
    cases n <;> exact frontier_closure_inside _ hP hinj
  have hiP : interior (closure (mk (Fin.append u v)).inside) =
      (mk (Fin.append u v)).inside := by
    cases n <;> exact interior_closure_inside _ hP hinj
  have hfQ := frontier_closure_inside (mk (Fin.snoc u (v 0))) hsQ hiQ
  have hfR := frontier_closure_inside (mk (Fin.snoc v (u 0))) hsR hiR
  have hvertex (i) : (Fin.append u v) i ∈ (mk (Fin.append u v)).boundary ℝ := by
    exact mem_iUnion.mpr ⟨i, 0, by simp, by simp [AffineMap.lineMap_apply_zero]⟩
  have hu : u 0 ∈ (mk (Fin.append u v)).boundary ℝ := by
    simpa only [Fin.append_left] using hvertex ((0 : Fin (m + 2)).castAdd (n + 2))
  have hv : v 0 ∈ (mk (Fin.append u v)).boundary ℝ := by
    simpa only [Fin.append_right] using hvertex (Fin.natAdd (m + 2) (0 : Fin (n + 2)))
  have hboth : (mk (Fin.snoc u (v 0))).boundary ℝ ∪ (mk (Fin.snoc v (u 0))).boundary ℝ ⊆
      (mk (Fin.append u v)).boundary ℝ ∪ openSegment ℝ (u 0) (v 0) := by
    rw [boundary_split_union]
    rintro x (hx | hx)
    · exact Or.inl hx
    · rw [← insert_endpoints_openSegment] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl hu
      · exact Or.inl hv
      · exact Or.inr hx
  have hdi : openSegment ℝ (u 0) (v 0) ⊆ interior (closure (mk (Fin.append u v)).inside) := by
    rwa [hiP]
  constructor
  · intro x hx
    have hsub : closure (mk (Fin.snoc u (v 0))).inside ⊆ closure (mk (Fin.append u v)).inside := by
      rw [hcover]
      exact subset_union_left
    have hfront : frontier (closure (mk (Fin.snoc u (v 0))).inside) ⊆
        frontier (closure (mk (Fin.append u v)).inside) ∪ openSegment ℝ (u 0) (v 0) := by
      rw [hfQ, hfP]
      exact subset_union_left.trans hboth
    simpa only [hfQ, hfP] using frontier_mem_iff_of_subset hsub hfront hdi hx
  · intro x hx
    have hsub : closure (mk (Fin.snoc v (u 0))).inside ⊆ closure (mk (Fin.append u v)).inside := by
      rw [hcover]
      exact subset_union_right
    have hfront : frontier (closure (mk (Fin.snoc v (u 0))).inside) ⊆
        frontier (closure (mk (Fin.append u v)).inside) ∪ openSegment ℝ (u 0) (v 0) := by
      rw [hfR, hfP]
      exact subset_union_right.trans hboth
    simpa only [hfR, hfP] using frontier_mem_iff_of_subset hsub hfront hdi hx

end Polygon
