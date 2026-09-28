import PoincareConjecture.Proofs.M25.Topology3D.Polygon.BoundaryBasics

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

structure IsSimplePolygon (p : Polygon E n) : Prop where

  three_le : 3 ≤ n

  vertices_injective : Function.Injective p

  edges_inter : ∀ i j, i ≠ j → p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
    {p i, p (finRotate n i)} ∩ {p j, p (finRotate n j)}

theorem IsSimplePolygon.hasNondegenerateEdges {p : Polygon E n} (hp : IsSimplePolygon p) :
    p.HasNondegenerateEdges := by
  intro i hi
  have heq := hp.vertices_injective hi
  have hn : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  by_cases hlast : i = Fin.last m
  · rw [hlast, finRotate_last] at heq
    have hval : m = 0 := congrArg Fin.val heq
    have hthree := hp.three_le
    omega
  · have hval : (i : ℕ) = (finRotate (m + 1) i : ℕ) := congrArg Fin.val heq
    rw [coe_finRotate_of_ne_last hlast] at hval
    omega

end Module

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem IsSimplePolygon.edgePath_injective {p : Polygon E n} (hp : IsSimplePolygon p)
    (i : Fin n) : Function.Injective (p.edgePath ℝ i) :=
  AffineMap.lineMap_injective ℝ (hp.hasNondegenerateEdges i)

theorem IsSimplePolygon.edge_inter_eq {p : Polygon E n} (hp : IsSimplePolygon p)
    {i j : Fin n} (hij : i ≠ j) :
    p.edgeSet ℝ i ∩ p.edgeSet ℝ j =
      {p i, p (finRotate n i)} ∩ {p j, p (finRotate n j)} := by
  apply subset_antisymm (hp.edges_inter i j hij)
  intro x hx
  constructor
  · rcases hx.1 with rfl | hx
    · exact polygon_left_mem_edgeSet p i
    · exact hx ▸ polygon_right_mem_edgeSet p i
  · rcases hx.2 with rfl | hx
    · exact polygon_left_mem_edgeSet p j
    · exact hx ▸ polygon_right_mem_edgeSet p j

theorem IsSimplePolygon.vertex_mem_edgeSet_iff {p : Polygon E n} (hp : IsSimplePolygon p)
    (k i : Fin n) : p k ∈ p.edgeSet ℝ i ↔ k = i ∨ k = finRotate n i := by
  constructor
  · intro hk
    by_cases hki : k = i
    · exact Or.inl hki
    · have hx := (hp.edges_inter i k (Ne.symm hki) ⟨hk, polygon_left_mem_edgeSet p k⟩).1
      rcases hx with hx | hx
      · exact Or.inl (hp.vertices_injective hx)
      · exact Or.inr (hp.vertices_injective hx)
  · rintro (rfl | rfl)
    · exact polygon_left_mem_edgeSet p _
    · exact polygon_right_mem_edgeSet p i

theorem IsSimplePolygon.edgePath_notMem_other_edge {p : Polygon E n}
    (hp : IsSimplePolygon p) {i j : Fin n} (hij : i ≠ j) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    p.edgePath ℝ i t ∉ p.edgeSet ℝ j := by
  intro hj
  have hi : p.edgePath ℝ i t ∈ p.edgeSet ℝ i :=
    ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hx := (hp.edges_inter i j hij ⟨hi, hj⟩).1
  rcases hx with hx | hx
  · have heq : t = 0 := hp.edgePath_injective i (by simpa [Polygon.edgePath] using hx)
    exact ht.1.ne' heq
  · have heq : t = 1 := hp.edgePath_injective i (by simpa [Polygon.edgePath] using hx)
    exact ht.2.ne heq

end Normed

end PoincareConjecture.M25.Topology3D
