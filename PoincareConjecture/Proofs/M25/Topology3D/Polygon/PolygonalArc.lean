import PoincareConjecture.Proofs.M25.Topology3D.Polygon.AdmissibleVertex

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

def polygonArcBoundary (p : Polygon E (n + 2)) : Set E :=
  ⋃ i : Fin (n + 1), p.edgeSet ℝ i.castSucc

structure IsSimplePolygonalArc (p : Polygon E (n + 2)) : Prop where

  vertices_injective : Function.Injective p

  edges_inter : ∀ i j : Fin (n + 1), i ≠ j →
    p.edgeSet ℝ i.castSucc ∩ p.edgeSet ℝ j.castSucc ⊆
      {p i.castSucc, p i.succ} ∩ {p j.castSucc, p j.succ}

def IsAdmissibleArcVertex (p : Polygon E (n + 2)) (k : Fin (n + 2)) : Prop :=
  k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
    polygonVertexTriangle p k ∩ polygonArcBoundary p =
      segment ℝ (p k) (p ((finRotate (n + 2)).symm k)) ∪
        segment ℝ (p k) (p (finRotate (n + 2) k))

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem polygon_arcEdge_eq_segment (p : Polygon E (n + 2)) (i : Fin (n + 1)) :
    p.edgeSet ℝ i.castSucc = segment ℝ (p i.castSucc) (p i.succ) := by
  have hi : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
  rw [polygon_edgeSet_eq_segment, hi]

theorem polygon_arcEdge_subset_boundary (p : Polygon E (n + 2)) (i : Fin (n + 1)) :
    p.edgeSet ℝ i.castSucc ⊆ polygonArcBoundary p :=
  subset_iUnion (fun j : Fin (n + 1) => p.edgeSet ℝ j.castSucc) i

theorem polygon_vertex_mem_arcBoundary (p : Polygon E (n + 2)) (k : Fin (n + 2)) :
    p k ∈ polygonArcBoundary p := by
  by_cases hk : k = Fin.last (n + 1)
  · subst k
    apply polygon_arcEdge_subset_boundary p (Fin.last n)
    rw [polygon_arcEdge_eq_segment]
    exact right_mem_segment ℝ _ _
  · have hlt : k.val < n + 1 := by
      have hh : k < Fin.last (n + 1) := Fin.lt_last_iff_ne_last.mpr hk
      exact hh
    let i : Fin (n + 1) := ⟨k.val, hlt⟩
    have hik : i.castSucc = k := Fin.ext rfl
    apply polygon_arcEdge_subset_boundary p i
    rw [polygon_arcEdge_eq_segment, hik]
    exact left_mem_segment ℝ _ _

theorem polygon_arcBoundary_isCompact (p : Polygon E (n + 2)) :
    IsCompact (polygonArcBoundary p) :=
  isCompact_iUnion (fun i : Fin (n + 1) => polygon_edgeSet_isCompact p i.castSucc)

theorem polygon_arcBoundary_isClosed (p : Polygon E (n + 2)) :
    IsClosed (polygonArcBoundary p) := (polygon_arcBoundary_isCompact p).isClosed

theorem IsSimplePolygonalArc.edge_endpoints_ne {p : Polygon E (n + 2)}
    (hp : IsSimplePolygonalArc p) (i : Fin (n + 1)) : p i.castSucc ≠ p i.succ := by
  intro h
  have hh := congrArg Fin.val (hp.vertices_injective h)
  simp only [Fin.val_castSucc, Fin.val_succ] at hh
  omega

theorem IsSimplePolygonalArc.edgePath_injective {p : Polygon E (n + 2)}
    (hp : IsSimplePolygonalArc p) (i : Fin (n + 1)) :
    Function.Injective (p.edgePath ℝ i.castSucc) := by
  apply AffineMap.lineMap_injective ℝ
  have hi : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
  rw [hi]
  exact hp.edge_endpoints_ne i

theorem IsSimplePolygonalArc.edge_inter_eq {p : Polygon E (n + 2)}
    (hp : IsSimplePolygonalArc p) {i j : Fin (n + 1)} (hij : i ≠ j) :
    p.edgeSet ℝ i.castSucc ∩ p.edgeSet ℝ j.castSucc =
      {p i.castSucc, p i.succ} ∩ {p j.castSucc, p j.succ} := by
  apply subset_antisymm (hp.edges_inter i j hij)
  intro x hx
  rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment]
  constructor
  · rcases hx.1 with rfl | hx
    · exact left_mem_segment ℝ _ _
    · exact hx ▸ right_mem_segment ℝ _ _
  · rcases hx.2 with rfl | hx
    · exact left_mem_segment ℝ _ _
    · exact hx ▸ right_mem_segment ℝ _ _

theorem IsSimplePolygonalArc.vertex_mem_edgeSet_iff {p : Polygon E (n + 2)}
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2)) (i : Fin (n + 1)) :
    p k ∈ p.edgeSet ℝ i.castSucc ↔ k = i.castSucc ∨ k = i.succ := by
  constructor
  · intro hk
    have hother (j : Fin (n + 1)) (hj : p k ∈ p.edgeSet ℝ j.castSucc)
        (hij : i ≠ j) : k = i.castSucc ∨ k = i.succ := by
      have hh := (hp.edges_inter i j hij ⟨hk, hj⟩).1
      rcases hh with hh | hh
      · exact Or.inl (hp.vertices_injective hh)
      · exact Or.inr (hp.vertices_injective hh)
    by_cases hlast : k = Fin.last (n + 1)
    · by_cases hi : i = Fin.last n
      · right
        rw [hi, hlast]
        rfl
      · apply hother (Fin.last n) ?_ hi
        rw [polygon_arcEdge_eq_segment, hlast]
        exact right_mem_segment ℝ _ _
    · have hlt : k.val < n + 1 := Fin.lt_last_iff_ne_last.mpr hlast
      let j : Fin (n + 1) := ⟨k.val, hlt⟩
      have hjk : j.castSucc = k := Fin.ext rfl
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hjk.symm)
      · apply hother j ?_ hij
        rw [polygon_arcEdge_eq_segment, hjk]
        exact left_mem_segment ℝ _ _
  · rintro (rfl | rfl)
    · rw [polygon_arcEdge_eq_segment]
      exact left_mem_segment ℝ _ _
    · rw [polygon_arcEdge_eq_segment]
      exact right_mem_segment ℝ _ _

end PoincareConjecture.M25.Topology3D
