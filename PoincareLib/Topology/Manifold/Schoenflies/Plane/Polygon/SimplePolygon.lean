import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.BoundaryBasics

/-!
# Simple closed polygons with straight vertices

The closed polygon condition used in Cairns (1951), Theorem 2.1,
pp. 860-861, and Munkres (1960), Lemma 2.3, p. 195. Vertices are distinct
and different edges meet only at their common endpoints. No noncollinearity,
Jordan separation, or filling is built into this condition.
See `smale/derivations/2026-09-21-polygon-basics.md` for the source review.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- A simple closed polygon, allowing straight vertices; Munkres, Lemma 2.3, p. 195. -/
structure IsSimplePolygon (p : Polygon E n) : Prop where
  /-- A closed simple polygon has at least three vertices; Cairns, Theorem 2.1, p. 860. -/
  three_le : 3 ≤ n
  /-- All vertices are distinct; Munkres, Lemma 2.3, p. 195. -/
  vertices_injective : Function.Injective p
  /-- Different edges meet only at common endpoints; Cairns, Theorem 2.1, p. 860. -/
  edges_inter : ∀ i j, i ≠ j → p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
    {p i, p (finRotate n i)} ∩ {p j, p (finRotate n j)}

/-- Simple polygon edges have distinct endpoints; Munkres, Lemma 2.3, p. 195. -/
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

/-- An edge of a simple polygon has an injective affine parametrization; Munkres, 2.3, p. 195. -/
theorem IsSimplePolygon.edgePath_injective {p : Polygon E n} (hp : IsSimplePolygon p)
    (i : Fin n) : Function.Injective (p.edgePath ℝ i) :=
  AffineMap.lineMap_injective ℝ (hp.hasNondegenerateEdges i)

/-- Distinct edges intersect exactly at their common endpoints; Cairns, 2.1, p. 860. -/
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

/-- Only the endpoint vertices lie on a simple polygon edge; Munkres, 2.3, p. 195. -/
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

/-- Interior edge parameters miss every other edge; Munkres, Lemma 2.3, p. 195. -/
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

end Poincare.Manifold.Schoenflies.Plane
