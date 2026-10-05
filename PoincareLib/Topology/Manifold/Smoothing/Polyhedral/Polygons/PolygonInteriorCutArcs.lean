import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.FinePolygonSubdivision
import Mathlib.Order.Interval.Set.Infinite

/-!
# Actual polygon arcs with interior cut points

Cut each edge at a point outside a prescribed finite set.
The two adjacent subsegments retain the intervening original
vertex and cover the original polygon exactly. See Alexander
1924, pp. 6--8, Hudson 1969, pp. 12--19 and M76 derivation 285.
-/

set_option autoImplicit false

open Set AffineMap

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The marked point on an original edge, with its actual
affine parameter. See M76 derivation 285. -/
def edgeCut (P : Polygon E n) (t : Fin n → ℝ) (i : Fin n) : E :=
  lineMap (P i) (P (finRotate n i)) (t i)

/-- The whole polygon arc from one edge-interior mark to
the next, retaining their common vertex. The two parameter
intervals may contain an original corner. See derivation 285. -/
def cutArc (P : Polygon E n) (t : Fin n → ℝ) (i : Fin n) : Set E :=
  (lineMap (P i) (P (finRotate n i)) '' Icc (t i) 1) ∪
    (lineMap (P (finRotate n i)) (P (finRotate n (finRotate n i))) ''
      Icc 0 (t (finRotate n i)))

/-- Every edge of a simple polygon admits an interior mark
outside an arbitrary finite ambient set. The choices retain
the original edge parameters. See M76 derivation 285. -/
theorem exists_edge_cuts_avoiding (P : Polygon E (n + 3))
    (hinj : Function.Injective P) {F : Set E} (hF : F.Finite) :
    ∃ t : Fin (n + 3) → ℝ, ∀ i, t i ∈ Ioo (0 : ℝ) 1 ∧ P.edgeCut t i ∉ F := by
  classical
  have h (i : Fin (n + 3)) : ∃ r ∈ Ioo (0 : ℝ) 1,
      lineMap (P i) (P (finRotate (n + 3) i)) r ∉ F := by
    have hfinite : ((lineMap (P i) (P (finRotate (n + 3) i))) ⁻¹' F).Finite :=
      Set.Finite.preimage
        (lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i)).injOn hF
    exact (Ioo_infinite zero_lt_one).exists_notMem_finite hfinite
  choose t ht havoid using h
  exact ⟨t, fun i => ⟨ht i, havoid i⟩⟩

/-- The chosen edge mark lies on its literal original edge.
See M76 derivation 285. -/
theorem edgeCut_mem_edgeSet (P : Polygon E n) (t : Fin n → ℝ)
    {i : Fin n} (ht : t i ∈ Icc (0 : ℝ) 1) : P.edgeCut t i ∈ P.edgeSet ℝ i :=
  ⟨t i, ht, rfl⟩

/-- Interior cut points on distinct edges of a simple polygon
are distinct, including the cyclic closing edge.
See Hudson pp. 12--19 and M76 derivation 285. -/
theorem edgeCut_injective (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) :
    Function.Injective (P.edgeCut t) := by
  intro i j hij
  exact (P.eq_of_halfOpen_edge_parameters hP hinj
    ⟨(ht i).1.le, (ht i).2⟩ ⟨(ht j).1.le, (ht j).2⟩ hij).1

/-- An interior edge cut is not an original polygon vertex.
See the exact edge-incidence check in M76 derivation 285. -/
theorem edgeCut_notMem_range (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) {i : Fin (n + 3)} (ht : t i ∈ Ioo (0 : ℝ) 1) :
    P.edgeCut t i ∉ range P := by
  rintro ⟨j, hj⟩
  have heq : lineMap (P i) (P (finRotate (n + 3) i)) (t i) =
      lineMap (P j) (P (finRotate (n + 3) j)) (0 : ℝ) := by
    rw [lineMap_apply_zero]
    exact hj.symm
  have h := P.eq_of_halfOpen_edge_parameters hP hinj
    ⟨ht.1.le, ht.2⟩ ⟨le_rfl, zero_lt_one⟩ heq
  exact ht.1.ne' h.2

/-- A cut arc lies in its two complete adjacent original
edges; no new chord is introduced. See M76 derivation 285. -/
theorem cutArc_subset_adjacent_edges (P : Polygon E n) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    P.cutArc t i ⊆ P.edgeSet ℝ i ∪ P.edgeSet ℝ (finRotate n i) := by
  rintro x (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
  · exact Or.inl ⟨r, ⟨(ht i).1.trans hr.1, hr.2⟩, rfl⟩
  · exact Or.inr ⟨r, ⟨hr.1, hr.2.trans (ht _).2⟩, rfl⟩

/-- The complete cyclic family of cut arcs covers precisely
the original boundary, including all original vertices and
all chosen marks. See Alexander pp. 6--8 and derivation 285. -/
theorem iUnion_cutArc (P : Polygon E n) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) :
    (⋃ i, P.cutArc t i) = P.boundary ℝ := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases P.cutArc_subset_adjacent_edges t ht i hi with hx | hx
    · exact mem_iUnion.mpr ⟨i, hx⟩
    · exact mem_iUnion.mpr ⟨finRotate n i, hx⟩
  · intro x hx
    obtain ⟨i, r, hr, rfl⟩ := mem_iUnion.mp hx
    by_cases hrt : t i ≤ r
    · exact mem_iUnion.mpr ⟨i, Or.inl ⟨r, ⟨hrt, hr.2⟩, rfl⟩⟩
    · apply mem_iUnion.mpr
      refine ⟨(finRotate n).symm i, Or.inr ?_⟩
      simpa only [Equiv.apply_symm_apply] using
        (show lineMap (P i) (P (finRotate n i)) r ∈
          lineMap (P i) (P (finRotate n i)) '' Icc 0 (t i) from
          ⟨r, ⟨hr.1, (lt_of_not_ge hrt).le⟩, rfl⟩)

/-- Actual cyclic arcs subordinate to an ambient cover can
have all endpoints avoid a finite forbidden set. The exact
original boundary, its corners and the cyclic mark labels
are retained. See Alexander pp. 6--8 and derivation 285. -/
theorem exists_subordinate_cut_arcs (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {ι : Type*} (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hcover : P.boundary ℝ ⊆ ⋃ i, U i) {F : Set E} (hF : F.Finite) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)) (t : Fin (N + 3) → ℝ),
      Q.HasSimplicialEdges ∧ Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      (∀ i, t i ∈ Ioo (0 : ℝ) 1 ∧ Q.edgeCut t i ∉ F) ∧
      Function.Injective (Q.edgeCut t) ∧
      (⋃ i, Q.cutArc t i) = P.boundary ℝ ∧
      ∀ i, ∃ j, Q.cutArc t i ⊆ U j := by
  obtain ⟨N, Q, hQ, hQi, hQP, hQU⟩ :=
    P.exists_subdivision_subordinate_adjacent_edges hP hinj U hU hcover
  obtain ⟨t, ht⟩ := Q.exists_edge_cuts_avoiding hQi hF
  have htt (i) := (ht i).1
  have htc (i) : t i ∈ Icc (0 : ℝ) 1 := ⟨(htt i).1.le, (htt i).2.le⟩
  refine ⟨N, Q, t, hQ, hQi, hQP, ht, Q.edgeCut_injective hQ hQi t htt,
    (Q.iUnion_cutArc t htc).trans hQP, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hQU i
  exact ⟨j, (Q.cutArc_subset_adjacent_edges t htc i).trans hj⟩

end Polygon
