import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ComponentCycleLabels
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic

/-!
# Segment carriers of graph components

A straight-edge graph decomposes into the carriers of its connected
components. Injective vertex placements with the simplicial intersection
law give disjoint component carriers. Cyclic labels identify each
degree-two component with a Mathlib polygon boundary. See Alexander
1924, p. 6 and M76 derivation 93.
-/

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The union of straight segments representing the edges of a graph.
Isolated vertices contribute no segments. See Alexander p. 6 and
M76 derivation 93. -/
def segmentCarrier (G : SimpleGraph V) (p : V → E) : Set E :=
  {x | ∃ v w, G.Adj v w ∧ x ∈ segment ℝ (p v) (p w)}

/-- The straight-edge carrier is the union of the induced component
carriers, also for empty graphs and isolated vertices. See Alexander
p. 6 and M76 derivation 93. -/
theorem segmentCarrier_eq_iUnion_components (G : SimpleGraph V) (p : V → E) :
    G.segmentCarrier p = ⋃ C : G.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => p v.val) := by
  ext x
  constructor
  · rintro ⟨v, w, hvw, hx⟩
    let C := G.connectedComponentMk v
    have hv : v ∈ C := rfl
    have hw : w ∈ C := C.mem_supp_of_adj_mem_supp hv hvw
    exact mem_iUnion.mpr ⟨C, ⟨v, hv⟩, ⟨w, hw⟩, hvw, hx⟩
  · intro hx
    obtain ⟨C, v, w, hvw, hx⟩ := mem_iUnion.mp hx
    exact ⟨v.val, w.val, hvw, hx⟩

/-- Distinct graph components have disjoint geometric carriers when
vertices are distinct and segments meet only over common endpoints.
See Alexander p. 6 and M76 derivation 93. -/
theorem pairwise_disjoint_component_segmentCarrier (G : SimpleGraph V) (p : V → E)
    (hinj : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    Pairwise fun C D : G.ConnectedComponent =>
      Disjoint (C.toSimpleGraph.segmentCarrier (fun v => p v.val))
        (D.toSimpleGraph.segmentCarrier (fun v => p v.val)) := by
  intro C D hCD
  apply Set.disjoint_left.mpr
  rintro x ⟨v, w, hvw, hx⟩ ⟨a, b, hab, hy⟩
  have hne (s : C) (t : D) : p s.val ≠ p t.val := by
    intro h
    exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex s.property
      (hinj h ▸ t.property))
  have hempty : ({p v.val, p w.val} : Set E) ∩ {p a.val, p b.val} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with ⟨h | h, k | k⟩ <;>
      exact hne _ _ (h.symm.trans k)
  have h : x ∈ convexHull ℝ (({p v.val, p w.val} : Set E) ∩ {p a.val, p b.val}) :=
    hinter hvw hab ⟨hx, hy⟩
  simp only [hempty, convexHull_empty, notMem_empty] at h

/-- Exact cyclic labels realize the graph's segment carrier as the
boundary of the corresponding polygon. See Alexander p. 6 and
M76 derivation 93. -/
theorem segmentCarrier_eq_polygonBoundary (G : SimpleGraph V) (p : V → E)
    {n : ℕ} (e : Fin (n + 3) ≃ V)
    (he : ∀ v w, G.Adj v w ↔ ∃ i, (e i = v ∧ e (i + 1) = w) ∨
      (e i = w ∧ e (i + 1) = v)) :
    G.segmentCarrier p = (Polygon.mk (fun i => p (e i))).boundary ℝ := by
  ext x
  simp only [Polygon.boundary, Polygon.edgeSet, affineSegment_eq_segment,
    finRotate_apply, mem_iUnion]
  constructor
  · rintro ⟨v, w, hvw, hx⟩
    obtain ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (he v w).mp hvw
    · exact ⟨i, hx⟩
    · exact ⟨i, by simpa only [segment_symm] using hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨e i, e (i + 1), (he _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩, hx⟩

end SimpleGraph
