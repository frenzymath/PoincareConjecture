import PoincareConjecture.Proofs.M76.Mathlib.GeometricCyclePolygons

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [AddCommGroup E] [Module ℝ E]

def edgeComponents (G : SimpleGraph V) : Set G.ConnectedComponent :=
  {C | ∃ v ∈ C.supp, v ∈ G.support}

theorem mem_support_of_mem_edgeComponent (G : SimpleGraph V)
    (C : G.edgeComponents) (v : C.val) : v.val ∈ G.support := by
  obtain ⟨a, ha, has⟩ := C.property
  by_cases h : v.val = a
  · exact h ▸ has
  · exact mem_support_of_reachable h (C.val.reachable_of_mem_supp v.property ha)

theorem IsCycles.edgeComponent_two_neighbors {G : SimpleGraph V} (hG : G.IsCycles)
    (C : G.edgeComponents) (v : C.val) :
    (C.val.toSimpleGraph.neighborSet v).ncard = 2 := by
  rw [C.val.ncard_neighborSet]
  exact hG (G.mem_support.mp (G.mem_support_of_mem_edgeComponent C v))

theorem segmentCarrier_eq_iUnion_edgeComponents (G : SimpleGraph V) (p : V → E) :
    G.segmentCarrier p = ⋃ C : G.edgeComponents,
      C.val.toSimpleGraph.segmentCarrier (fun v => p v.val) := by
  ext x
  constructor
  · rintro ⟨v, w, hvw, hx⟩
    let C := G.connectedComponentMk v
    have hv : v ∈ C := rfl
    have hw : w ∈ C := C.mem_supp_of_adj_mem_supp hv hvw
    let C' : G.edgeComponents := ⟨C, v, hv, hvw.mem_support_left⟩
    exact mem_iUnion.mpr ⟨C', ⟨v, hv⟩, ⟨w, hw⟩, hvw, hx⟩
  · intro hx
    obtain ⟨C, v, w, hvw, hx⟩ := mem_iUnion.mp hx
    exact ⟨v.val, w.val, hvw, hx⟩

theorem IsCycles.exists_edgeComponent_polygons [Finite V] {G : SimpleGraph V}
    (hG : G.IsCycles) (p : V → E) (hinj : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    ∃ (n : G.edgeComponents → ℕ) (P : ∀ C, Polygon E (n C + 3)),
      (∀ C, Function.Injective (P C) ∧ (P C).HasSimplicialEdges ∧
        (P C).boundary ℝ = C.val.toSimpleGraph.segmentCarrier (fun v => p v.val)) ∧
      G.segmentCarrier p = ⋃ C, (P C).boundary ℝ ∧
      Pairwise (fun C D => Disjoint ((P C).boundary ℝ) ((P D).boundary ℝ)) := by
  have hex (C : G.edgeComponents) :=
    C.val.toSimpleGraph.exists_polygon_of_two_neighbors (fun v => p v.val)
      C.val.connected_toSimpleGraph (hG.edgeComponent_two_neighbors C)
      (hinj.comp Subtype.val_injective) (fun {_ _ _ _} hvw hab => hinter hvw hab)
  choose n P hinjP hinterP hbound using hex
  refine ⟨n, P, fun C => ⟨hinjP C, hinterP C, hbound C⟩, ?_, ?_⟩
  · simp only [hbound, G.segmentCarrier_eq_iUnion_edgeComponents p]
  · intro C D hCD
    rw [hbound, hbound]
    exact G.pairwise_disjoint_component_segmentCarrier p hinj hinter
      (fun h => hCD (Subtype.ext h))

end SimpleGraph
