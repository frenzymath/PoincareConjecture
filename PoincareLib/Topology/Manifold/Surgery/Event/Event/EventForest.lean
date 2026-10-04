import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventGraphComponents
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# A spanning forest with actual cap indices

The pinned graph theorem chooses a forest on the exact cut vertices.
Each unordered forest edge is lifted once to an original cap index.
All other cap indices, including unused parallel edges, remain residual.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- The unordered pair of actual endpoints of one original cap index. -/
noncomputable def eventCapEnds (i : Fin (F.event T hT).cap_count) : Sym2 (EventCutVertex F T hT) :=
  s(Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint),
    Sum.inr (ConnectedComponents.mk (P i).attachmentPoint))

/-- A link has precisely the unordered endpoint pair of its original cap. -/
theorem event_isLink_iff_ends (i : Fin (F.event T hT).cap_count) (x y : EventCutVertex F T hT) :
    (eventIncidenceGraph F T hT P).IsLink i x y ↔ eventCapEnds F T hT P i = s(x, y) :=
  (eventIncidenceGraph_link F T hT P i).isLink_iff_sym2_eq

/-- A spanning forest on all actual cut vertices, with unchanged reachability. -/
structure EventSpanningForest where
  graph : SimpleGraph (EventCutVertex F T hT)
  le_adjacency : graph ≤ eventIncidenceAdjacency F T hT P
  acyclic : graph.IsAcyclic
  reachable_eq : graph.Reachable = (eventIncidenceAdjacency F T hT P).Reachable

/-- The pinned Mathlib spanning-forest theorem applies to the exact event graph. -/
theorem exists_eventSpanningForest : Nonempty (EventSpanningForest F T hT P) := by
  obtain ⟨S, hle, hacyclic, hreach⟩ :=
    (eventIncidenceAdjacency F T hT P).exists_isAcyclic_reachable_eq_le
  exact ⟨⟨S, hle, hacyclic, hreach⟩⟩

namespace EventSpanningForest

variable {F T hT P} (S : EventSpanningForest F T hT P)

/-- Every unordered forest edge has an original cap with exactly those ends. -/
theorem exists_capEdge (e : S.graph.edgeSet) :
    ∃ i, eventCapEnds F T hT P i = e.val := by
  obtain ⟨⟨x, y⟩, hxy⟩ := Sym2.mk_surjective e.val
  change s(x, y) = e.val at hxy
  have hmem : s(x, y) ∈ S.graph.edgeSet := hxy.symm ▸ e.property
  have hadj : S.graph.Adj x y := S.graph.mem_edgeSet.mp hmem
  obtain ⟨i, hi⟩ := (eventIncidenceAdjacency_iff F T hT P x y).mp (S.le_adjacency hadj)
  exact ⟨i, ((event_isLink_iff_ends F T hT P i x y).mp hi).trans hxy⟩

/-- Choose once per unordered forest edge, independently of its orientation. -/
noncomputable def capEdge (e : S.graph.edgeSet) : Fin (F.event T hT).cap_count :=
  Classical.choose (S.exists_capEdge e)

/-- The selected original cap has the literal forest edge as its endpoint pair. -/
theorem capEdge_ends (e : S.graph.edgeSet) :
    eventCapEnds F T hT P (S.capEdge e) = e.val := Classical.choose_spec (S.exists_capEdge e)

/-- Distinct forest edges select distinct original cap indices. -/
theorem capEdge_injective : Function.Injective S.capEdge := by
  intro e f h
  apply Subtype.ext
  exact (S.capEdge_ends e).symm.trans ((congrArg (eventCapEnds F T hT P) h).trans
    (S.capEdge_ends f))

/-- With either orientation the selected cap is a link between the displayed vertices. -/
theorem capEdge_link {x y : EventCutVertex F T hT} (h : S.graph.Adj x y) :
    (eventIncidenceGraph F T hT P).IsLink (S.capEdge ⟨s(x, y), h⟩) x y :=
  (event_isLink_iff_ends F T hT P _ x y).mpr (S.capEdge_ends ⟨s(x, y), h⟩)

/-- Reversing an edge uses the same original cap index. -/
theorem capEdge_reverse {x y : EventCutVertex F T hT} (h : S.graph.Adj x y) :
    S.capEdge ⟨s(x, y), h⟩ = S.capEdge ⟨s(y, x), h.symm⟩ := by
  congr 1
  exact Subtype.ext Sym2.eq_swap

/-- Exactly the original cap indices selected by the forest. -/
def selectedCaps : Set (Fin (F.event T hT).cap_count) := Set.range S.capEdge

/-- Every unselected original cap is retained as a residual edge. -/
def residualCaps : Set (Fin (F.event T hT).cap_count) := S.selectedCapsᶜ

/-- Selected and residual indices form an exact disjoint partition. -/
theorem cap_partition : Disjoint S.selectedCaps S.residualCaps ∧
    S.selectedCaps ∪ S.residualCaps = Set.univ :=
  ⟨Set.disjoint_left.mpr (fun _ hi hnot => hnot hi), Set.union_compl_self _⟩

/-- Both index families are finite because the actual cap index type is finite. -/
theorem cap_families_finite : S.selectedCaps.Finite ∧ S.residualCaps.Finite :=
  ⟨Set.toFinite _, Set.toFinite _⟩

/-- Forest components are the exact original pre-slice components. -/
theorem reachable_iff_pre_component (x y : EventCutVertex F T hT) :
    S.graph.Reachable x y ↔
      eventVertexPreComponent F T hT x = eventVertexPreComponent F T hT y := by
  rw [S.reachable_eq]
  exact eventIncidence_reachable_iff F T hT P x y

/-- The two endpoints of every original cap are joined by a genuine forest path. -/
theorem exists_capPath (i : Fin (F.event T hT).cap_count) :
    ∃ p : S.graph.Walk
      (Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint))
      (Sum.inr (ConnectedComponents.mk (P i).attachmentPoint)), p.IsPath := by
  apply SimpleGraph.Reachable.exists_isPath
  rw [S.reachable_eq]
  exact ((eventIncidenceAdjacency_iff F T hT P _ _).mpr
    ⟨i, eventIncidenceGraph_link F T hT P i⟩).reachable

/-- Lift the finite edge list of a forest walk to its chosen actual cap indices. -/
noncomputable def walkCaps {x y : EventCutVertex F T hT} (p : S.graph.Walk x y) :
    List (Fin (F.event T hT).cap_count) :=
  p.edges.attach.map (fun e => S.capEdge ⟨e.val, p.edges_subset_edgeSet e.property⟩)

/-- Every cap traversed by a lifted forest walk belongs to the selected range. -/
theorem walkCaps_mem_selected {x y : EventCutVertex F T hT} (p : S.graph.Walk x y)
    {i : Fin (F.event T hT).cap_count} (hi : i ∈ S.walkCaps p) : i ∈ S.selectedCaps := by
  obtain ⟨e, _, heq⟩ := List.mem_map.mp hi
  rw [← heq]
  exact Set.mem_range_self _

/-- In particular a residual original cap never occurs along its forest path.
Parallel residual caps are distinguished by their original indices here. -/
theorem residual_not_mem_walkCaps {x y : EventCutVertex F T hT} (p : S.graph.Walk x y)
    {i : Fin (F.event T hT).cap_count} (hi : i ∈ S.residualCaps) : i ∉ S.walkCaps p :=
  fun h => hi (S.walkCaps_mem_selected p h)

end EventSpanningForest

end PoincareMT.M38
