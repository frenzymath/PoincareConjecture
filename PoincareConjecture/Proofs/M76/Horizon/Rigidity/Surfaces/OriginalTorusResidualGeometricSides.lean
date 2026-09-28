import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualSideOrder
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricWalkPaths

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

private theorem exists_edge_endpoints
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    ∃ u v : K.vertices, u ≠ v ∧ e.val = {u, v} := by
  exact Finset.card_eq_two.mp e.property.2

private theorem exists_edge_endpoint_pair
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    ∃ uv : K.vertices × K.vertices,
      uv.1 ≠ uv.2 ∧ e.val = {uv.1, uv.2} := by
  obtain ⟨u, v, huv, he⟩ := exists_edge_endpoints K e
  exact ⟨(u, v), huv, he⟩

noncomputable def residualEdgeEndpoints
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    K.vertices × K.vertices :=
  Classical.choose (exists_edge_endpoint_pair K e)

theorem residualEdgeEndpoints_spec
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    (residualEdgeEndpoints K e).1 ≠ (residualEdgeEndpoints K e).2 ∧
      e.val = {((residualEdgeEndpoints K e).1),
        ((residualEdgeEndpoints K e).2)} :=
  Classical.choose_spec (exists_edge_endpoint_pair K e)

noncomputable def residualEdgePath
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (b : Bool) : C(Set.Icc (0 : ℝ) 1, K.space) := by
  let u := (residualEdgeEndpoints K e).1
  let v := (residualEdgeEndpoints K e).2
  have huv : K.vertexAbstractComplex.edgeGraph.Adj u v := by
    refine ⟨(residualEdgeEndpoints_spec K e).1, ?_⟩
    rw [← residualEdgeEndpoints_spec K e |>.2]
    exact e.property.1
  cases b with
  | false => exact (K.geometricEdgePath huv).toContinuousMap
  | true => exact (K.geometricEdgePath huv).symm.toContinuousMap

theorem residualEdgePath_zero_false
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    residualEdgePath K e false 0 =
      (⟨(residualEdgeEndpoints K e).1,
        K.vertices_subset_space ((residualEdgeEndpoints K e).1).property⟩ : K.space) := by
  simp [residualEdgePath]

theorem residualEdgePath_one_false
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    residualEdgePath K e false 1 =
      (⟨(residualEdgeEndpoints K e).2,
        K.vertices_subset_space ((residualEdgeEndpoints K e).2).property⟩ : K.space) := by
  simp [residualEdgePath]

theorem residualEdgePath_zero_true
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    residualEdgePath K e true 0 =
      (⟨(residualEdgeEndpoints K e).2,
        K.vertices_subset_space ((residualEdgeEndpoints K e).2).property⟩ : K.space) := by
  simp [residualEdgePath]

theorem residualEdgePath_one_true
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    residualEdgePath K e true 1 =
      (⟨(residualEdgeEndpoints K e).1,
        K.vertices_subset_space ((residualEdgeEndpoints K e).1).property⟩ : K.space) := by
  simp [residualEdgePath]

noncomputable def residualBoundarySourcePath
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) (b : Bool) :
    C(Set.Icc (0 : ℝ) 1, K.space) :=
  residualEdgePath K ((Finset.equivFinOfCardEq hL).symm i).val b

theorem residualBoundarySourcePath_opposite_endpoints
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) :
    residualBoundarySourcePath K hL i false 0 =
        residualBoundarySourcePath K hL i true 1 ∧
      residualBoundarySourcePath K hL i false 1 =
        residualBoundarySourcePath K hL i true 0 := by
  exact ⟨(residualEdgePath_zero_false K _).trans
      (residualEdgePath_one_true K _).symm,
    (residualEdgePath_one_false K _).trans
      (residualEdgePath_zero_true K _).symm⟩

theorem residualBoundarySourcePath_sideEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (hL : L.card = 2) (i : Fin 2) (b : Bool) :
    I.sideEdge (residualBoundarySide hL i b) =
      ((Finset.equivFinOfCardEq hL).symm i).val := by
  exact I.sideEdge_residual _ _ rfl

theorem residualBoundarySourcePath_sideEdge_opposite
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (hL : L.card = 2) (i : Fin 2) (b : Bool) :
    I.sideEdge (residualBoundarySide hL i (!b)) =
      I.sideEdge (residualBoundarySide hL i b) := by
  rw [residualBoundarySourcePath_sideEdge I hL i (!b),
    residualBoundarySourcePath_sideEdge I hL i b]

theorem residualBoundarySourcePath_sideEdge_opposite_inventory
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (hL : L.card = 2) (i : Fin 2) (b : Bool) :
    I.sideEdge (I.opposite (residualBoundarySide hL i b)) =
      I.sideEdge (residualBoundarySide hL i b) := by
  exact I.opposite_preserves_original_edge _

end PoincareConjecture.M76
