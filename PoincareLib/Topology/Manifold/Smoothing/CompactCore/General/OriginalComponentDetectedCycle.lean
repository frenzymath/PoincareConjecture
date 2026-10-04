import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.OriginalComponentResidualEdges
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Graphs.Mathlib.ResidualCycleEvaluation

/-!
# A detected simple cycle in the actual original frontier component

The complete original surface incidence constructs both trees and every
residual edge. A positive literal residual count selects an original edge,
constructs the paired cycles, and returns a closed cochain whose value on
the actual simple primal cycle is one. No genus, cut or essential loop is
assumed. See Wall019, lines 29--40 and 133--143.
-/

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

/-- Construct a simple original component cycle detected by a closed
cochain whenever the literal original incidence count is positive. -/
theorem exists_edgeComponent_detected_cycle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space) :
    let J := K.edgeComponentComplex C
    let : Fintype J.vertices :=
      (J.finite_vertices_of_finite_faces (hK.subset (K.edgeComponentComplex_le C))).fintype
    let A := J.vertexAbstractComplex.toPreAbstractSimplicialComplex
    Nat.card J.vertices + Nat.card (Triangle A) < Nat.card (Edge A) + 2 →
      ∃ (z : Edge A → ZMod 2) (hz : edgeCoboundary A z = 0)
        (v : J.vertices) (c : J.vertexAbstractComplex.edgeGraph.Walk v v),
        c.IsCycle ∧ (cocycleOfClosed A z hz).walkValue c = 1 := by
  classical
  let J := K.edgeComponentComplex C
  let : Fintype J.vertices :=
    (J.finite_vertices_of_finite_faces (hK.subset (K.edgeComponentComplex_le C))).fintype
  dsimp only
  intro hpositive
  obtain ⟨P, hP, hPtree, D, hD, hDtree, L, hL, _, hcount⟩ :=
    K.exists_edgeComponent_trees_with_residual_edges hK C hpure hcofaces hlinks
  have hLpos : 0 < L.card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hLpos
  obtain ⟨s, _, hs⟩ := (hL e).mp he
  exact J.vertexAbstractComplex.exists_detected_cycle_of_residual_edge
    (K.edgeComponentComplex_triangle_cofaces C hcofaces)
    P hP hPtree.connected D hD hDtree.connected s hs

end Geometry.SimplicialComplex
