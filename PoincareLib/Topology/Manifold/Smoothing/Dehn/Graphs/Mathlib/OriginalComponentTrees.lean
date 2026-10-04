import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.OriginalComponentSurfaceCounts
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Graphs.Mathlib.PrimalDualTrees

/-!
# Actual complementary trees on each whole original component

The literal component restriction retains all cofaces and vertex
links. Its connectedness, restricted exactness and finite incidence
counts construct both trees on their original vertex types.
See Dehn derivation 019 and Putman, pp. 15--16.
-/

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.vertices]

/-- Each whole component of the original complex has an actual
primal tree whose exact complementary triangle graph is a tree.
The component count and connectedness are derived here from the
retained original geometry and incidence. See Dehn derivation 019. -/
theorem edgeComponentComplex_primal_dual_trees
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected)
    (hexact : LinearMap.ker
      (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      LinearMap.range (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) :
    ∃ T : SimpleGraph (K.edgeComponentComplex C).vertices,
      T ≤ (K.edgeComponentComplex C).vertexAbstractComplex.edgeGraph ∧ T.IsTree ∧
      (complementaryTriangleGraph
        (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex T).IsTree :=
  by
    classical
    let J := K.edgeComponentComplex C
    let i := K.subcomplexVertexEmbedding J (K.edgeComponentComplex_le C)
    let : Fintype J.vertices := Fintype.ofInjective i i.injective
    exact J.vertexAbstractComplex.exists_primal_complementary_trees
      (K.edgeComponentComplex_connected C)
      (K.edgeComponentComplex_triangle_cofaces C hcofaces)
      (K.edgeComponentComplex_triangle_connected C hpure hlinks)
      (K.edgeComponentComplex_surface_count C hpure hcofaces hlinks hexact)

end Geometry.SimplicialComplex
