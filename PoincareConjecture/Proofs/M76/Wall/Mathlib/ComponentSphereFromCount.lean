import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComponentSurfaceSphere
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalComponentSurfaceCounts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PrimalDualTrees
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLCubeSphereModel

set_option autoImplicit false

open Set Geometry TriangularRoofModel PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

theorem exists_edgeComponent_cube_sphere_of_count
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hcount : Nat.card (K.edgeComponentComplex C).vertices +
      Nat.card (Triangle
        (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      Nat.card (Edge
        (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    ∃ b : (K.edgeComponentComplex C).space ≃ₜ Metric.sphere (0 : Fin 3 → ℝ) 1,
      b.IsFinitePL := by
  classical
  let J := K.edgeComponentComplex C
  have hJ : J.faces.Finite := hK.subset (K.edgeComponentComplex_le C)
  let : Fintype J.vertices := (J.finite_vertices_of_finite_faces hJ).fintype
  have hlinkgraphs : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected := by
    intro p hp
    exact ((K.faceLink {p}).connected_edgeGraph_of_isConnected
      (SimplicialComplex.finite_faceLink_faces hK _) (hlinks p hp)).preconnected
  obtain ⟨T, hT, hprimal, hdual⟩ :=
    J.vertexAbstractComplex.exists_primal_complementary_trees
      (K.edgeComponentComplex_connected C)
      (K.edgeComponentComplex_triangle_cofaces C hcofaces)
      (K.edgeComponentComplex_triangle_connected C hpure hlinkgraphs) hcount
  obtain ⟨H, hH⟩ :=
    K.exists_edgeComponent_sphere_model hK C hpure hcofaces hlinks T hT hprimal hdual
  have hcv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  exact hH.exists_unit_cube_sphere_model (isCompact_halfBall (Or.inl rfl)) hcv
    (interior_halfBall_nonempty (h := 1) (Or.inl rfl)) hdim

end Geometry.SimplicialComplex
