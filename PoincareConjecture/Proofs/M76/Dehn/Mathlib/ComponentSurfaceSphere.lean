import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PrimalDualSurfaceSphere
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalEdgeComponent

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E)

theorem exists_edgeComponent_sphere_model
    (hK : K.faces.Finite) (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (T : SimpleGraph (K.edgeComponentComplex C).vertices)
    (hT : T ≤ (K.edgeComponentComplex C).vertexAbstractComplex.edgeGraph)
    (hprimal : T.IsTree)
    (hdual : (complementaryTriangleGraph
      (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex T).IsTree) :
    ∃ H : (K.edgeComponentComplex C).space ≃ₜ frontier (TriangularRoofModel.halfBall 1),
      H.IsFinitePL := by
  classical
  let J := K.edgeComponentComplex C
  have hJ : J.faces.Finite := hK.subset (K.edgeComponentComplex_le C)
  let : Fintype J.faces := hJ.fintype
  apply J.exists_sphere_model_of_primal_complementary_trees _ _ _ T hT hprimal hdual
  · intro s hs
    obtain ⟨t, ht, hst, htc⟩ := K.edgeComponentComplex_pure C hpure s hs
    exact ⟨t, ht, htc, hst⟩
  · intro e he hec
    rw [K.edgeComponentComplex_cofaces C he 3]
    exact hcofaces e (K.edgeComponentComplex_le C he) hec
  · intro p hp
    rw [← J.faceLink_singleton_eq_link, K.edgeComponentComplex_vertex_link C hp]
    exact hlinks p (K.edgeComponentComplex_le C hp)

end Geometry.SimplicialComplex
