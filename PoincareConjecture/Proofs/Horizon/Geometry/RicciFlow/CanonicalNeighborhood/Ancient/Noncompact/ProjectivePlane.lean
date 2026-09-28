import PoincareConjecture.Definitions.M27ProductModels

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem NoEmbeddedTrivialNormalProjectivePlane.not_product_homeomorph
    (h : NoEmbeddedTrivialNormalProjectivePlane K)
    (e : M ≃ₜ (RealProjectiveTwo × ℝ)) : False := by
  apply h
  refine ⟨fun p => e.symm (p.1, p.2.val), ?_⟩
  exact e.symm.isOpenEmbedding.comp
    (Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)

theorem NoEmbeddedTrivialNormalProjectivePlane.not_projectivePlaneLine
    (h : NoEmbeddedTrivialNormalProjectivePlane K) :
    ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) := by
  rintro ⟨model⟩
  exact h.not_product_homeomorph model.product_homeomorph

end PoincareConjecture
