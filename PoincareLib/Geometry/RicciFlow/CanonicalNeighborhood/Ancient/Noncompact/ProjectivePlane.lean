import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Products

/-!
# Excluding the projective-plane product

Restrict the line coordinate of a projective-plane product to the open unit
interval and transport the resulting open embedding to the solution carrier.
This discharges the exceptional product branch using the exact topological
hypothesis of Morgan--Tian Corollary 9.88, pp. 239--240.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

/-- A projective-plane product contains the forbidden two-sided plane. -/
theorem NoEmbeddedTrivialNormalProjectivePlane.not_product_homeomorph
    (h : NoEmbeddedTrivialNormalProjectivePlane K)
    (e : M ≃ₜ (RealProjectiveTwo × ℝ)) : False := by
  apply h
  refine ⟨fun p => e.symm (p.1, p.2.val), ?_⟩
  exact e.symm.isOpenEmbedding.comp
    (Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)

/-- The exceptional flow-model certificate contradicts the Corollary 9.88
hypothesis on this same carrier. -/
theorem NoEmbeddedTrivialNormalProjectivePlane.not_projectivePlaneLine
    (h : NoEmbeddedTrivialNormalProjectivePlane K) :
    ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) := by
  rintro ⟨model⟩
  exact h.not_product_homeomorph model.product_homeomorph

end PoincareMT
