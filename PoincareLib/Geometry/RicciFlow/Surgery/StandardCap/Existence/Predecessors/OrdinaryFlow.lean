import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem GeneralizedRicciGaugeTheory.ordinary_flow {n : ℕ}
    (h : GeneralizedRicciGaugeTheory.{u} n) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (I : SpacetimeInterval) (F : RicciFlow n M I.domain) :
    ∃ R : OrdinaryProductRicciGeometry F.metric I,
      IntrinsicGeneralizedRicciEquation R.leafwiseConnection := by
  obtain ⟨R⟩ := h.ordinary_product M F.metric I F.smooth
  exact ⟨R, (R.equation_iff F.connection).mpr F.equation⟩

end PoincareMT
