import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Proofs.M11
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Calculus
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Assembly











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture








theorem m12MetricPredecessors (n : ℕ) : M12MetricPredecessors.{u} n where
  connection_exists _ _ _ _ _ _ g := normalization_exists_leviCivitaData g
  connection_regular _ _ _ _ _g D _ hU Y hY :=
    D.normalization_contMDiffOn_connection hU Y hY
  curvature_calculus _ _ _ _ _g D := D.normalization_curvatureTensorCalculus




























theorem generalizedRicciGaugeGeometry (n : ℕ)
    (hGeometry : GeneralizedSpacetimeGeometryTheory.{u} n)
    (hMetric : M12MetricPredecessors.{u} n)
    (hCoordinates : M12MetricPredecessors.{0} n) :
    GeneralizedRicciGaugeTheory.{u} n := by
  exact generalizedRicciGaugeGeometry_proof n hGeometry hMetric hCoordinates








theorem generalizedRicciGaugeGeometry_from_M03_M04_M11 (n : ℕ) :
    GeneralizedRicciGaugeTheory.{u} n :=
  generalizedRicciGaugeGeometry n (generalizedSpacetimeGeometry n)
    (m12MetricPredecessors.{u} n) (m12MetricPredecessors.{0} n)






theorem GeneralizedRicciGaugeTheory.ordinary_flow {n : ℕ}
    (h : GeneralizedRicciGaugeTheory.{u} n) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (I : SpacetimeInterval) (F : RicciFlow n M I.domain) :
    ∃ R : OrdinaryProductRicciGeometry F.metric I,
      IntrinsicGeneralizedRicciEquation R.leafwiseConnection := by
  obtain ⟨R⟩ := h.ordinary_product M F.metric I F.smooth
  exact ⟨R, (R.equation_iff F.connection).mpr F.equation⟩

end PoincareConjecture
