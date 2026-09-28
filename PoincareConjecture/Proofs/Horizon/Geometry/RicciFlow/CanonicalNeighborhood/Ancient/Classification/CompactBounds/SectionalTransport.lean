import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Based
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Transport











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace



theorem normalized_compact_uniform_sectional_lower_any_carrier
    (P : M27KappaAlternativePredecessors.{u})
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 ≤ D) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        IsCompact (univ : Set M) →
        metricDiameter (K.flow.metric 0) univ ≤ D →
        ∀ y : M, ∀ v w : TangentSpace (𝓡 3) y,
          LinearIndependent ℝ ![v, w] →
          c < (K.flow.connection 0).sectionalCurvature y v w := by
  obtain ⟨c, hc, hbound⟩ := normalized_compact_uniform_sectional_lower P hkappa hD
  refine ⟨c, hc, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnoncollapsed hnormalized hcompact hdiam y v w hvw
  let B := K.toSmallBased p hkappa hnoncollapsed hnormalized
  let e := Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M
  have hcompact' : IsCompact (univ : Set B.carrier.carrier) :=
    K.toSmallBased_isCompact p hkappa hnoncollapsed hnormalized hcompact
  have hdiam' : metricDiameter (B.flow.flow.metric 0) univ ≤ D := by
    change metricDiameter (K.flow.shrink.metric 0) univ ≤ D
    rwa [RicciFlow.metricDiameter_shrink]
  have hind : LinearIndependent ℝ
      ![mfderiv (𝓡 3) (𝓡 3) e y v, mfderiv (𝓡 3) (𝓡 3) e y w] := by
    let de := e.mfderivToContinuousLinearEquiv (by simp) y
    convert! hvw.map' de.toLinearMap (LinearMap.ker_eq_bot.mpr de.injective) using 1
    funext i
    fin_cases i <;> rfl
  have h := hbound B hcompact' hdiam' (e y)
    (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w) hind
  have hsec := Homothety.homothety_sectionalCurvature_eq
    (K.flow.metric 0) (B.flow.flow.metric 0) e 1 zero_lt_one
    (K.flow.metricHomothety_shrink 0) (K.flow.connection 0)
    (B.flow.flow.connection 0) y v w
  simpa only [div_one] using h.trans_eq hsec

end PoincareConjecture
