import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Definitions.Ch09.AsymptoticVolume
import PoincareConjecture.Statements.Ch04.Continuation
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Statements.M15Noncollapsing
import PoincareConjecture.Statements.M27KappaAlternatives
import PoincareConjecture.Statements.M30ControlledBlowupLimits

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

structure M34StandardCapPredecessors : Prop where
  local_flow :
    ∀ (n : ℕ) (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      RicciFlowLocalTheory n M
  curvature : RicciFlowCurvatureTheory.{0}
  pointed_compactness :
    ∀ {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T),
      Nonempty (PointedRicciFlowCompactnessConclusion H)
  ordinary_windows : M14OrdinaryProviders.{0} 3
  ordinary_product :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [Nonempty M]
      (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain),
      ∃ R : OrdinaryProductRicciGeometry F.metric I,
        IntrinsicGeneralizedRicciEquation R.leafwiseConnection
  ordinary_rescaling :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M]
      (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain)
      (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
      Nonempty (OrdinaryParabolicRescaling F Q hQ a)
  metric_homothety :
    ∀ (M N : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
      [T3Space M] [MeasurableSpace M] [BorelSpace M]
      [T3Space N] [MeasurableSpace N] [BorelSpace N]
      (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
      (f : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Q : ℝ), 0 < Q →
      MetricHomothety g h f Q → MetricHomothetyCalculus g h f Q
  exponential :
    ∀ (X : Type) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport 3 X time I),
      Nonempty (M14ExponentialConclusion G)
  ordinary_capture :
    ∀ (X : Type) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport 3 X time I)
      (O : M14OrdinaryProviders.{0} 3),
      M14OrdinaryCaptureStatement G O
  noncollapse_generalized : M15GeneralizedUniformTheorem.{0} 3
  zero_avr :
    ∀ {M : Type} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M), AncientAsymptoticVolumeRatioZero K
  kappa_alternatives : RepairedKappaAlternativeTheory.{0}
  long_limits : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
    M30LongLimitStatement.{0} epsilon₀

structure RepairedStandardCapExistenceTheory : Prop where
  initial_metric : Nonempty StandardInitialMetric
  existence : ∀ g₀ : StandardInitialMetric,
    Nonempty (RepairedStandardCapExistenceData g₀)

end PoincareConjecture
