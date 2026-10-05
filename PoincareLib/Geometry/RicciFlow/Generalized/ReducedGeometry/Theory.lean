import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Rescaling

/-! Adapted from Mapher `PoincareMT/Statements/M14GeneralizedLGeometry.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

set_option autoImplicit false

open scoped Manifold ContMDiff ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

structure GeneralizedLGeometryConclusion
    (G : GeneralizedLGeometryTransport n X time I) : Prop where
  path_calculus : M14PathCalculusConclusion G
  exponential : M14ExponentialConclusion G
  finite_value : M14FiniteValueStatement G
  attainment : M14AttainmentStatement G
  regular_formulas : M14RegularFormulaStatement G
  positive_start_correction : M14PositiveStartCorrectionStatement G
  measure_transport : M14MeasureTransportStatement G
  reduced_volume : M14ReducedVolumeStatement G
  local_lipschitz : M14LocalLipschitzStatement G
  small_time_coverage : M14SmallTimeCoverageStatement G
  reduced_volume_analytic : ∀ (T τ : ℝ) (x : G.Point),
    ∀ (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E),
      Nonempty (M14ReducedVolumeAnalyticData G T τ x E H)
  reduced_volume_source : Nonempty (M14ReducedVolumeSourceCoverageData G)
  analytic_rescaling : M14AnalyticRescalingConclusion G
  ordinary_capture : ∀ O : M14OrdinaryProviders.{u} n, M14OrdinaryCaptureStatement G O

structure GeneralizedLGeometryTheory (n : ℕ) : Prop where
  conclusion : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport n X time I),
    Nonempty (GeneralizedLGeometryConclusion G)

end PoincareMT
