import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Small
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.ScalarDerivatives

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

local instance smallSecondCountable : SecondCountableTopology (Shrink.{0} M) :=
  (Poincare.Topology.SecondCountable.homeomorphShrink M).symm.isEmbedding.secondCountableTopology

local instance smallConnectedSpace : ConnectedSpace (Shrink.{0} M) :=
  (Poincare.Topology.SecondCountable.homeomorphShrink M).connectedSpace_iff.mp inferInstance

omit [T2Space M] [ConnectedSpace M] in
theorem ancientKappaNoncollapsed_shrink (F : RicciFlow n M (Iic 0))
    {κ : ℝ} (hκ : AncientKappaNoncollapsed F κ) :
    AncientKappaNoncollapsed F.shrink κ := by
  intro r₀ hr₀ t ht p r hr hrr₀ hbound
  rw [calibratedMetricVolume_eq_volumeMeasure, F.shrink_volumeMeasure_ball,
    ← calibratedMetricVolume_eq_volumeMeasure]
  apply hκ r₀ hr₀ t ht ((equivShrink M).symm p) r hr hrr₀
  intro s hs q hq
  have hmem : equivShrink M q ∈ (F.shrink.metric t).ball p r := by
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, F.shrink_edist,
      Equiv.symm_apply_apply] using hq
  simpa only [F.shrink_curvatureTensorNorm, Equiv.symm_apply_apply] using
    hbound s hs (equivShrink M q) hmem



noncomputable def smallAncientKappaSolution (K : AncientKappaSolution n M)
    (κ : ℝ) (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed K.flow κ) :
    AncientKappaSolution n (Shrink.{0} M) where
  flow := K.flow.shrink
  kappa := κ
  kappa_pos := hκ
  complete := fun t ht => (K.flow.shrink_metricComplete_iff t).2 (K.complete t ht)
  nonnegative_curvature_operator := fun t ht x =>
    (K.flow.shrink_nonnegativeCurvatureOperator_iff t x).2
      (K.nonnegative_curvature_operator t ht _)
  bounded_curvature := by
    intro t ht
    obtain ⟨C, hC, hbound⟩ := K.bounded_curvature t ht
    refine ⟨C, hC, fun x => ?_⟩
    simpa only [K.flow.shrink_curvatureTensorNorm] using hbound ((equivShrink M).symm x)
  nonflat := by
    intro t ht
    obtain ⟨x, hx⟩ := K.nonflat t ht
    exact ⟨equivShrink M x, by simpa using hx⟩
  noncollapsed := ancientKappaNoncollapsed_shrink K.flow hnc


noncomputable abbrev smallKappaCarrier : FlowCarrier.{0} n where
  carrier := Shrink.{0} M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance
  connected := isConnected_univ

variable {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  [MeasurableSpace N] [BorelSpace N] [T2Space N] [T3Space N]
  [SecondCountableTopology N] [ConnectedSpace N]



noncomputable abbrev smallBasedKappaSolution (K : AncientKappaSolution 3 N)
    (x : N) (κ : ℝ) (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed K.flow κ)
    (hR : (K.flow.connection 0).scalarCurvature x = 1) : BasedKappaSolution κ where
  carrier := smallKappaCarrier (M := N)
  connectedSpace := smallConnectedSpace
  flow := smallAncientKappaSolution K κ hκ hnc
  base := equivShrink N x
  kappa_eq := rfl
  scalar_normalized := by
    change (K.flow.shrink.connection 0).scalarCurvature (equivShrink N x) = 1
    rw [K.flow.shrink_scalarCurvature, Equiv.symm_apply_apply]
    exact hR

@[simp] theorem smallBasedKappaSolution_scalarCurvature (K : AncientKappaSolution 3 N)
    (x : N) (κ : ℝ) (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed K.flow κ)
    (hR : (K.flow.connection 0).scalarCurvature x = 1) (t : ℝ) (y : Shrink.{0} N) :
    ((smallBasedKappaSolution K x κ hκ hnc hR).flow.flow.connection t).scalarCurvature y =
      (K.flow.connection t).scalarCurvature ((equivShrink N).symm y) :=
  K.flow.shrink_scalarCurvature t y

@[simp] theorem smallBasedKappaSolution_curvatureTensorNorm (K : AncientKappaSolution 3 N)
    (x : N) (κ : ℝ) (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed K.flow κ)
    (hR : (K.flow.connection 0).scalarCurvature x = 1) (t : ℝ) (y : Shrink.{0} N) :
    ((smallBasedKappaSolution K x κ hκ hnc hR).flow.flow.connection t).curvatureTensorNorm y =
      (K.flow.connection t).curvatureTensorNorm ((equivShrink N).symm y) :=
  K.flow.shrink_curvatureTensorNorm t y

@[simp] theorem smallBasedKappaSolution_curvatureDerivativeNorm
    (K : AncientKappaSolution 3 N) (x : N) (κ : ℝ) (hκ : 0 < κ)
    (hnc : AncientKappaNoncollapsed K.flow κ)
    (hR : (K.flow.connection 0).scalarCurvature x = 1)
    (t : ℝ) (k : ℕ) (y : Shrink.{0} N) :
    ((smallBasedKappaSolution K x κ hκ hnc hR).flow.flow.connection t).curvatureDerivativeNorm
        k y = (K.flow.connection t).curvatureDerivativeNorm k ((equivShrink N).symm y) :=
  K.flow.pullbackDiffeomorph_curvatureDerivativeNorm _ t k y

@[simp] theorem smallBasedKappaSolution_edist (K : AncientKappaSolution 3 N)
    (x : N) (κ : ℝ) (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed K.flow κ)
    (hR : (K.flow.connection 0).scalarCurvature x = 1)
    (t : ℝ) (y z : Shrink.{0} N) :
    ((smallBasedKappaSolution K x κ hκ hnc hR).flow.flow.metric t).edist y z =
      (K.flow.metric t).edist ((equivShrink N).symm y) ((equivShrink N).symm z) :=
  K.flow.shrink_edist t y z

theorem smallBasedKappaSolution_mem_ball (K : AncientKappaSolution 3 N)
    (x : N) (κ : ℝ) (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed K.flow κ)
    (hR : (K.flow.connection 0).scalarCurvature x = 1) (t r : ℝ) (y : N) :
    equivShrink N y ∈
        ((smallBasedKappaSolution K x κ hκ hnc hR).flow.flow.metric t).ball
          (smallBasedKappaSolution K x κ hκ hnc hR).base r ↔
      y ∈ (K.flow.metric t).ball x r := by
  change (K.flow.shrink.metric t).edist (equivShrink N x) (equivShrink N y) < _ ↔ _
  rw [K.flow.shrink_edist, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

end PoincareConjecture.ScalarDerivatives
