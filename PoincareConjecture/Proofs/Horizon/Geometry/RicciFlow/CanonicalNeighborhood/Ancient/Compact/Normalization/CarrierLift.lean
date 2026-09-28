import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe v u

namespace PoincareConjecture

attribute [local instance] RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

omit [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] in

theorem ancientKappaNoncollapsed_ulift (F : RicciFlow n M (Iic 0))
    {kappa : ℝ} (hkappa : AncientKappaNoncollapsed F kappa) :
    AncientKappaNoncollapsed (F.ulift : RicciFlow n (ULift.{v} M) (Iic 0)) kappa := by
  intro r₀ hr₀ t ht p r hr hrr₀ hbound
  rw [calibratedMetricVolume_eq_volumeMeasure, F.ulift_volumeMeasure_ball,
    ← calibratedMetricVolume_eq_volumeMeasure]
  apply hkappa r₀ hr₀ t ht p.down r hr hrr₀
  intro s hs q hq
  have hmem : ULift.up.{v} q ∈ (F.ulift.metric t).ball p r := by
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, F.ulift_edist] using hq
  simpa only [F.ulift_curvatureTensorNorm] using hbound s hs (ULift.up.{v} q) hmem

namespace AncientKappaSolution

local instance uliftSecondCountable : SecondCountableTopology (ULift.{v} M) :=
  (Homeomorph.ulift : ULift.{v} M ≃ₜ M).isEmbedding.secondCountableTopology

local instance uliftConnectedSpace : ConnectedSpace (ULift.{v} M) :=
  (Homeomorph.ulift : ULift.{v} M ≃ₜ M).connectedSpace_iff.mpr inferInstance

noncomputable def ulift (K : AncientKappaSolution n M) :
    AncientKappaSolution n (ULift.{v} M) where
  flow := K.flow.ulift
  kappa := K.kappa
  kappa_pos := K.kappa_pos
  complete := fun t ht => (K.flow.ulift_metricComplete_iff t).2 (K.complete t ht)
  nonnegative_curvature_operator := fun t ht x =>
    (K.flow.ulift_nonnegativeCurvatureOperator_iff t x).2
      (K.nonnegative_curvature_operator t ht x.down)
  bounded_curvature := by
    intro t ht
    obtain ⟨C, hC, hbound⟩ := K.bounded_curvature t ht
    refine ⟨C, hC, fun x => ?_⟩
    simpa only [K.flow.ulift_curvatureTensorNorm] using hbound x.down
  nonflat := by
    intro t ht
    obtain ⟨x, hx⟩ := K.nonflat t ht
    exact ⟨ULift.up x, by simpa only [K.flow.ulift_curvatureTensorNorm] using hx⟩
  noncollapsed := ancientKappaNoncollapsed_ulift K.flow K.noncollapsed

@[simp] theorem ulift_flow (K : AncientKappaSolution n M) :
    (K.ulift : AncientKappaSolution n (ULift.{v} M)).flow = K.flow.ulift := rfl

@[simp] theorem ulift_kappa (K : AncientKappaSolution n M) :
    (K.ulift : AncientKappaSolution n (ULift.{v} M)).kappa = K.kappa := rfl

@[simp] theorem ulift_scalarCurvature (K : AncientKappaSolution n M)
    (t : ℝ) (x : ULift.{v} M) :
    (K.ulift.flow.connection t).scalarCurvature x =
      (K.flow.connection t).scalarCurvature x.down :=
  K.flow.ulift_scalarCurvature t x

@[simp] theorem ulift_curvatureTensorNorm (K : AncientKappaSolution n M)
    (t : ℝ) (x : ULift.{v} M) :
    (K.ulift.flow.connection t).curvatureTensorNorm x =
      (K.flow.connection t).curvatureTensorNorm x.down :=
  K.flow.ulift_curvatureTensorNorm t x

@[simp] theorem ulift_curvatureDerivativeNorm (K : AncientKappaSolution n M)
    (t : ℝ) (j : ℕ) (x : ULift.{v} M) :
    (K.ulift.flow.connection t).curvatureDerivativeNorm j x =
      (K.flow.connection t).curvatureDerivativeNorm j x.down :=
  K.flow.ulift_curvatureDerivativeNorm t j x

@[simp] theorem ulift_edist (K : AncientKappaSolution n M)
    (t : ℝ) (x y : ULift.{v} M) :
    (K.ulift.flow.metric t).edist x y = (K.flow.metric t).edist x.down y.down :=
  K.flow.ulift_edist t x y

@[simp] theorem ulift_calibratedMetricVolume_ball (K : AncientKappaSolution n M)
    (t : ℝ) (x : ULift.{v} M) (r : ℝ) :
    calibratedMetricVolume (K.ulift.flow.metric t) ((K.ulift.flow.metric t).ball x r) =
      calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball x.down r) := by
  rw [calibratedMetricVolume_eq_volumeMeasure, calibratedMetricVolume_eq_volumeMeasure]
  exact K.flow.ulift_volumeMeasure_ball t x r

end AncientKappaSolution
end PoincareConjecture
