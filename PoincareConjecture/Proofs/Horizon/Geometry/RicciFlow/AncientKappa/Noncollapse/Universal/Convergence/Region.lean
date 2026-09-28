import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Convergence.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.ScalarSpacetime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Measure.Monotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds







set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem AncientCompactTimeConvergence.eventually_model_scalar_lt
    (G : AncientCompactTimeConvergence S)
    (hscalar : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection (-1)).scalarCurvature x < 2) :
    ∀ᶠ k in atTop, ∀ x ∈ ((S.rescaling (G.subsequence k)).flow.metric (-1)).ball
      (S.base (G.subsequence k)) 1,
      ((S.rescaling (G.subsequence k)).flow.connection (-1)).scalarCurvature x < 2 := by
  let A := closure ((G.limit.flow.metric (-1)).ball G.limit.base 2)
  have hA : IsCompact A := (G.limit.flow.metric (-1)).isCompact_closure_ball_of_metricComplete
    (G.limit.complete (-1) (by norm_num)) G.limit.base 2
  have hcompact : IsCompact ({(-1 : ℝ)} ×ˢ A) := isCompact_singleton.prod hA
  have hscalar' := G.eventually_scalarCurvature_lt_on_compact (B := 2)
    hcompact (fun p hp ↦ by rw [show p.1 = -1 from hp.1]; norm_num)
    (fun p hp ↦ by rw [show p.1 = -1 from hp.1]; exact hscalar p.2)
  filter_upwards [G.eventually_source_ball_subset_image_ball (t := -1) (r := 1)
    (C := 2) (by norm_num) G.limit.base (by norm_num) (by norm_num), hscalar']
    with k hcover hk x hx
  have hbase : ((G.embedding k).toFun (-1, G.limit.base)).2 = S.base (G.subsequence k) :=
    congrArg Prod.snd (G.base_preserving k)
  rw [hbase] at hcover
  obtain ⟨y, hy, rfl⟩ := hcover hx
  exact hk (-1, y) ⟨rfl, subset_closure (by simpa using hy)⟩

namespace AncientRescaling

variable {τ : ℝ} (R : AncientRescaling K τ)

theorem volumeMeasure_antitone_of_tensor_calculus
    (hTensor : ∀ t ≤ 0, (K.flow.connection t).CurvatureTensorCalculus)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 0) {A : Set M} (hA : MeasurableSet A) :
    (R.flow.metric t).volumeMeasure A ≤ (R.flow.metric s).volumeMeasure A := by
  apply R.flow.volumeMeasure_antitone_of_nonnegative_ricci (convex_Iio 0)
    (fun t ht x v ↦ ?_) (hst.trans_lt ht) ht hst hA
  rw [R.ricci_scale t ht]
  have htt : τ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos R.tau_pos.le ht.le
  exact ((K.flow.connection (τ * t)).ricci_bounds_of_nonnegative_curvatureOperator
    (hTensor (τ * t) htt) x (K.nonnegative_curvature_operator (τ * t) htt x) v).1

end AncientRescaling

theorem AncientCompactTimeConvergence.eventually_model_region_volume_lower
    (G : AncientCompactTimeConvergence S)
    (hTensor : ∀ t ≤ 0, (K.flow.connection t).CurvatureTensorCalculus)
    (hvol : ENNReal.ofReal universalNoncollapseModelVolume ≤
      (G.limit.flow.metric (-1)).volumeMeasure
        ((G.limit.flow.metric (-1)).ball G.limit.base (1 / 4))) :
    ∀ᶠ k in atTop, ∀ t ≤ -1, ENNReal.ofReal universalNoncollapseVolume ≤
      ((S.rescaling (G.subsequence k)).flow.metric t).volumeMeasure
        (((S.rescaling (G.subsequence k)).flow.metric (-1)).ball
          (S.base (G.subsequence k)) (1 / 2)) := by
  filter_upwards [G.eventually_model_ball_volume_lower hvol] with k hk t ht
  apply hk.trans
  apply (S.rescaling (G.subsequence k)).volumeMeasure_antitone_of_tensor_calculus
    hTensor ht (by norm_num)
  let g := (S.rescaling (G.subsequence k)).flow.metric (-1)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  change MeasurableSet {x | edist (S.base (G.subsequence k)) x < ENNReal.ofReal (1 / 2)}
  exact (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet

end PoincareConjecture
