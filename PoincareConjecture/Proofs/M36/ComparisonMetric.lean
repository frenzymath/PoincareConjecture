import PoincareConjecture.Proofs.M36.ComparisonPullback
import PoincareConjecture.Proofs.M36.ComparisonNeckJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem surgeryRetainedInverse_chart (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {p : StandardCapSpace}
    (hp : p ∈ Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ N.epsilon))) :
    surgeryRetainedInverse g₀ N (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) p) =
      comparisonNeckLift g₀ N p := by
  unfold surgeryRetainedInverse
  rw [surgeryBallChart_right_inverse g₀ _ hp]
  rfl

theorem surgeryRetainedInverse_chart_mfderiv (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    {p : StandardCapSpace}
    (hp : p ∈ Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ N.epsilon)))
    (hp0 : p ≠ 0) (v : StandardCapSpace) :
    mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N)
      (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) p)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon)) p v) =
        mfderiv (𝓡 3) (𝓡 3) (comparisonNeckLift g₀ N) p v := by
  have hc := ((surgeryBallChart_contMDiffOn g₀ _ _ hp).contMDiffAt
    (Metric.isOpen_ball.mem_nhds hp)).mdifferentiableAt (by simp)
  have hi := (surgeryRetainedInverse_contMDiffAt g₀ N hcut (by
    rw [surgeryBallChart_right_inverse g₀ _ hp]
    exact hp0)).mdifferentiableAt (by simp)
  have heq : surgeryRetainedInverse g₀ N ∘
      surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) =ᶠ[nhds p]
        comparisonNeckLift g₀ N := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with x hx
    exact surgeryRetainedInverse_chart g₀ N hx
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp p hi hc] at hd
  exact congrArg (fun A => A v) hd

theorem surgeryMetric_chart_coefficients (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (C q eta r : ℝ) (heta : 0 < eta) (hr : 0 < r)
    {p : StandardCapSpace}
    (hp : p ∈ Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ N.epsilon))) :
    N.connection.scalarCurvature N.center •
        (surgeryMetric g₀ N hcut C q eta r N.scalar_center_pos heta hr).pullbackCoefficients
          (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon)) p =
      radialConformalMultiplier g₀ C q N.epsilon r p •
        (radialNeckWeight g₀ p • (normalizedNeckMetric N).pullbackCoefficients
            (comparisonNeckLift g₀ N) p +
          (1 - radialNeckWeight g₀ p) • (eta • g₀.metric.euclideanCoefficients p)) := by
  let e := surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon)
  have hmu : surgeryConformalMultiplier g₀ N C q r (e p) =
      radialConformalMultiplier g₀ C q N.epsilon r p := by
    unfold surgeryConformalMultiplier e
    rw [Function.comp_apply, surgeryBallChart_right_inverse g₀ _ hp]
  have ha : surgeryNeckWeight g₀ N (e p) = radialNeckWeight g₀ p := by
    unfold surgeryNeckWeight e
    rw [Function.comp_apply, surgeryBallChart_right_inverse g₀ _ hp]
  have hbg (v w : StandardCapSpace) :
      metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) (e p)
        (mfderiv (𝓡 3) (𝓡 3) e p v) (mfderiv (𝓡 3) (𝓡 3) e p w) =
          g₀.metric.euclideanCoefficients p v w := by
    rw [metricPullbackForm_apply, surgeryBallChart_inclusion_mfderiv g₀ _ hp,
      surgeryBallChart_inclusion_mfderiv g₀ _ hp]
    erw [surgeryBallChart_right_inverse g₀ _ hp]
    rfl
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change N.connection.scalarCurvature N.center *
    (surgeryMetric g₀ N hcut C q eta r N.scalar_center_pos heta hr).inner (e p)
      (mfderiv (𝓡 3) (𝓡 3) e p v) (mfderiv (𝓡 3) (𝓡 3) e p w) = _
  rw [surgeryMetric_inner, hmu, ha, hbg]
  simp only [smul_apply, add_apply, smul_eq_mul]
  by_cases hzero : radialNeckWeight g₀ p = 0
  · rw [hzero]
    simp only [zero_mul, sub_zero, one_mul, zero_add]
    field_simp [N.scalar_center_pos.ne']
  · have hp0 : p ≠ 0 := by
      intro hp0
      subst p
      exact hzero (radialNeckWeight_eventually_zero g₀).self_of_nhds
    have hneck : metricPullbackForm g (surgeryRetainedInverse g₀ N) (e p)
        (mfderiv (𝓡 3) (𝓡 3) e p v) (mfderiv (𝓡 3) (𝓡 3) e p w) =
          g.pullbackCoefficients (comparisonNeckLift g₀ N) p v w := by
      rw [metricPullbackForm_apply, surgeryRetainedInverse_chart_mfderiv g₀ N hcut hp hp0,
        surgeryRetainedInverse_chart_mfderiv g₀ N hcut hp hp0]
      erw [surgeryRetainedInverse_chart g₀ N hp]
      rfl
    have hnorm : (normalizedNeckMetric N).pullbackCoefficients
        (comparisonNeckLift g₀ N) p v w =
        N.connection.scalarCurvature N.center *
          g.pullbackCoefficients (comparisonNeckLift g₀ N) p v w := by
      exact m01RescaledMetric_inner g _ N.scalar_center_pos (comparisonNeckLift g₀ N p)
        (mfderiv (𝓡 3) (𝓡 3) (comparisonNeckLift g₀ N) p v)
        (mfderiv (𝓡 3) (𝓡 3) (comparisonNeckLift g₀ N) p w)
    rw [hneck, hnorm]
    field_simp [N.scalar_center_pos.ne']

theorem surgeryMetric_chart_error (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (C q r : ℝ) (heta : 0 < 1 - 6 * N.epsilon) (hr : 0 < r)
    {p : StandardCapSpace}
    (hp : p ∈ Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ N.epsilon))) :
    N.connection.scalarCurvature N.center •
        (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r
          N.scalar_center_pos heta hr).pullbackCoefficients
          (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon)) p -
        g₀.metric.euclideanCoefficients p =
      (radialConformalMultiplier g₀ C q N.epsilon r p * radialNeckWeight g₀ p) •
        ((normalizedNeckMetric N).pullbackCoefficients (comparisonNeckLift g₀ N) p -
          g₀.metric.euclideanCoefficients p) + standardScalarError g₀ C q r N.epsilon p := by
  rw [surgeryMetric_chart_coefficients g₀ N hcut C q (1 - 6 * N.epsilon) r heta hr hp]
  unfold standardScalarError
  module

end PoincareConjecture.M36
