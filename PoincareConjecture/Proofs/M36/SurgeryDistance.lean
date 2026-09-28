import PoincareConjecture.Proofs.M36.CollapseMetric
import PoincareConjecture.Proofs.M36.PolarContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem surgeryBackground_collapse_bound (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hsmall : N.epsilon < 1 / 200)
    {x : M} (hx : x ∈ N.carrier) (hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀)
    (v : TangentSpace (𝓡 3) x) :
    ((1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center) *
      metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) (surgeryCollapse g₀ N x)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) ≤ g.inner x v v := by
  have hc := (surgeryCollapse_contMDiffAt_before_tip g₀ N hx hs).mdifferentiableAt (by simp)
  have hj := (surgeryBallInclusion_contMDiff g₀ (surgeryOuterRadius g₀ N.epsilon)
    (surgeryCollapse g₀ N x)).mdifferentiableAt (by simp)
  have hi := (neck_inverse_contMDiffAt N hx).mdifferentiableAt (by simp)
  have hp := ((adaptedClippedCollapse_contMDiffOn g₀ (surgeryCapRadius g₀)
    (N.coordinate_inverse x) hs).contMDiffAt
      ((isOpen_lt continuous_snd continuous_const).mem_nhds hs)).mdifferentiableAt (by simp)
  have heq : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) ∘ surgeryCollapse g₀ N
      =ᶠ[nhds x] adaptedClippedCollapse g₀ (surgeryCapRadius g₀) ∘ N.coordinate_inverse := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact surgeryCollapse_inclusion g₀ N hy
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hj hc, mfderiv_comp x hp hi] at hd
  have hdv := congrArg (fun L => L v) hd
  have hpolar := adaptedClippedCollapse_contracts g₀ (surgeryCapRadius g₀)
    (N.coordinate_inverse x) hs (mfderiv (𝓡 3) IC N.coordinate_inverse x v)
  have hbackground : metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _)
      (surgeryCollapse g₀ N x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) ≤
      RoundCylinderMetric (N.coordinate_inverse x)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v) := by
    rw [metricPullbackForm_apply, surgeryCollapse_inclusion g₀ N hx]
    change mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ _) (surgeryCollapse g₀ N x)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) =
      mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀))
        (N.coordinate_inverse x) (mfderiv (𝓡 3) IC N.coordinate_inverse x v) at hdv
    erw [hdv]
    exact hpolar
  have hneck := neck_inverse_cylinder_bound N hx v
  have heta := (neck_contraction_coefficient_pos N hsmall).le
  calc
    _ = ((1 - 6 * N.epsilon) * metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _)
        (surgeryCollapse g₀ N x)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)) /
          N.connection.scalarCurvature N.center := by ring
    _ ≤ ((1 - 6 * N.epsilon) * RoundCylinderMetric (N.coordinate_inverse x)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v)
        (mfderiv (𝓡 3) IC N.coordinate_inverse x v)) /
          N.connection.scalarCurvature N.center :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbackground heta) N.scalar_center_pos.le
    _ ≤ g.inner x v v := (div_le_iff₀ N.scalar_center_pos).mpr (by
      simpa only [mul_comm] using hneck)

theorem surgeryMetric_collapse_bound (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (hsmall : N.epsilon < 1 / 200) {C : ℝ} (hC : 0 ≤ C) (q : ℝ)
    {r : ℝ} (hr : 0 < r) {x : M} (hx : x ∈ N.carrier)
    (hs : (N.coordinate_inverse x).2 < surgeryCapRadius g₀)
    (v : TangentSpace (𝓡 3) x) :
    (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
      (neck_contraction_coefficient_pos N hsmall) hr).inner (surgeryCollapse g₀ N x)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) ≤ g.inner x v v := by
  have hneck : metricPullbackForm g (surgeryRetainedInverse g₀ N) (surgeryCollapse g₀ N x)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v) = g.inner x v v := by
    rw [metricPullbackForm_apply, surgeryRetainedInverse_comp_mfderiv_before_tip g₀ N hcut hx hs,
      surgeryCollapse_left_inverse_before_tip g₀ N hx hs]
  have hbackground := surgeryBackground_collapse_bound g₀ N hsmall hx hs v
  have ha := radialNeckWeight_bounds g₀
    (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) (surgeryCollapse g₀ N x))
  change 0 ≤ surgeryNeckWeight g₀ N (surgeryCollapse g₀ N x) ∧
    surgeryNeckWeight g₀ N (surgeryCollapse g₀ N x) ≤ 1 at ha
  have hm := radialConformalMultiplier_le_one g₀ hC q N.epsilon_pos.le r
    (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) (surgeryCollapse g₀ N x))
  change surgeryConformalMultiplier g₀ N C q r (surgeryCollapse g₀ N x) ≤ 1 at hm
  have hmpos : 0 ≤ surgeryConformalMultiplier g₀ N C q r (surgeryCollapse g₀ N x) :=
    (radialConformalMultiplier_pos g₀ C q N.epsilon r _).le
  rw [surgeryMetric_inner, hneck]
  have hblend' : surgeryNeckWeight g₀ N (surgeryCollapse g₀ N x) * g.inner x v v +
      (1 - surgeryNeckWeight g₀ N (surgeryCollapse g₀ N x)) *
        ((1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center *
          metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) (surgeryCollapse g₀ N x)
            (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)
            (mfderiv (𝓡 3) (𝓡 3) (surgeryCollapse g₀ N) x v)) ≤ g.inner x v v := by
    calc
      _ ≤ surgeryNeckWeight g₀ N (surgeryCollapse g₀ N x) * g.inner x v v +
          (1 - surgeryNeckWeight g₀ N (surgeryCollapse g₀ N x)) * g.inner x v v :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hbackground (sub_nonneg.mpr ha.2))
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hblend' hmpos).trans
    (by simpa using mul_le_mul_of_nonneg_right hm (metric_inner_nonneg g x v))

theorem surgeryMetric_distance_decreasing (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (hsmall : N.epsilon < 1 / 200) {C : ℝ} (hC : 0 ≤ C) (q : ℝ)
    {r : ℝ} (hr : 0 < r) (x y : M) :
    (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
      (neck_contraction_coefficient_pos N hsmall) hr).edist
        (surgeryCollapse g₀ N x) (surgeryCollapse g₀ N y) ≤
      intrinsicEDist g N.carrier x y := by
  apply edist_le_intrinsicEDist_off_tip g _
    (surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N))
    (surgeryCollapse_continuousOn g₀ N)
  · intro z hz htip
    exact surgeryCollapse_contMDiffAt_before_tip g₀ N hz
      ((surgeryCollapse_ne_tip_iff g₀ N hz).mp htip)
  · intro z hz htip v
    exact surgeryMetric_collapse_bound g₀ N hcut hsmall hC q hr hz
      ((surgeryCollapse_ne_tip_iff g₀ N hz).mp htip) v

end PoincareConjecture.M36
