import PoincareConjecture.Proofs.M36.SurgeryBalls
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M36

noncomputable def dilatedSurgeryBallChart (g₀ : StandardInitialMetric) (L a : ℝ)
    [Nonempty (SurgeryBall.{u} g₀ L)] : StandardCapSpace → SurgeryBall.{u} g₀ L :=
  fun p => surgeryBallChart g₀ L (a • p)

noncomputable def dilatedSurgeryBallInverse (g₀ : StandardInitialMetric) (L a : ℝ) :
    SurgeryBall.{u} g₀ L → StandardCapSpace :=
  fun y => a⁻¹ • surgeryBallInclusion g₀ L y

theorem dilation_mem_surgeryBall (g₀ : StandardInitialMetric)
    {L a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L)
    {p : StandardCapSpace} (hp : p ∈ g₀.metric.ball 0 R) :
    a • p ∈ Metric.ball 0 (radialEuclideanRadius g₀ L) := by
  rw [standard_ball_eq_euclidean g₀ hR, Metric.mem_ball, dist_zero_right] at hp
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  exact (mul_lt_mul_of_pos_left hp ha).trans_le hfit

theorem dilatedSurgeryBallChart_inclusion (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)] (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L)
    {p : StandardCapSpace} (hp : p ∈ g₀.metric.ball 0 R) :
    surgeryBallInclusion g₀ L (dilatedSurgeryBallChart g₀ L a p) = a • p :=
  surgeryBallChart_right_inverse g₀ L (dilation_mem_surgeryBall g₀ ha hR hfit hp)

theorem dilatedSurgeryBallChart_left_inverse (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)] (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L) :
    Set.LeftInvOn (dilatedSurgeryBallInverse g₀ L a) (dilatedSurgeryBallChart g₀ L a)
      (g₀.metric.ball 0 R) := by
  intro p hp
  change a⁻¹ • surgeryBallInclusion g₀ L (dilatedSurgeryBallChart g₀ L a p) = p
  rw [dilatedSurgeryBallChart_inclusion g₀ ha hR hfit hp,
    smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

theorem dilatedSurgeryBallChart_right_inverse (g₀ : StandardInitialMetric)
    {L a : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)] (ha : 0 < a)
    (y : SurgeryBall.{u} g₀ L) :
    dilatedSurgeryBallChart g₀ L a (dilatedSurgeryBallInverse g₀ L a y) = y := by
  unfold dilatedSurgeryBallChart dilatedSurgeryBallInverse
  rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  exact surgeryBallChart_left_inverse g₀ L y

theorem dilatedSurgeryBallChart_zero (g₀ : StandardInitialMetric)
    {L : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)] (hL : 0 < L) (a : ℝ) :
    dilatedSurgeryBallChart g₀ L a 0 = surgeryBallTip g₀ hL := by
  rw [dilatedSurgeryBallChart, smul_zero, surgeryBallChart_zero g₀ hL]

theorem dilatedSurgeryBallChart_contMDiffOn (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)] (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (dilatedSurgeryBallChart g₀ L a)
      (g₀.metric.ball 0 R) := by
  have hd : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p : StandardCapSpace => a • p) :=
    (contDiff_id.const_smul a).contMDiff
  exact (surgeryBallChart_contMDiffOn g₀ L).comp hd.contMDiffOn
    (fun _ hp => dilation_mem_surgeryBall g₀ ha hR hfit hp)

theorem dilatedSurgeryBallInverse_contMDiff (g₀ : StandardInitialMetric)
    (L a : ℝ) [Nonempty (SurgeryBall.{u} g₀ L)] :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (dilatedSurgeryBallInverse g₀ L a) := by
  change ContMDiff (𝓡 3) (𝓡 3) ∞
    (fun y : SurgeryBall.{u} g₀ L => a⁻¹ • surgeryBallInclusion g₀ L y)
  exact ((contDiff_id.const_smul a⁻¹).contMDiff).comp
    (surgeryBallInclusion_contMDiff g₀ L)

theorem dilatedSurgeryBallChart_image (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)] (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L) :
    dilatedSurgeryBallChart g₀ L a '' g₀.metric.ball 0 R =
      {y | ‖surgeryBallInclusion g₀ L y‖ < a * radialEuclideanRadius g₀ R} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    change ‖surgeryBallInclusion g₀ L (dilatedSurgeryBallChart g₀ L a p)‖ < _
    rw [dilatedSurgeryBallChart_inclusion g₀ ha hR hfit hp,
      norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    apply mul_lt_mul_of_pos_left _ ha
    simpa only [standard_ball_eq_euclidean g₀ hR, Metric.mem_ball, dist_zero_right] using hp
  · intro hy
    refine ⟨dilatedSurgeryBallInverse g₀ L a y, ?_,
      dilatedSurgeryBallChart_right_inverse g₀ ha y⟩
    rw [standard_ball_eq_euclidean g₀ hR, Metric.mem_ball, dist_zero_right]
    change ‖a⁻¹ • surgeryBallInclusion g₀ L y‖ < radialEuclideanRadius g₀ R
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    have h := mul_lt_mul_of_pos_left hy (inv_pos.mpr ha)
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using h

theorem dilatedSurgeryBallChart_image_contains (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)]
    (hL : 0 < L) (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L)
    (h : RiemannianMetric 3 (SurgeryBall.{u} g₀ L)) {scale beta : ℝ}
    (hscale : 0 < scale) (hbeta : 0 < beta)
    (hbound : ∀ y : SurgeryBall.{u} g₀ L,
      ENNReal.ofReal (Real.sqrt beta * scale * radialArclength g₀
        ‖surgeryBallInclusion g₀ L y‖) ≤ h.edist (surgeryBallTip g₀ hL) y)
    (hroom : R ≤ Real.sqrt beta * radialArclength g₀ (a * radialEuclideanRadius g₀ R)) :
    h.ball (surgeryBallTip g₀ hL) (scale * R) ⊆
      dilatedSurgeryBallChart g₀ L a '' g₀.metric.ball 0 R := by
  intro y hy
  rw [dilatedSurgeryBallChart_image g₀ ha hR hfit]
  change ‖surgeryBallInclusion g₀ L y‖ < a * radialEuclideanRadius g₀ R
  have hdist : Real.sqrt beta * scale * radialArclength g₀
      ‖surgeryBallInclusion g₀ L y‖ < scale * R := by
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hscale hR)).mp
    exact (hbound y).trans_lt hy
  have hsqrt : 0 < Real.sqrt beta := Real.sqrt_pos.mpr hbeta
  apply (radialArclength_strictMono g₀).lt_iff_lt.mp
  have hrad : Real.sqrt beta * radialArclength g₀ ‖surgeryBallInclusion g₀ L y‖ < R := by
    apply (mul_lt_mul_iff_right₀ hscale).mp
    nlinarith only [hdist]
  exact (mul_lt_mul_iff_right₀ hsqrt).mp (by
    nlinarith only [hrad, hroom])

theorem dilatedSurgeryBallChart_coefficient_contDiffOn (g₀ : StandardInitialMetric)
    {L a R : ℝ} [Nonempty (SurgeryBall.{u} g₀ L)] (ha : 0 < a) (hR : 0 < R)
    (hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L)
    (h : RiemannianMetric 3 (SurgeryBall.{u} g₀ L)) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (surgeryMetricCoefficient h (dilatedSurgeryBallChart g₀ L a) i j)
      (g₀.metric.ball 0 R) := by
  intro p hp
  have hopen : IsOpen (g₀.metric.ball 0 R) := by
    rw [standard_ball_eq_euclidean g₀ hR]
    exact Metric.isOpen_ball
  have hc := h.contDiffAt_pullbackCoefficients
    ((dilatedSurgeryBallChart_contMDiffOn g₀ ha hR hfit p hp).contMDiffAt
      (hopen.mem_nhds hp))
  exact ((hc.clm_apply contDiffAt_const).clm_apply contDiffAt_const).contDiffWithinAt

end PoincareConjecture.M36
