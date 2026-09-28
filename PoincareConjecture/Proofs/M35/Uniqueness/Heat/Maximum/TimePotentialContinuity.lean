import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricFieldVariation
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.L2IntegralContinuity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Cov" => V →L[ℝ] ℝ

local instance timePotentialCovectorGroup : NormedAddCommGroup Cov :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance timePotentialCovectorSpace : NormedSpace ℝ Cov :=
  ContinuousLinearMap.toNormedSpace

theorem quadratic_lipschitz_of_derivative_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (hf : ∀ z, HasFDerivAt f (D z) z)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖D z‖ ≤ C * ‖z‖) (z w : E) :
    ‖f z - f w‖ ≤ C * (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have hnorm (y : E) (hy : y ∈ segment ℝ w z) : ‖y‖ ≤ ‖z‖ + ‖w‖ := by
    have hw : w ∈ Metric.closedBall (0 : E) (‖z‖ + ‖w‖) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_add_of_nonneg_left (norm_nonneg z)
    have hz : z ∈ Metric.closedBall (0 : E) (‖z‖ + ‖w‖) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_add_of_nonneg_right (norm_nonneg w)
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (convex_closedBall (0 : E) (‖z‖ + ‖w‖)).segment_subset hw hz hy
  exact (convex_segment w z).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y _ => (hf y).hasFDerivWithinAt)
    (fun y hy => (hb y).trans (mul_le_mul_of_nonneg_left (hnorm y hy) hC))
    (left_mem_segment ℝ w z) (right_mem_segment ℝ w z)

theorem metricEntropyPotential_value_zero (g : RiemannianMetric n V)
    (η : V → ℝ) (Q : ℝ) (x : V) :
    fderiv ℝ (fun z => metricEntropyPotential g η Q (x, z)) 0 = 0 := by
  simp only [(metricEntropyPotential_value_hasFDerivAt g η Q x 0).fderiv, map_zero, smul_zero]

theorem metricEntropyTimePotential_eq_pair {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (η : V → ℝ) (Q : ℝ) (x z : V) :
    metricEntropyTimePotential D η Q (x, z) =
      -(D.scalarCurvature x) * metricEntropyPotential g η Q (x, z) -
        fderiv ℝ (fun w => metricEntropyPotential g η Q (x, w)) z (rawRicciLinear D x z) := by
  rw [(metricEntropyPotential_value_hasFDerivAt g η Q x z).fderiv]
  have hp : g.euclideanCoefficients x z (rawRicciLinear D x z) = D.ricci x z z :=
    (g.symm x _ _).trans (inner_ricciSharp D x z z)
  simp only [smul_apply, smul_eq_mul, hp, metricEntropyTimePotential, metricEntropyPotential]
  ring

private theorem potential_ricci_pair_difference
    (D : V → Cov) (B : V →L[ℝ] V) {C b : ℝ} (hC : 0 ≤ C)
    (hB : ‖B‖ ≤ b) (hD : ∀ z, ‖D z‖ ≤ C * ‖z‖)
    (hLip : ∀ z w, ‖D z - D w‖ ≤ C * ‖z - w‖) (z w : V) :
    ‖D z (B z) - D w (B w)‖ ≤ (b * C) * (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have he : D z (B z) - D w (B w) = (D z - D w) (B z) + D w (B (z - w)) := by
    simp only [sub_apply, map_sub]
    ring
  have hBz : ‖B z‖ ≤ b * ‖z‖ :=
    (B.le_opNorm z).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hBdiff : ‖B (z - w)‖ ≤ b * ‖z - w‖ :=
    (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  rw [he]
  calc
    _ ≤ ‖D z - D w‖ * ‖B z‖ + ‖D w‖ * ‖B (z - w)‖ :=
      (norm_add_le _ _).trans (add_le_add ((D z - D w).le_opNorm _) ((D w).le_opNorm _))
    _ ≤ (C * ‖z - w‖) * (b * ‖z‖) + (C * ‖w‖) * (b * ‖z - w‖) := by
      gcongr
      · exact hLip z w
      · exact hD w
    _ = _ := by ring

private theorem compact_scalar_ricci_bound {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {K : Set V} (hK : IsCompact K) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, ‖D.scalarCurvature x‖ ≤ b ∧ ‖rawRicciLinear D x‖ ≤ b := by
  have hc := (raw_scalar_contDiff D).continuous.norm.add (rawRicciLinear_contDiff D).continuous.norm
  obtain ⟨b, hb, hbound⟩ := (hK.image hc).isBounded.exists_pos_norm_le
  refine ⟨b, hb, ?_⟩
  intro x hx
  have hh := hbound _ ⟨x, hx, rfl⟩
  change ‖‖D.scalarCurvature x‖ + ‖rawRicciLinear D x‖‖ ≤ b at hh
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hh
  exact ⟨by linarith [norm_nonneg (rawRicciLinear D x)],
    by linarith [norm_nonneg (D.scalarCurvature x)]⟩

theorem metricEntropyTimePotential_quadratic_lipschitz {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {η : V → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (Q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z w,
      ‖metricEntropyTimePotential D η Q (x, z) - metricEntropyTimePotential D η Q (x, w)‖ ≤
        C * (‖z‖ + ‖w‖) * ‖z - w‖ := by
  obtain ⟨b, hb, hbound⟩ := compact_scalar_ricci_bound D hc
  refine (metricEntropyPotential_derivative_lipschitz g hη hc Q).elim ?_
  intro C hC
  have hC0 := hC.1
  refine ⟨2 * b * C, by positivity, fun x z w => ?_⟩
  by_cases hx : x ∈ tsupport η
  · let A (v : V) : Cov := fderiv ℝ (fun y => metricEntropyPotential g η Q (x, y)) v
    have hA (v : V) : ‖A v‖ ≤ C * ‖v‖ := by
      simpa only [metricEntropyPotential_value_zero, sub_zero] using hC.2 x v 0
    have hF := quadratic_lipschitz_of_derivative_growth
      (fun v => metricEntropyPotential g η Q (x, v)) A
      (fun v => (metricEntropyPotential_value_hasFDerivAt g η Q x v).differentiableAt.hasFDerivAt)
      hC.1 hA z w
    have hpair := potential_ricci_pair_difference A (rawRicciLinear D x)
      hC.1 (hbound x hx).2 hA (hC.2 x) z w
    have he : metricEntropyTimePotential D η Q (x, z) -
        metricEntropyTimePotential D η Q (x, w) =
        -(D.scalarCurvature x) * (metricEntropyPotential g η Q (x, z) -
          metricEntropyPotential g η Q (x, w)) -
            (A z (rawRicciLinear D x z) - A w (rawRicciLinear D x w)) := by
      rw [metricEntropyTimePotential_eq_pair, metricEntropyTimePotential_eq_pair]
      dsimp only [A]
      ring
    rw [he]
    calc
      _ ≤ ‖D.scalarCurvature x‖ *
          ‖metricEntropyPotential g η Q (x, z) - metricEntropyPotential g η Q (x, w)‖ +
          ‖A z (rawRicciLinear D x z) - A w (rawRicciLinear D x w)‖ := by
        simpa only [norm_mul, norm_neg] using norm_sub_le
          (-(D.scalarCurvature x) * (metricEntropyPotential g η Q (x, z) -
            metricEntropyPotential g η Q (x, w))) _
      _ ≤ b * (C * (‖z‖ + ‖w‖) * ‖z - w‖) +
          (b * C) * (‖z‖ + ‖w‖) * ‖z - w‖ :=
        add_le_add (mul_le_mul (hbound x hx).1 hF (norm_nonneg _) hb.le) hpair
      _ = _ := by ring
  · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [metricEntropyTimePotential, hz, zero_mul, sub_self, norm_zero]
    positivity

theorem metricEntropyTimePotential_field_continuous {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {η : V → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q) :
    Continuous (fieldIntegral (metricEntropyTimePotential D η Q)) := by
  refine (metricEntropyTimePotential_quadratic_lipschitz D hη hc Q).elim ?_
  intro C hC
  have hzero (x : V) : metricEntropyTimePotential D η Q (x, 0) = 0 := by
    rw [metricEntropyTimePotential_eq_pair, metricEntropyPotential_value_zero]
    simp only [metricEntropyPotential, map_zero,
      normBoundEntropy_zero_of_le hQ, mul_zero, sub_zero]
  have hbound (x z : V) : ‖metricEntropyTimePotential D η Q (x, z)‖ ≤ C * ‖z‖ ^ 2 := by
    simpa only [hzero, sub_zero, norm_zero, add_zero, pow_two, mul_assoc] using hC.2 x z 0
  exact fieldIntegral_continuous _
    (integrable_quadratic_field _ (metricEntropyTimePotential_contDiff D hη Q).continuous hbound)
    hC.1 hC.2

end PoincareConjecture.M35.Uniqueness.Heat
