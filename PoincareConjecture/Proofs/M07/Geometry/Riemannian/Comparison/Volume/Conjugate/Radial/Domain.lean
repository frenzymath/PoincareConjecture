import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactVariation

set_option autoImplicit false

open Set

namespace PoincareConjecture.RiemannianMetric

theorem exists_radial_closed_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {v : E} (hv : v ∈ Metric.ball 0 R) :
    ∃ a b : ℝ, a < 0 ∧ 1 < b ∧
      Icc a b ⊆ {t : ℝ | t • v ∈ Metric.ball 0 R} := by
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hvR) ‖v‖
  refine ⟨-(1 + δ), 1 + δ, by linarith, by linarith, ?_⟩
  intro t ht
  rw [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
  have ht' : |t| ≤ 1 + δ := abs_le.mpr ht
  have hmul := mul_le_mul_of_nonneg_right ht' (norm_nonneg v)
  nlinarith

end PoincareConjecture.RiemannianMetric
