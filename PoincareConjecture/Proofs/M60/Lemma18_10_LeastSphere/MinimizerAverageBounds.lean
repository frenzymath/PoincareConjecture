import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakAverages
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.Mollifier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem suL2_disk_L1_bound {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} (a : Plane) {r : ℝ} (hr : 0 < r)
    (hf : MemLp f 2 (volume.restrict (Metric.ball a r))) :
    (∫ x in Metric.ball a r, ‖f x‖) ≤
      Real.sqrt Real.pi * r * Real.sqrt (∫ x in Metric.ball a r, ‖f x‖ ^ 2) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a r) < ⊤)⟩
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf.norm) (memLp_const (μ := volume.restrict (Metric.ball a r)) (1 : ℝ))
  have hvol : volume.real (Metric.ball a r) = r ^ 2 * Real.pi := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  have h' : (∫ x in Metric.ball a r, ‖f x‖) ≤
      Real.sqrt (∫ x in Metric.ball a r, ‖f x‖ ^ 2) *
        Real.sqrt (volume.real (Metric.ball a r)) := by
    simpa only [norm_norm, norm_one, mul_one, Real.rpow_two, one_pow, integral_const,
      smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow, Measure.real,
      Measure.restrict_apply_univ] using h
  rw [hvol, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le] at h'
  exact h'.trans_eq (by ring)

theorem suPlaneOperator_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Plane →L[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hcol : ∀ i : Fin 2, ‖L (EuclideanSpace.single i 1)‖ ≤ C) : ‖L‖ ≤ 2 * C := by
  apply L.opNorm_le_bound (by positivity)
  intro x
  have hx : x = x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  have hL : L x = x 0 • L (EuclideanSpace.single 0 1) +
      x 1 • L (EuclideanSpace.single 1 1) := by
    nth_rw 1 [hx]
    rw [map_add, map_smul, map_smul]
  calc
    ‖L x‖ ≤ ‖x 0‖ * ‖L (EuclideanSpace.single 0 1)‖ +
        ‖x 1‖ * ‖L (EuclideanSpace.single 1 1)‖ := by
      rw [hL]
      simpa only [norm_smul] using norm_add_le
        (x 0 • L (EuclideanSpace.single 0 1)) (x 1 • L (EuclideanSpace.single 1 1))
    _ ≤ ‖x‖ * C + ‖x‖ * C := add_le_add
      (mul_le_mul (PiLp.norm_apply_le x 0) (hcol 0) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (PiLp.norm_apply_le x 1) (hcol 1) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem suMollifier_plane_bound {r : ℝ} (hr : 0 < r) (x : Plane) :
    mollifierEps (d := 2) hr x ≤ 4 / (r ^ 2 * Real.pi) := by
  have h := (mollifierBumpEps (d := 2) hr).normed_le_div_measure_closedBall_rOut
    volume 2 (by dsimp only [mollifierBumpEps]; linarith) x
  have hvol : volume.real (Metric.closedBall (0 : Plane) r) = r ^ 2 * Real.pi := by
    simp only [Measure.real, EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  have hdim : Module.finrank ℝ Plane = 2 := by simp
  simpa only [mollifierEps, mollifierBumpEps, hdim,
    hvol, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem suMollifier_convolution_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) {f : Plane → E}
    (hf : LocallyIntegrable f volume) (x : Plane) :
    ‖(mollifierEps hr ⋆[lsmul ℝ ℝ, volume] f) x‖ ≤
      (4 / (r ^ 2 * Real.pi)) * ∫ y in Metric.ball x r, ‖f y‖ := by
  have hi : IntegrableOn f (Metric.ball x r) :=
    (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have heq : (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] f) x =
      ∫ y in Metric.ball x r, mollifierEps hr (x - y) • f y := by
    rw [convolution_lsmul_swap]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro y hy
    have hz : x - y ∉ Metric.ball (0 : Plane) r := by
      simpa only [Metric.mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm] using hy
    have hzero : mollifierEps hr (x - y) = 0 := by
      apply Function.notMem_support.mp
      simpa only [mollifierEps_support_eq] using hz
    rw [hzero, zero_smul]
  rw [heq, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hi.norm.const_mul _)
  exact Eventually.of_forall fun y => by
    rw [norm_smul, Real.norm_of_nonneg (mollifierEps_nonneg hr _)]
    exact mul_le_mul_of_nonneg_right (suMollifier_plane_bound hr _) (norm_nonneg _)

end PoincareConjecture.M60

end
