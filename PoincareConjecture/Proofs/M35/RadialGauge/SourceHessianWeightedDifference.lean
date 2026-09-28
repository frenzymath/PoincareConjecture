import PoincareConjecture.Proofs.M35.RadialGauge.SourceHessianDifference
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingGraphDifference









set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => V →L[ℝ] ℝ

noncomputable local instance m35SourceHessianWeightedDifferenceLocal1 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35SourceHessianWeightedDifferenceLocal2 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace

theorem gaugeSource_weighted_hessian_difference_bound
    {b : V → V} {G : V → ℝ → ℝ} {u v : V → ℝ} {x : V}
    {eta B B1 B2 L1 M2 M3 H J d E : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hL1 : 0 ≤ L1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hbb : ‖b x‖ ≤ B) (hdb : ‖fderiv ℝ b x‖ ≤ B1)
    (hddb : ‖fderiv ℝ (fderiv ℝ b) x‖ ≤ B2)
    (hGz : |forcingScalarDeriv G x (u x)| ≤ L1)
    (hGxz : ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2)
      (x, v x) (0, 1)‖ ≤ M2)
    (hGzx : ‖(fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2)
      (x, u x)).comp (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ M2)
    (hGzzu : ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2)
      (x, u x) (0, 1)‖ ≤ M2)
    (hGzzv : ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2)
      (x, v x) (0, 1)‖ ≤ M2)
    (hGzlip : |forcingScalarDeriv G x (u x) - forcingScalarDeriv G x (v x)| ≤
      M2 * |u x - v x|)
    (hDGxlip : ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, u x) -
      fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, v x)‖ ≤ M3 * |u x - v x|)
    (hDGzlip : ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, u x) -
      fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, v x)‖ ≤ M3 * |u x - v x|)
    (hpu : (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ eta)
    (hpv : (1 + ‖x‖) * ‖fderiv ℝ v x‖ ≤ eta)
    (hHu : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H)
    (hHv : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ H)
    (hJv : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ J)
    (huv : (1 + ‖x‖) * |u x - v x| ≤ d)
    (hpuv : (1 + ‖x‖) * ‖fderiv ℝ u x - fderiv ℝ v x‖ ≤ d)
    (hHuv : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ v) x‖ ≤ d)
    (hJuv : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x -
      fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ E) :
    (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugeSource b G u)) x -
      fderiv ℝ (fderiv ℝ (gaugeSource b G v)) x‖ ≤
      (B + 2 * eta) * E +
        (2 * B1 + 4 * H + L1 + B2 + 2 * J + 2 * M2 * (1 + eta) +
          M3 * (1 + eta) ^ 2 + M2 * H) * d := by
  have hw : 0 ≤ 1 + ‖x‖ := by positivity
  have hp : ‖fderiv ℝ u x‖ ≤ eta := by
    nlinarith only [hpu, mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ u x))]
  have hq : ‖fderiv ℝ v x‖ ≤ eta := by
    nlinarith only [hpv, mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ v x))]
  have hHu' : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H := by
    nlinarith only [hHu, mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ (fderiv ℝ u) x))]
  have hHv' : ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ H := by
    nlinarith only [hHv, mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ (fderiv ℝ v) x))]
  have hJv' : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ J := by
    nlinarith only [hJv, mul_nonneg (norm_nonneg x)
      (ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x))]
  have hgx := forcing_graph_fderiv_difference_norm_le hM3
    ((forcingSpaceDeriv_contDiff hG).differentiable (by simp) (x, u x))
    ((forcingSpaceDeriv_contDiff hG).differentiable (by simp) (x, v x))
    (hu.differentiable (by simp) x) (hv.differentiable (by simp) x) hp hGxz hDGxlip
  have hgz := forcing_graph_fderiv_difference_norm_le hM3
    ((forcingScalarDeriv_contDiff hG).differentiable (by simp) (x, u x))
    ((forcingScalarDeriv_contDiff hG).differentiable (by simp) (x, v x))
    (hu.differentiable (by simp) x) (hv.differentiable (by simp) x) hp hGzzv hDGzlip
  have hgzu := forcing_graph_fderiv_norm_le
    ((forcingScalarDeriv_contDiff hG).differentiable (by simp) (x, u x))
    (hu.differentiable (by simp) x)
  have hgzu' : ‖fderiv ℝ (fun y => forcingScalarDeriv G y (u y)) x‖ ≤ M2 * (1 + eta) := by
    have hp' := mul_le_mul hGzzu hp (norm_nonneg _) hM2
    nlinarith only [hgzu, hGzx, hp']
  have hgraph (A : V → ℝ → D)
      (hA : ‖fderiv ℝ (fun y => A y (u y) - A y (v y)) x‖ ≤
        M3 * (1 + eta) * |u x - v x| + M2 * ‖fderiv ℝ u x - fderiv ℝ v x‖) :
      (1 + ‖x‖) * ‖fderiv ℝ (fun y => A y (u y) - A y (v y)) x‖ ≤
        (M3 * (1 + eta) + M2) * d := by
    have h0 := mul_le_mul_of_nonneg_left hA hw
    have h1 := mul_le_mul_of_nonneg_left huv (show 0 ≤ M3 * (1 + eta) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hpuv hM2
    nlinarith only [h0, h1, h2]
  have hgx' := hgraph (forcingSpaceDeriv G) hgx
  have hgz' : (1 + ‖x‖) *
      ‖fderiv ℝ (fun y => forcingScalarDeriv G y (u y) - forcingScalarDeriv G y (v y)) x‖ ≤
      (M3 * (1 + eta) + M2) * d := by
    have h0 := mul_le_mul_of_nonneg_left hgz hw
    have h1 := mul_le_mul_of_nonneg_left huv (show 0 ≤ M3 * (1 + eta) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hpuv hM2
    nlinarith only [h0, h1, h2]
  have hmain := mul_le_mul_of_nonneg_left (gaugeSource_hessian_difference_norm_le hb hG hu hv x) hw
  have hhigh := mul_le_mul_of_nonneg_left hJuv (show 0 ≤ B + 2 * eta by positivity)
  have hhigh' := mul_le_mul_of_nonneg_right
    (add_le_add hbb (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)))
    (mul_nonneg hw (norm_nonneg (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x -
      fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x)))
  have hH0 := mul_le_mul_of_nonneg_left hHuv (show 0 ≤ 2 * B1 + 4 * H + L1 by positivity)
  have hH1 := mul_le_mul_of_nonneg_right
    (show 2 * ‖fderiv ℝ b x‖ + 2 * ‖fderiv ℝ (fderiv ℝ u) x‖ +
        2 * ‖fderiv ℝ (fderiv ℝ v) x‖ + |forcingScalarDeriv G x (u x)| ≤
        2 * B1 + 4 * H + L1 by linarith only [hdb, hHu', hHv', hGz])
    (mul_nonneg hw (norm_nonneg (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ v) x)))
  have hp0 := mul_le_mul_of_nonneg_left hpuv
    (show 0 ≤ B2 + 2 * J + M2 * (1 + eta) by positivity)
  have hp1 := mul_le_mul_of_nonneg_right
    (show ‖fderiv ℝ (fderiv ℝ b) x‖ + 2 * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ +
        ‖fderiv ℝ (fun y => forcingScalarDeriv G y (u y)) x‖ ≤ B2 + 2 * J + M2 * (1 + eta)
      by linarith only [hddb, hJv', hgzu'])
    (mul_nonneg hw (norm_nonneg (fderiv ℝ u x - fderiv ℝ v x)))
  have hz0 := mul_le_mul_of_nonneg_left huv hM2
  have hz1 := mul_le_mul_of_nonneg_left hGzlip hw
  have hz2 := mul_le_mul_of_nonneg_left hHv'
    (mul_nonneg hw (abs_nonneg (forcingScalarDeriv G x (u x) - forcingScalarDeriv G x (v x))))
  have hzbound : (1 + ‖x‖) * |forcingScalarDeriv G x (u x) - forcingScalarDeriv G x (v x)| ≤
      M2 * d := by nlinarith only [hz0, hz1]
  have hz3 := mul_le_mul_of_nonneg_left hzbound hH
  have hgz0 := mul_le_mul_of_nonneg_left hgz' heta
  have hgz1 := mul_le_mul_of_nonneg_left hq
    (mul_nonneg hw (norm_nonneg
      (fderiv ℝ (fun y => forcingScalarDeriv G y (u y) - forcingScalarDeriv G y (v y)) x)))
  nlinarith only [hmain, hhigh, hhigh', hH0, hH1, hp0, hp1, hgx', hz2, hz3, hgz0, hgz1]

end PoincareConjecture.M35.RadialGauge
