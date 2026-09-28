import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingLimit
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingAE
import Mathlib.Analysis.Calculus.MeanValue











set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Convolution SchwartzMap InnerProductSpace

namespace PoincareConjecture.M65Interior

private theorem plane_linear_norm_le (L : LoopPlane →L[ℝ] ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hL : ∀ i : Fin 2, |L (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ A) :
    ‖L‖ ≤ 2 * A := by
  apply L.opNorm_le_bound (by positivity)
  intro z
  have hrepr : (∑ i : Fin 2, z i • EuclideanSpace.basisFun (Fin 2) ℝ i) = z :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr z
  have heq : L z = z 0 * L (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      z 1 * L (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    have h := congrArg L hrepr
    simpa only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul] using h.symm
  have ht (i : Fin 2) : |z i * L (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ ‖z‖ * A := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i)
      (hL i) (abs_nonneg _) (norm_nonneg _)
  rw [heq, Real.norm_eq_abs]
  exact (abs_add_le _ _).trans (by nlinarith only [ht 0, ht 1])





theorem exists_scalar_holder_representative
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    (x0 : LoopPlane) {Λ β R : ℝ} (hΛ : 0 ≤ Λ) (hβ : 0 < β) (hR : 0 < R)
    (hE : ∀ x ∈ closedBall x0 R, ∀ r ∈ Ioc 0 R,
      (∫ z in closedBall x r, ∑ i : Fin 2, (d i z) ^ 2) ≤ Λ * r ^ (2 * β)) :
    ∃ (v : LoopPlane → ℝ) (H : ℝ), 0 < H ∧ ContinuousOn v (closedBall x0 (R / 2)) ∧
      (v =ᵐ[volume.restrict (closedBall x0 (R / 2))] u) ∧
      ∀ x ∈ closedBall x0 (R / 2), ∀ y ∈ closedBall x0 (R / 2),
        |v y - v x| ≤ H * dist y x ^ β := by
  obtain ⟨v, K, hK, hv, hlim, herr⟩ :=
    averagingValue_exists_uniform_limit u d hw hΛ hβ hR hE
  obtain ⟨C, hC, hD⟩ := averagingValue_derivatives_of_energy (β := β) hΛ
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hsmall : closedBall x0 (R / 2) ⊆ closedBall x0 R :=
    closedBall_subset_closedBall (by linarith)
  refine ⟨v, 2 * K + 2 * C, by positivity, hv.mono hsmall, ?_, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset hsmall
      (averagingValue_limit_ae hu isClosed_closedBall.measurableSet hlim)
  · intro x hx y hy
    by_cases heq : y = x
    · simp only [heq, sub_self, abs_zero, dist_self, Real.zero_rpow hβ.ne', mul_zero, le_refl]
    have hr : 0 < dist y x := dist_pos.mpr heq
    have hrR : dist y x ≤ R := by
      calc
        dist y x ≤ dist y x0 + dist x0 x := dist_triangle _ _ _
        _ ≤ R := by
          rw [dist_comm x0 x]
          have hx' : dist x x0 ≤ R / 2 := hx
          have hy' : dist y x0 ≤ R / 2 := hy
          linarith
    let r := dist y x
    have hreg : ContDiff ℝ ∞ (averagingValue u r) :=
      (averagingKernel_hasCompactSupport hr).contDiff_convolution_right
        (ContinuousLinearMap.mul ℝ ℝ) hu (averagingKernel_contDiff r)
    have hnorm (z : LoopPlane) (hz : z ∈ closedBall x0 R) :
        ‖fderiv ℝ (averagingValue u r) z‖ ≤ 2 * (C * r ^ (β - 1)) := by
      apply plane_linear_norm_le _ (mul_nonneg hC.le (Real.rpow_nonneg hr.le _))
      exact (hD u d hw z r hr (hE z hz r ⟨hr, hrR⟩)).1
    have hm := (convex_closedBall x0 R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hreg.differentiable (by simp)) z) hnorm (hsmall hx) (hsmall hy)
    have hspace : |averagingValue u r y - averagingValue u r x| ≤ 2 * C * r ^ β := by
      have hid : 2 * (C * r ^ (β - 1)) * ‖y - x‖ = 2 * C * r ^ β := by
        rw [Real.rpow_sub_one hr.ne', ← dist_eq_norm]
        change 2 * (C * (r ^ β / r)) * r = _
        field_simp [show r ≠ 0 from hr.ne']
      simpa only [Real.norm_eq_abs, hid] using hm
    have hleft : |v y - averagingValue u r y| ≤ K * r ^ β := by
      rw [abs_sub_comm]
      exact herr y (hsmall hy) r ⟨hr, hrR⟩
    have hright := herr x (hsmall hx) r ⟨hr, hrR⟩
    have htriangle := dist_triangle4 (v y) (averagingValue u r y) (averagingValue u r x) (v x)
    simp only [Real.dist_eq] at htriangle
    change |v y - v x| ≤ (2 * K + 2 * C) * r ^ β
    nlinarith only [htriangle, hleft, hspace, hright]

end PoincareConjecture.M65Interior
