import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactPotential
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.FrozenCoordinates







noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Set
open scoped ContDiff NNReal RealInnerProductSpace

namespace Poincare.Parabolic.Interior

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def matrixHeatResidual (A : Matrix ι ι ℝ) (f : EuclideanSpace ℝ ι × ℝ → F)
    (p : EuclideanSpace ℝ ι × ℝ) : F :=
  timeDerivative f p - Kernel.matrixLap A (spatialDerivative (spatialDerivative f) p)

variable [Nonempty ι] [CompleteSpace F]

theorem norm_hessian_le_of_matrixHeatResidual
    (A : Matrix ι ι ℝ) (hA : A.PosDef) {R S K Q δ t : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hδ : 0 < δ) (ht : 0 < t)
    (hL : ∀ y, ‖Kernel.spdSqrtEquiv A hA y‖ ≤ R * ‖y‖)
    (hLi : ∀ y, ‖(Kernel.spdSqrtEquiv A hA).symm y‖ ≤ S * ‖y‖)
    {f : EuclideanSpace ℝ ι × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : ∀ y, f (y, 0) = 0)
    (x v w : EuclideanSpace ℝ ι)
    (hsource : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y,
      ‖matrixHeatResidual A f (y, s)‖ ≤ K * ‖y - x‖ ^ (1 / 2 : ℝ) + Q)
    (hlate : ∀ s ∈ Ioo (0 : ℝ) t, t - δ < s → ∀ y,
      ‖matrixHeatResidual A f (y, s)‖ ≤ K * ‖y - x‖ ^ (1 / 2 : ℝ)) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x v w‖ ≤
      (S ^ 2 * R ^ (1 / 2 : ℝ) * Kernel.heatC2Holder (V := EuclideanSpace ℝ ι) (1 / 2) *
        4 * K * t ^ (1 / 4 : ℝ) +
        S ^ 2 * Kernel.heatC2 (EuclideanSpace ℝ ι) * Q * δ⁻¹ * t) * ‖v‖ * ‖w‖ := by
  let L := Kernel.spdSqrtEquiv A hA
  let g := spatialPullback L f
  have hdist (y : EuclideanSpace ℝ ι) :
      ‖L y - x‖ ^ (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) * ‖y - L.symm x‖ ^ (1 / 2 : ℝ) := by
    calc
      _ = ‖L (y - L.symm x)‖ ^ (1 / 2 : ℝ) := by simp only [map_sub, L.apply_symm_apply]
      _ ≤ (R * ‖y - L.symm x‖) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow (norm_nonneg _) (hL _) (by norm_num)
      _ = _ := Real.mul_rpow hR (norm_nonneg _)
  have h := norm_hessian_le_of_centered_add_time_gap_heatResidual
    (contDiff_spatialPullback L hf) (hasCompactSupport_spatialPullback L hc)
    (fun y => hzero (L y)) ht (mul_nonneg hK (Real.rpow_nonneg hR _)) hQ hδ
    (α := (1 / 2 : ℝ≥0)) (by norm_num) (by norm_num)
    (L.symm x) (L.symm v) (L.symm w)
    (fun s hs y => by
      rw [heatResidual_spd_spatialPullback A hA hf]
      norm_num only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one]
      exact (hsource s hs (L y)).trans (by
        simpa only [mul_assoc] using
          add_le_add (mul_le_mul_of_nonneg_left (hdist y) hK) (le_refl Q)))
    (fun s hs hgap y => by
      rw [heatResidual_spd_spatialPullback A hA hf]
      norm_num only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one]
      exact (hlate s hs hgap (L y)).trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hdist y) hK))
  have hjet : fderiv ℝ (fun y => fderiv ℝ (fun z => g (z, t)) y)
      (L.symm x) (L.symm v) (L.symm w) =
      fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x v w := by
    rw [fderiv_fderiv_spatialSlice (contDiff_spatialPullback L hf),
      spatialDerivative_spatialDerivative_spatialPullback L hf,
      Kernel.pushHess_apply, L.apply_symm_apply, L.apply_symm_apply, L.apply_symm_apply,
      fderiv_fderiv_spatialSlice hf]
  change ‖fderiv ℝ (fun y => fderiv ℝ (fun z => g (z, t)) y)
    (L.symm x) (L.symm v) (L.symm w)‖ ≤ _ at h
  rw [hjet] at h
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one] at h
  have hm := Kernel.heatC2Holder_nonneg (V := EuclideanSpace ℝ ι) (1 / 2)
  have hm₂ := Kernel.heatC2_nonneg (V := EuclideanSpace ℝ ι)
  refine h.trans ?_
  calc
    _ ≤ ((S * ‖v‖) * (S * ‖w‖) * (K * R ^ (1 / 2 : ℝ)) *
        Kernel.heatC2Holder (V := EuclideanSpace ℝ ι) (1 / 2)) *
          ((2 / (1 / 2 : ℝ)) * t ^ ((1 / 2 : ℝ) / 2)) +
        ((S * ‖v‖) * (S * ‖w‖) * Q * δ⁻¹ * Kernel.heatC2 (EuclideanSpace ℝ ι)) * t := by
      norm_num only
      gcongr <;> exact hLi _
    _ = _ := by norm_num; ring



theorem exists_uniform_matrix_heatResidual_hessian_bound
    (lam upper : ℝ) (hlam : 0 < lam) (hupper : lam ≤ upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Matrix ι ι ℝ) (_hA : A.PosDef),
        (∀ y : EuclideanSpace ℝ ι,
          lam * ‖y‖ ^ 2 ≤ inner ℝ y (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A y)) →
        (∀ y : EuclideanSpace ℝ ι,
          inner ℝ y (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A y) ≤ upper * ‖y‖ ^ 2) →
        ∀ (f : EuclideanSpace ℝ ι × ℝ → F), ContDiff ℝ ∞ f → HasCompactSupport f →
          (∀ y, f (y, 0) = 0) →
        ∀ (K Q δ t : ℝ), 0 ≤ K → 0 ≤ Q → 0 < δ → 0 < t →
        ∀ x : EuclideanSpace ℝ ι,
          (∀ s ∈ Ioo (0 : ℝ) t, ∀ y,
            ‖matrixHeatResidual A f (y, s)‖ ≤ K * ‖y - x‖ ^ (1 / 2 : ℝ) + Q) →
          (∀ s ∈ Ioo (0 : ℝ) t, t - δ < s → ∀ y,
            ‖matrixHeatResidual A f (y, s)‖ ≤ K * ‖y - x‖ ^ (1 / 2 : ℝ)) →
          ∀ v w : EuclideanSpace ℝ ι,
            ‖fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x v w‖ ≤
              C * (K * t ^ (1 / 4 : ℝ) + Q * δ⁻¹ * t) * ‖v‖ * ‖w‖ := by
  let D₁ := (Real.sqrt lam)⁻¹ ^ 2 * (Real.sqrt upper) ^ (1 / 2 : ℝ) *
    Kernel.heatC2Holder (V := EuclideanSpace ℝ ι) (1 / 2) * 4
  let D₂ := (Real.sqrt lam)⁻¹ ^ 2 * Kernel.heatC2 (EuclideanSpace ℝ ι)
  let C := max 1 (max D₁ D₂)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro A hA hlower hupperA f hf hc hzero K Q δ t hK hQ hδ ht x hsource hlate v w
  have h := norm_hessian_le_of_matrixHeatResidual A hA
    (Real.sqrt_nonneg upper) (inv_nonneg.mpr (Real.sqrt_nonneg lam)) hK hQ hδ ht
    (Kernel.spdSqrt_apply_le A hA (hlam.le.trans hupper) hupperA)
    (Kernel.spdSqrt_symm_le A hA hlam hlower) hf hc hzero x v w hsource hlate
  have h₁ : D₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : D₂ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine h.trans ?_
  change (D₁ * K * t ^ (1 / 4 : ℝ) + D₂ * Q * δ⁻¹ * t) * ‖v‖ * ‖w‖ ≤ _
  calc
    _ ≤ (C * K * t ^ (1 / 4 : ℝ) + C * Q * δ⁻¹ * t) * ‖v‖ * ‖w‖ := by
      gcongr
    _ = _ := by ring

end Poincare.Parabolic.Interior
