import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.IntegralRatio










noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.RiemannianMetric

theorem ofReal_modelVolume_eq_lintegral (n : ℕ) {κ r : ℝ}
    (hκ : 0 ≤ κ) (hr : 0 ≤ r) :
    ENNReal.ofReal (modelVolume n κ r) =
      ∫⁻ t in Ioo (0 : ℝ) r,
        ENNReal.ofReal (n * euclideanUnitBallVolume n) *
          ENNReal.ofReal (modelS κ t ^ (n - 1)) := by
  have hf : IntegrableOn (fun t => modelS κ t ^ (n - 1)) (Ioo (0 : ℝ) r) :=
    (intervalIntegrable_modelS_pow n κ 0 r).1.mono_set Ioo_subset_Ioc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)]
      (fun t => modelS κ t ^ (n - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact pow_nonneg (modelS_nonneg hκ ht.1.le) _
  rw [modelVolume, ENNReal.ofReal_mul
    (mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_nonneg n)),
    intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hf hnonneg]
  exact (lintegral_const_mul _
    (ENNReal.continuous_ofReal.comp ((continuous_modelS κ).pow (n - 1))).measurable).symm



theorem antitoneOn_angular_div_modelVolume {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 1 ≤ n) {κ R : ℝ} (hκ : 0 ≤ κ)
    {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (fun p : Ω × ℝ => F p.1 p.2))
    (hcross : ∀ θ, ∀ t ∈ Ioo (0 : ℝ) R, ∀ s ∈ Ioo (0 : ℝ) R,
      t ≤ s → F θ s * ENNReal.ofReal (modelS κ t ^ (n - 1)) ≤
        F θ t * ENNReal.ofReal (modelS κ s ^ (n - 1))) :
    AntitoneOn (fun r : ℝ =>
      (∫⁻ θ, (∫⁻ t in Ioo (0 : ℝ) r, F θ t) ∂μ) /
        ENNReal.ofReal (modelVolume n κ r)) (Ioo (0 : ℝ) R) := by
  let c := ENNReal.ofReal (n * euclideanUnitBallVolume n)
  let G := fun t => c * ENNReal.ofReal (modelS κ t ^ (n - 1))
  have hG : Measurable G := measurable_const.mul
    (ENNReal.continuous_ofReal.comp ((continuous_modelS κ).pow (n - 1))).measurable
  have heq (r : ℝ) (hr : 0 ≤ r) :
      ENNReal.ofReal (modelVolume n κ r) = ∫⁻ t in Ioo (0 : ℝ) r, G t :=
    ofReal_modelVolume_eq_lintegral n hκ hr
  have hmodel : ∀ r ∈ Ioo (0 : ℝ) R,
      (∫⁻ t in Ioo (0 : ℝ) r, G t) ≠ 0 ∧
        (∫⁻ t in Ioo (0 : ℝ) r, G t) ≠ ⊤ := by
    intro r hr
    rw [← heq r hr.1.le]
    exact ⟨(ENNReal.ofReal_pos.mpr (modelVolume_pos hn hκ hr.1)).ne',
      ENNReal.ofReal_ne_top⟩
  have hm := antitoneOn_angular_cumulative_ratio μ hF hG hmodel
    (fun θ t ht s hs hts => show F θ s * G t ≤ F θ t * G s from by
      simpa only [G, mul_left_comm] using
        mul_le_mul' (le_refl c) (hcross θ t ht s hs hts))
  intro r hr s hs hrs
  dsimp only
  rw [heq r hr.1.le, heq s hs.1.le]
  exact hm hr hs hrs

end PoincareConjecture.RiemannianMetric
