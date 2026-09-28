import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.Uniform




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientRescalingSequence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

private theorem sqrt_one_div_pow_eq_rpow_neg_half {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.sqrt (1 / s) ^ n = s ^ (-(n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : 0 ≤ 1 / s), one_div,
    Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
  congr 1
  ring

theorem integral_normalized_reducedLength_eq_reducedVolume
    (S : AncientRescalingSequence K) (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ q, τ ^ (-(n : ℝ) / 2) *
      Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ))
        ∂calibratedMetricVolume ((S.rescaling k).flow.metric (-τ))) =
      reducedVolume K.flow 0 S.reference (S.scale k * τ) := by
  have hvol : calibratedMetricVolume ((S.rescaling k).flow.metric (-τ)) =
      ENNReal.ofReal (Real.sqrt (1 / S.scale k)) ^ n •
        calibratedMetricVolume (K.flow.metric (-(S.scale k * τ))) := by
    ext A hA
    rw [Measure.smul_apply, smul_eq_mul]
    simpa only [mul_neg] using (S.rescaling k).volume_scale (-τ) (neg_neg_of_pos hτ) A
  rw [hvol, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]
  unfold reducedVolume
  simp only [zero_sub, reducedVolumeDensity, if_pos (mul_pos (S.scale_pos k) hτ)]
  rw [integral_const_mul, integral_const_mul, ← mul_assoc,
    sqrt_one_div_pow_eq_rpow_neg_half (S.scale_pos k),
    ← Real.mul_rpow (S.scale_pos k).le hτ.le]
  rfl

theorem lintegral_normalized_reducedLength_eq_reducedVolume
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (∫⁻ q, ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) *
      Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)))
        ∂calibratedMetricVolume ((S.rescaling k).flow.metric (-τ))) =
      ENNReal.ofReal (reducedVolume K.flow 0 S.reference (S.scale k * τ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (S.normalized_reducedLength_integrable P k hτ)
    (ae_of_all _ (fun q => mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.exp_nonneg _))),
    S.integral_normalized_reducedLength_eq_reducedVolume k hτ]

end PoincareConjecture.AncientRescalingSequence
