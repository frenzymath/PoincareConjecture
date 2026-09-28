import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingBound
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls











set_option autoImplicit false

open Set Filter Metric MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65Interior





theorem averagingValue_tendsto_ae {u : LoopPlane → ℝ}
    (hu : LocallyIntegrable u volume) :
    ∀ᵐ x, Tendsto (fun r => averagingValue u r x) (𝓝[>] 0) (𝓝 (u x)) := by
  obtain ⟨B, _hB0, hB⟩ := averagingProfile_bounded
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hu 0] with x hx
  have hmean := hx (fun _ : ℝ => x) (fun r => r) tendsto_id
    (Eventually.of_forall (fun r => by simp))
  have hmass : Tendsto (fun r : ℝ => ∫ z, averagingKernel r (x - z))
      (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [integral_sub_left_eq_self, averagingKernel_integral hr]
  have hsupp : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Function.support (fun z => averagingKernel r (x - z)) ⊆ closedBall x r := by
    filter_upwards [self_mem_nhdsWithin] with r hr z hz
    rw [mem_closedBall_iff_norm']
    exact mem_closedBall_zero_iff.mp (averagingKernel_support hr hz)
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z,
      |averagingKernel r (x - z)| ≤ (B * Real.pi) / volume.real (closedBall x r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr z
    have hvol : volume.real (closedBall x r) = r ^ 2 * Real.pi := by
      rw [Measure.real, EuclideanSpace.volume_closedBall_fin_two]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal Real.pi_nonneg]
    rw [hvol, abs_of_nonneg (averagingKernel_nonneg r (x - z))]
    calc
      averagingKernel r (x - z) ≤ r⁻¹ ^ 2 * B :=
        mul_le_mul_of_nonneg_left (hB (r⁻¹ • (x - z))) (sq_nonneg _)
      _ = (B * Real.pi) / (r ^ 2 * Real.pi) := by
        field_simp
  have h := tendsto_integral_smul_of_tendsto_average_norm_sub (B * Real.pi) hmean
    (Eventually.of_forall (fun r => hu.integrableOn_isCompact (isCompact_closedBall x r)))
    hmass hsupp hbound
  simpa only [averagingValue, smul_eq_mul, mul_comm] using h




theorem averagingValue_limit_ae {u v : LoopPlane → ℝ}
    (hu : LocallyIntegrable u volume) {S : Set LoopPlane} (hS : MeasurableSet S)
    (hlim : TendstoUniformlyOn (fun r x => averagingValue u r x) v (𝓝[>] 0) S) :
    v =ᵐ[volume.restrict S] u := by
  change ∀ᵐ x ∂volume.restrict S, v x = u x
  rw [ae_restrict_iff' hS]
  filter_upwards [averagingValue_tendsto_ae hu] with x hx hxS
  exact tendsto_nhds_unique (hlim.tendsto_at hxS) hx

end PoincareConjecture.M65Interior
