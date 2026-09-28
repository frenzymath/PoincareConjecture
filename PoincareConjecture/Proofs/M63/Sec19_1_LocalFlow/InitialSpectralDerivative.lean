import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialSpectralTrace

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63

open SpectralHeatNative

theorem ae_hasDerivAt_initialHeat {iota : Type*} [Countable iota]
    (lambda : iota → NNReal) (w : State iota) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (fun s => heat lambda s.toNNReal (shiftedBaseMultiplier lambda w))
        (-initialHeatGenerator lambda w t) t := by
  have hGmem := (initialHeatGenerator_memLp_energy lambda w hT).1
  have hGint : IntervalIntegrable (initialHeatGenerator lambda w) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (hGmem.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hGint.ae_hasDerivAt_integral] with t ht hmem
  have hd := (hasDerivAt_const t (shiftedBaseMultiplier lambda w)).sub
    (ht (by simpa only [uIcc_of_le hT] using Ioc_subset_Icc_self hmem) 0 left_mem_uIcc)
  have heq : (fun s => heat lambda s.toNNReal (shiftedBaseMultiplier lambda w)) =ᶠ[𝓝 t]
      (fun s => shiftedBaseMultiplier lambda w -
        ∫ v in (0 : ℝ)..s, initialHeatGenerator lambda w v) := by
    filter_upwards [Ioi_mem_nhds hmem.1] with s hs
    exact initialHeat_eq_sub_integral lambda w hs.le
  simpa only [zero_sub] using hd.congr_of_eventuallyEq heq

end PoincareConjecture.M63
