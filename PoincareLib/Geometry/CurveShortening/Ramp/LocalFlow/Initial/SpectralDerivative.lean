import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Initial.SpectralTrace

/-!
# Differentiation of the actual initial heat contribution

The proved Bochner primitive identity and Mathlib's a.e. fundamental
theorem give the actual homogeneous derivative at positive times.
MT2007 Claim 19.1, p. 437; contract review block 8 and the supporting
derivation `2026-09-21-affine-spectral-residual.md`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareMT.M63

open SpectralHeatNative

/-- The actual initial heat path has negative generator derivative a.e.
No derivative at the initial time is asserted. MT2007 Claim 19.1, p. 437;
contract block 8 and the affine spectral-residual derivation. -/
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

end PoincareMT.M63
