import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.L2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Tactic.Linarith



noncomputable section

open Set MeasureTheory
open scoped ENNReal
open Poincare.Analysis.Sobolev

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem continuous_memLp_on_compact {g : E → ℝ} (hg : Continuous g)
    {K : Set E} (hK : IsCompact K) : MemLp g 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.continuousOn.norm
  apply MemLp.of_bound hg.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC (mem_image_of_mem _ hx)

theorem eLpNorm_two_le_of_integral_sq_le_source
    {V W : Set E} {u f q : E → ℝ} (hu : MemLp u 2 (volume.restrict V))
    (hf : MemLp f 2 (volume.restrict V)) (hq : MemLp q 2 (volume.restrict W))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫ x in W, q x ^ 2) ≤
      C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2)) :
    eLpNorm q 2 (volume.restrict W) ≤ ENNReal.ofReal (Real.sqrt C) *
      (eLpNorm u 2 (volume.restrict V) + eLpNorm f 2 (volume.restrict V)) := by
  have hn : (eLpNorm q 2 (volume.restrict W)).toReal ≤ Real.sqrt C *
      ((eLpNorm u 2 (volume.restrict V)).toReal +
        (eLpNorm f 2 (volume.restrict V)).toReal) := by
    apply (sq_le_sq₀ ENNReal.toReal_nonneg
      (mul_nonneg (Real.sqrt_nonneg C) (add_nonneg ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg))).mp
    rw [eLpNorm_toReal_sq_eq_integral hq, mul_pow, Real.sq_sqrt hC]
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ hC
    rw [← eLpNorm_toReal_sq_eq_integral hu, ← eLpNorm_toReal_sq_eq_integral hf]
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm u 2 (volume.restrict V)),
      ENNReal.toReal_nonneg (a := eLpNorm f 2 (volume.restrict V))]
  have h := ENNReal.ofReal_le_ofReal hn
  rwa [ENNReal.ofReal_toReal hq.eLpNorm_ne_top,
    ENNReal.ofReal_mul (Real.sqrt_nonneg C),
    ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hu.eLpNorm_ne_top, ENNReal.ofReal_toReal hf.eLpNorm_ne_top] at h

end Poincare.Analysis.Elliptic.InteriorEstimates
