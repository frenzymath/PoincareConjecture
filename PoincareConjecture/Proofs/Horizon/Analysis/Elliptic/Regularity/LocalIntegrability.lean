import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Lp.MeasurableSpace



noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Poincare.Analysis.Elliptic

variable {n : ℕ} {O : Set (EuclideanSpace ℝ (Fin n))}
  {u c : EuclideanSpace ℝ (Fin n) → ℝ}


theorem locallyIntegrableOn_of_compact_memLp (hO : IsOpen O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K)) :
    LocallyIntegrableOn u O := by
  apply (locallyIntegrableOn_iff hO.isLocallyClosed).mpr
  intro K hKO hK
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  exact (hu K hK hKO).integrable (by norm_num)


theorem compact_memLp_mul_continuousOn (hc : ContinuousOn c O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKO : K ⊆ O) :
    MemLp (fun x => c x * u x) 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hc.mono hKO).norm
  have hcK : MemLp c ∞ (volume.restrict K) := by
    apply memLp_top_of_bound ((hc.mono hKO).aestronglyMeasurable hK.measurableSet) C
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hC (mem_image_of_mem _ hx)
  exact (hu K hK hKO).mul hcK

end Poincare.Analysis.Elliptic
