import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable









set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem contDiff_of_contDiffOn_of_tsupport_subset {U : Set E} (hU : IsOpen U)
    {f : E → F} {k : ℕ∞ω} (hf : ContDiffOn ℝ k f U) (hs : tsupport f ⊆ U) :
    ContDiff ℝ k f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hU.mem_nhds (hs hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem integrable_of_continuousOn_of_tsupport_subset
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : E → F} (hf : ContinuousOn f U) (hs : tsupport f ⊆ K) : Integrable f μ := by
  have hcont := hf.continuous_of_tsupport_subset hU (hs.trans hKU)
  exact hcont.integrable_of_hasCompactSupport
    (hK.of_isClosed_subset (isClosed_tsupport _) hs)

end PoincareConjecture.M10
