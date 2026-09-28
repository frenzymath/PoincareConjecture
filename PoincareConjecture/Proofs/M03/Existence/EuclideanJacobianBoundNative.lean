import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace








set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace PoincareConjecture.EuclideanJacobianBoundNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_volume_image_bound {F : E → E} {U K : Set E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : Set E, MeasurableSet A → A ⊆ K →
      volume (F '' A) ≤ ENNReal.ofReal B * volume A := by
  have hdet : ContinuousOn (fun x => |(fderiv ℝ F x).det|) U :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (hF.continuousOn_fderiv_of_isOpen hU (by norm_num))).abs
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hdet.mono hKU)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro A hA hAK
  calc
    volume (F '' A) ≤ ∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ F x).det| := by
      apply addHaar_image_le_lintegral_abs_det_fderiv volume hA
      intro x hx
      exact (((hF.differentiableOn (by norm_num)) x (hKU (hAK hx))).differentiableAt
        (hU.mem_nhds (hKU (hAK hx)))).hasFDerivAt.hasFDerivWithinAt
    _ ≤ ∫⁻ _x in A, ENNReal.ofReal (max B 0) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact ENNReal.ofReal_le_ofReal ((hB (mem_image_of_mem _ (hAK hx))).trans (le_max_left _ _))
    _ = _ := by simp

end PoincareConjecture.EuclideanJacobianBoundNative
