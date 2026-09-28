import PoincareConjecture.Proofs.M65.Def18_23_Profile.AreaWeight
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Icc a b))

theorem m65AreaWeight_uniformBounds (compact : IsCompact (univ : Set M)) :
    ∃ U : ℝ, 0 < U ∧ ∃ D : ℝ, 0 < D ∧
      (∀ t ∈ Icc a b, |m65AreaWeight F t| ≤ U) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |m65AreaWeight F t - m65AreaWeight F s| ≤ D * |t - s|) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |∫ r in s..t, m65AreaWeight F r| ≤ U * |t - s|) := by
  have hweight := m65AreaWeight_continuousOn F compact
  have hderiv := ((flowScalarCurvatureInfimum_continuousOn F compact).div_const 2).mul hweight
  obtain ⟨U0, hU0⟩ := isCompact_Icc.exists_bound_of_continuousOn hweight
  obtain ⟨D0, hD0⟩ := isCompact_Icc.exists_bound_of_continuousOn hderiv
  let U := |U0| + 1
  let D := |D0| + 1
  have hU : 0 < U := by dsimp [U]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hUb (t : ℝ) (ht : t ∈ Icc a b) : |m65AreaWeight F t| ≤ U :=
    (hU0 t ht).trans ((le_abs_self _).trans (le_add_of_nonneg_right (by norm_num)))
  have hDb (t : ℝ) (ht : t ∈ Icc a b) :
      ‖(flowScalarCurvatureInfimum F t / 2) * m65AreaWeight F t‖ ≤ D :=
    (hD0 t ht).trans ((le_abs_self _).trans (le_add_of_nonneg_right (by norm_num)))
  refine ⟨U, hU, D, hD, hUb, ?_, ?_⟩
  · intro s hs t ht
    simpa only [Real.norm_eq_abs] using
      (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r hr => m65AreaWeight_hasDerivWithinAt F compact hr) hDb hs ht
  · intro s hs t ht
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_of_norm_le_const (f := m65AreaWeight F)
        (a := s) (b := t) (C := U) (fun r hr => by
          simpa only [Real.norm_eq_abs] using
            hUb r (uIcc_subset_Icc hs ht (uIoc_subset_uIcc hr)))

end PoincareConjecture
