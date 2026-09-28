import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.Profile
import Mathlib.Analysis.Calculus.LocalExtr.Basic











noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace PoincareConjecture

theorem deriv_axialTransitionProfile_eq_zero_of_not_mem
    {L s : ℝ} (hL : 0 < L) (hs : s ∉ Ioo (-L) L) :
    deriv (axialTransitionProfile L) s = 0 := by
  rcases le_or_gt s (-L) with hs' | hs'
  · have hmin : IsLocalMin (axialTransitionProfile L) s := by
      filter_upwards [] with t
      rw [axialTransitionProfile_zero hL hs']
      exact (axialTransitionProfile_mem_Icc L t).1
    exact hmin.deriv_eq_zero
  · have hsL : L ≤ s := le_of_not_gt (fun h => hs ⟨hs', h⟩)
    have hmax : IsLocalMax (axialTransitionProfile L) s := by
      filter_upwards [] with t
      rw [axialTransitionProfile_one hL hsL]
      exact (axialTransitionProfile_mem_Icc L t).2
    exact hmax.deriv_eq_zero


theorem lintegral_ofReal_mul_deriv_axialTransitionProfile_of_le
    {L R κ : ℝ} (hL : 0 < L) (hLR : L ≤ R) (hκ : 0 ≤ κ) :
    ∫⁻ s in Ioo (-R) R, ENNReal.ofReal
      (κ * deriv (axialTransitionProfile L) s) = ENNReal.ofReal κ := by
  let F : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (κ * deriv (axialTransitionProfile L) s)
  have hsupp : Function.support F ⊆ Ioo (-L) L := by
    intro s hs
    by_contra hnot
    exact hs (by simp [F, deriv_axialTransitionProfile_eq_zero_of_not_mem hL hnot])
  have hsupp' : Function.support F ⊆ Ioo (-R) R :=
    hsupp.trans (Ioo_subset_Ioo (neg_le_neg hLR) hLR)
  calc
    (∫⁻ s in Ioo (-R) R, F s) = ∫⁻ s, F s :=
      setLIntegral_eq_of_support_subset hsupp'
    _ = ∫⁻ s in Ioo (-L) L, F s :=
      (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ENNReal.ofReal κ := lintegral_ofReal_mul_deriv_axialTransitionProfile hL hκ

end PoincareConjecture
