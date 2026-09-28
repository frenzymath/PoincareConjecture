import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.CenteredEstimate
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.PotentialRealization








set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_heatD2Duh_le_of_centered_bound
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) {K t : ℝ}
    (ht : 0 < t) (f : ℝ → V → F) (x : V)
    (hf : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y, ‖f s y‖ ≤ K * ‖y - x‖ ^ (α : ℝ))
    (v w : V) :
    ‖heatD2Duh t v w f x‖ ≤
      (‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α) *
        ((2 / (α : ℝ)) * t ^ ((α : ℝ) / 2)) := by
  unfold heatD2Duh heatD2Conv
  apply norm_hessian_potential_le_of_centered_bound hα0 hα1 ht
  intro s hs y
  simpa only [sub_sub_cancel_left, norm_neg] using hf s hs (x - y)



theorem norm_fderiv_fderiv_heatDuh_le_of_centered_bound
    {α L B : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) {K t : ℝ}
    (ht : 0 < t) (f : ℝ → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : ℝ) t, ‖f s‖ ≤ B)
    (hholder : ∀ s ∈ Icc (0 : ℝ) t, HolderWith L α (f s))
    (hmeas0 : ∀ z : V, AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) z) (volume.restrict (uIoc (0 : ℝ) t)))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : ℝ => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : ℝ) t)))
    (hmeas2 : ∀ z : V, AEStronglyMeasurable
      (fun s : ℝ => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : ℝ) t)))
    (x : V)
    (hcenter : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y,
      ‖f s y‖ ≤ K * ‖y - x‖ ^ (α : ℝ)) (v w : V) :
    ‖fderiv ℝ (fun z => fderiv ℝ (heatDuh t f) z) x v w‖ ≤
      (‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α) *
        ((2 / (α : ℝ)) * t ^ ((α : ℝ) / 2)) := by
  have hgrad : fderiv ℝ (heatDuh t f) = heatDuhGradientMap t f := by
    funext z
    exact (heatDuh_hasFDerivAt ht f hbound hmeas0 hmeas1 z).fderiv
  change ‖fderiv ℝ (fderiv ℝ (heatDuh t f)) x v w‖ ≤ _
  rw [hgrad, (heatDuhGradientMap_hasFDerivAt hα0 hα1 ht f hbound hholder
    hmeas1 hmeas2 x).fderiv,
    heatDuhHessian_apply hα0 hα1 ht f hbound hholder hmeas1 hmeas2 x v w,
    heatD2Duh_comm t w v]
  exact norm_heatD2Duh_le_of_centered_bound hα0 hα1 ht (fun s => f s) x hcenter v w

end Poincare.Parabolic.Interior.Kernel
