import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactRepresentation
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.PotentialRealization
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.CenteredRealization
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.SeparatedEstimate

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Filter MeasureTheory Set
open scoped ContDiff Topology NNReal

namespace Poincare.Parabolic.Interior

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem continuous_heatScaled_compactSlice {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (t : ℝ) (x : V) :
    Continuous (fun s => Kernel.heatScaled (t - s) (compactSlice f hf.continuous hc s) x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact Kernel.tendsto_heatScaled_of_tendsto
    (continuous_const.sub continuous_id).continuousAt
    (continuous_compactSlice hf hc).continuousAt x

omit [Nontrivial V] [CompleteSpace F] in
theorem heatDuh_eq_integral_heatScaled {t : ℝ} (ht : 0 < t)
    (f : ℝ → BoundedContinuousFunction V F) (x : V) :
    Kernel.heatDuh t f x = ∫ s in (0 : ℝ)..t, Kernel.heatScaled (t - s) (f s) x := by
  unfold Kernel.heatDuh
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hst
  intro hs
  rw [uIoc_of_le ht.le] at hs
  exact Kernel.heatSup_scaled (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (f s) x

omit [CompleteSpace F] in
theorem hasFDerivAt_heatDuh_compactSlice {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (x : V) :
    HasFDerivAt (Kernel.heatDuh t (compactSlice f hf.continuous hc))
      (Kernel.heatDuh t (compactSlice (spatialDerivative f)
        (contDiff_spatialDerivative hf).continuous (hasCompactSupport_spatialDerivative hc)) x)
      x := by
  let u := compactSlice f hf.continuous hc
  let du := compactSlice (spatialDerivative f) (contDiff_spatialDerivative hf).continuous
    (hasCompactSupport_spatialDerivative hc)
  obtain ⟨K, hK⟩ := (hasCompactSupport_spatialDerivative hc).exists_bound_of_continuous
    (contDiff_spatialDerivative hf).continuous
  have hdu (s : ℝ) : ‖du s‖ ≤ max 0 K := by
    apply (BoundedContinuousFunction.norm_le (le_max_left 0 K)).mpr
    intro y
    exact (hK (y, s)).trans (le_max_right 0 K)
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y s => Kernel.heatScaled (t - s) (u s) y)
    (F' := fun y s => Kernel.heatScaled (t - s) (du s) y)
    (bound := fun _ => max 0 K) (s := (univ : Set V)) (μ := volume)
    univ_mem
    (Eventually.of_forall fun y =>
      (continuous_heatScaled_compactSlice hf hc t y).aestronglyMeasurable)
    ((continuous_heatScaled_compactSlice hf hc t x).intervalIntegrable 0 t)
    (continuous_heatScaled_compactSlice (contDiff_spatialDerivative hf)
      (hasCompactSupport_spatialDerivative hc) t x).aestronglyMeasurable
    (Eventually.of_forall fun s _ y _ => (Kernel.heatScaled_norm (t - s) (du s) y).trans
      (hdu s))
    intervalIntegrable_const
    (Eventually.of_forall fun s _ y _ => Kernel.heatScaled_space (t - s) (u s) (du s)
      (fun z => hasFDerivAt_spatialSlice (hf.differentiable (by simp)) z s) y)
  simpa only [← heatDuh_eq_integral_heatScaled ht, u, du] using h

omit [CompleteSpace F] in
theorem fderiv_fderiv_heatDuh_compactSlice {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (x : V) :
    fderiv ℝ (fun y => fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) y) x =
      Kernel.heatDuh t (compactSlice (spatialDerivative (spatialDerivative f))
        (contDiff_spatialDerivative (contDiff_spatialDerivative hf)).continuous
        (hasCompactSupport_spatialDerivative (hasCompactSupport_spatialDerivative hc))) x := by
  simp only [(hasFDerivAt_heatDuh_compactSlice hf hc ht _).fderiv]
  exact (hasFDerivAt_heatDuh_compactSlice (contDiff_spatialDerivative hf)
    (hasCompactSupport_spatialDerivative hc) ht x).fderiv

omit [CompleteSpace F] in
theorem heatSupGradient_eq_heatScaled_derivative {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    Kernel.heatSupGradient t u x = Kernel.heatScaled t du x := by
  have heq : Kernel.heatSup t u = fun y => Kernel.heatScaled t u y :=
    funext fun y => Kernel.heatSup_scaled ht u y
  have h := Kernel.heatSup_hasFDerivAt ht u x
  rw [heq] at h
  exact h.unique (Kernel.heatScaled_space t u du hu x)

omit [CompleteSpace F] in
theorem heatSupHessian_eq_heatScaled_derivative {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (ddu : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : V → V →L[ℝ] F) (ddu x) x) (x : V) :
    Kernel.heatSupHessian t u x = Kernel.heatScaled t ddu x := by
  have heq : Kernel.heatSupGradient t u = fun y => Kernel.heatScaled t du y :=
    funext fun y => heatSupGradient_eq_heatScaled_derivative ht u du hu y
  have h := Kernel.heatSupGradient_hasFDerivAt ht u x
  rw [heq] at h
  exact h.unique (Kernel.heatScaled_space t du ddu hdu x)

omit [CompleteSpace F] in
theorem fderiv_fderiv_heatDuh_eq_heatD2Duh {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t)
    (x v w : V) :
    fderiv ℝ (fun y => fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) y)
      x v w = Kernel.heatD2Duh t w v (fun s y => f (y, s)) x := by
  let u := compactSlice f hf.continuous hc
  let du := compactSlice (spatialDerivative f) (contDiff_spatialDerivative hf).continuous
    (hasCompactSupport_spatialDerivative hc)
  let ddu := compactSlice (spatialDerivative (spatialDerivative f))
    (contDiff_spatialDerivative (contDiff_spatialDerivative hf)).continuous
    (hasCompactSupport_spatialDerivative (hasCompactSupport_spatialDerivative hc))
  have hcont : Continuous (fun s => Kernel.heatScaled (t - s) (ddu s) x) :=
    continuous_heatScaled_compactSlice
      (contDiff_spatialDerivative (contDiff_spatialDerivative hf))
      (hasCompactSupport_spatialDerivative (hasCompactSupport_spatialDerivative hc)) t x
  have hint := hcont.intervalIntegrable (μ := volume) 0 t
  rw [fderiv_fderiv_heatDuh_compactSlice hf hc ht, heatDuh_eq_integral_heatScaled ht]
  change (∫ s in (0 : ℝ)..t, Kernel.heatScaled (t - s) (ddu s) x) v w = _
  rw [ContinuousLinearMap.intervalIntegral_apply hint v]
  rw [ContinuousLinearMap.intervalIntegral_apply
    ((hcont.clm_apply continuous_const).intervalIntegrable 0 t) w]
  unfold Kernel.heatD2Duh
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hst
  intro hs
  rw [uIoc_of_le ht.le] at hs
  have hpos := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  rw [← heatSupHessian_eq_heatScaled_derivative hpos (u s) (du s) (ddu s)
    (fun y => hasFDerivAt_spatialSlice (hf.differentiable (by simp)) y s)
    (fun y => hasFDerivAt_spatialSlice
      ((contDiff_spatialDerivative hf).differentiable (by simp)) y s) x,
    Kernel.heatSupHessian_apply hpos]
  rfl

theorem norm_hessian_le_of_centered_heatResidual {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hzero : ∀ y, f (y, 0) = 0) {t K : ℝ} (ht : 0 < t)
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (x v w : V)
    (hsource : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y,
      ‖heatResidual f (y, s)‖ ≤ K * ‖y - x‖ ^ (α : ℝ)) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x v w‖ ≤
      (‖v‖ * ‖w‖ * K * Kernel.heatC2Holder (V := V) α) *
        ((2 / (α : ℝ)) * t ^ ((α : ℝ) / 2)) := by
  have hrep : (fun z => f (z, t)) = Kernel.heatDuh t
      (compactSlice (heatResidual f) (contDiff_heatResidual hf).continuous
        (hasCompactSupport_heatResidual hc)) := by
    funext z
    exact (heatDuh_compactSlice_residual hf hc hzero ht z).symm
  rw [hrep, fderiv_fderiv_heatDuh_eq_heatD2Duh (contDiff_heatResidual hf)
    (hasCompactSupport_heatResidual hc) ht, Kernel.heatD2Duh_comm t w v]
  exact Kernel.norm_heatD2Duh_le_of_centered_bound hα0 hα1 ht
    (fun s y => heatResidual f (y, s)) x hsource v w

theorem norm_hessian_le_of_centered_add_time_gap_heatResidual {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hzero : ∀ y, f (y, 0) = 0) {t K Q δ : ℝ} (ht : 0 < t)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hδ : 0 < δ)
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (x v w : V)
    (hsource : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y,
      ‖heatResidual f (y, s)‖ ≤ K * ‖y - x‖ ^ (α : ℝ) + Q)
    (hlate : ∀ s ∈ Ioo (0 : ℝ) t, t - δ < s → ∀ y,
      ‖heatResidual f (y, s)‖ ≤ K * ‖y - x‖ ^ (α : ℝ)) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x v w‖ ≤
      (‖v‖ * ‖w‖ * K * Kernel.heatC2Holder (V := V) α) *
        ((2 / (α : ℝ)) * t ^ ((α : ℝ) / 2)) +
      (‖v‖ * ‖w‖ * Q * δ⁻¹ * Kernel.heatC2 V) * t := by
  have hrep : (fun z => f (z, t)) = Kernel.heatDuh t
      (compactSlice (heatResidual f) (contDiff_heatResidual hf).continuous
        (hasCompactSupport_heatResidual hc)) := by
    funext z
    exact (heatDuh_compactSlice_residual hf hc hzero ht z).symm
  rw [hrep, fderiv_fderiv_heatDuh_eq_heatD2Duh (contDiff_heatResidual hf)
    (hasCompactSupport_heatResidual hc) ht, Kernel.heatD2Duh_comm t w v]
  unfold Kernel.heatD2Duh Kernel.heatD2Conv
  apply Kernel.norm_hessian_potential_le_of_centered_add_time_gap hα0 hα1 hK hQ hδ ht
  · intro s hs y
    simpa only [sub_sub_cancel_left, norm_neg] using hsource s hs (x - y)
  · intro s hs hgap y
    simpa only [sub_sub_cancel_left, norm_neg] using hlate s hs hgap (x - y)

end Poincare.Parabolic.Interior
