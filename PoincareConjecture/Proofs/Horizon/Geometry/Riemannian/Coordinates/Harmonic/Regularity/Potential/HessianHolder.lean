import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.HessianDifference
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.ScaleSplit
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactPotential










noncomputable section
set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ContDiff Topology NNReal

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]



theorem heatD2Duh_sub_integrable_and_norm_le_halfHolder {t : ℝ} (ht : 0 < t)
    {K : ℝ≥0} (f : ℝ → V → F)
    (hf : ∀ s ∈ Icc (0 : ℝ) t, HolderWith K (1 / 2) (f s))
    (hc : ∀ s ∈ Icc (0 : ℝ) t, HasCompactSupport (f s))
    (v w : V)
    (hmeas : ∀ z, AEStronglyMeasurable
      (fun s : ℝ => heatD2Conv (t - s) v w (f s) z)
      (volume.restrict (uIoc (0 : ℝ) t))) (x y : V) :
    IntervalIntegrable
      (fun s : ℝ => heatD2Conv (t - s) v w (f s) x -
        heatD2Conv (t - s) v w (f s) y) volume 0 t ∧
    ‖heatD2Duh t v w f x - heatD2Duh t v w f y‖ ≤
      4 * (2 * heatC2Half V + heatC3Half V) * (K : ℝ) *
        ‖v‖ * ‖w‖ * Real.sqrt ‖x - y‖ := by
  have hx := heatD2Duh_int ht f hf v w x (hmeas x)
  have hy := heatD2Duh_int ht f hf v w y (hmeas y)
  refine ⟨hx.sub hy, ?_⟩
  by_cases hxy : x = y
  · subst y
    simp
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let H := fun τ : ℝ => heatD2Conv τ v w (f (t - τ)) x -
    heatD2Conv τ v w (f (t - τ)) y
  have hHi : IntervalIntegrable H volume 0 t := by
    simpa only [H, sub_zero, sub_self, sub_sub_cancel] using
      ((hx.sub hy).comp_sub_left t).symm
  have hHm : AEStronglyMeasurable H (volume.restrict (Ioo 0 t)) :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hHi).aestronglyMeasurable
  let A := 2 * heatC2Half V * (K : ℝ) * ‖v‖ * ‖w‖
  let B := heatC3Half V * (K : ℝ) * ‖v‖ * ‖w‖
  have hC2 := heatC2Half_nonneg (V := V)
  have hC3 := heatC3Half_nonneg (V := V)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hshort (τ) (hτ : τ ∈ Ioo 0 t) : ‖H τ‖ ≤ A * τ ^ (-(3 / 4 : ℝ)) := by
    have hs : t - τ ∈ Icc (0 : ℝ) t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    simpa only [H, A, neg_div] using
      heatD2Conv_sub_norm_le_uniform_half_holder (hf _ hs) hτ.1 v w x y
  have hlong (τ) (hτ : τ ∈ Ioo 0 t) :
      ‖H τ‖ ≤ B * ‖x - y‖ * τ ^ (-(5 / 4 : ℝ)) := by
    have hs : t - τ ∈ Icc (0 : ℝ) t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    exact (heatD2Conv_sub_norm_le_of_half_holder (hc _ hs) (hf _ hs)
      hτ.1 v w x y).trans_eq (by dsimp [B]; rw [neg_div]; ring)
  have hsplit := (norm_integral_le_halfPower_of_two_bounds ht hd hA hB hHm hshort hlong).2
  have hreverse : (∫ τ in 0..t, H τ) =
      ∫ s in 0..t, heatD2Conv (t - s) v w (f s) x -
        heatD2Conv (t - s) v w (f s) y := by
    simpa only [H, sub_zero, sub_self, sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left
        (fun s => heatD2Conv (t - s) v w (f s) x -
          heatD2Conv (t - s) v w (f s) y) t (a := 0) (b := t))
  unfold heatD2Duh
  rw [← intervalIntegral.integral_sub hx hy, ← hreverse]
  exact hsplit.trans_eq (by dsimp [A, B]; ring)

end Poincare.Parabolic.Interior.Kernel

namespace Poincare.Parabolic.Interior

private theorem hasCompactSupport_spaceSlice {V F : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup F] {f : V × ℝ → F}
    (hc : HasCompactSupport f) (s : ℝ) : HasCompactSupport (fun x => f (x, s)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_fst)
  intro x hx
  exact ⟨(x, s), subset_closure hx, rfl⟩

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in


theorem aestronglyMeasurable_heatD2Conv_compactSlice {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (v w x : V) :
    AEStronglyMeasurable
      (fun s : ℝ => Kernel.heatD2Conv (t - s) v w (fun z => f (z, s)) x)
      (volume.restrict (uIoc (0 : ℝ) t)) := by
  let u := compactSlice f hf.continuous hc
  let du := compactSlice (spatialDerivative f) (contDiff_spatialDerivative hf).continuous
    (hasCompactSupport_spatialDerivative hc)
  let ddu := compactSlice (spatialDerivative (spatialDerivative f))
    (contDiff_spatialDerivative (contDiff_spatialDerivative hf)).continuous
    (hasCompactSupport_spatialDerivative (hasCompactSupport_spatialDerivative hc))
  have hcont : Continuous (fun s => Kernel.heatScaled (t - s) (ddu s) x w v) :=
    ((continuous_heatScaled_compactSlice
      (contDiff_spatialDerivative (contDiff_spatialDerivative hf))
      (hasCompactSupport_spatialDerivative (hasCompactSupport_spatialDerivative hc)) t x).clm_apply
        continuous_const).clm_apply continuous_const
  apply hcont.aestronglyMeasurable.congr
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : ℝ) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  have hpos := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  rw [← heatSupHessian_eq_heatScaled_derivative hpos (u s) (du s) (ddu s)
    (fun y => hasFDerivAt_spatialSlice (hf.differentiable (by simp)) y s)
    (fun y => hasFDerivAt_spatialSlice
      ((contDiff_spatialDerivative hf).differentiable (by simp)) y s) x,
    Kernel.heatSupHessian_apply hpos]
  rfl



theorem norm_fderiv_fderiv_heatDuh_compactSlice_sub_le {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (hholder : ∀ s ∈ Icc (0 : ℝ) t, HolderWith K (1 / 2) (fun z => f (z, s)))
    (x y : V) :
    ‖fderiv ℝ (fun z => fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) z) x -
      fderiv ℝ (fun z => fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) z) y‖ ≤
      4 * (2 * Kernel.heatC2Half V + Kernel.heatC3Half V) * (K : ℝ) *
        Real.sqrt ‖x - y‖ := by
  have hC2 := Kernel.heatC2Half_nonneg (V := V)
  have hC3 := Kernel.heatC3Half_nonneg (V := V)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  simp only [sub_apply, fderiv_fderiv_heatDuh_eq_heatD2Duh hf hc ht]
  exact (Kernel.heatD2Duh_sub_integrable_and_norm_le_halfHolder ht
    (fun s z => f (z, s)) hholder (fun s _ => hasCompactSupport_spaceSlice hc s) w v
    (fun z => aestronglyMeasurable_heatD2Conv_compactSlice hf hc ht w v z) x y).2.trans_eq
      (by ring)

end Poincare.Parabolic.Interior
