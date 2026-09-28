import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactPotential
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ContDiff Topology NNReal

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem heatD2ConvMap_norm_le_of_bounded {t : ℝ} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD2ConvMap t v u x‖ ≤ ‖v‖ * t⁻¹ * heatC2 V * ‖u‖ := by
  have hC2 := heatC2_nonneg (V := V)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [heatD2ConvMap_apply ht]
  change ‖heatD2Sup t v w u x‖ ≤ _
  exact (heatD2Sup_norm ht v w u x).trans_eq (by ring)

theorem heatD1Sup_sub_norm_le_of_bounded {t : ℝ} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x y : V) :
    ‖heatD1Sup t v u x - heatD1Sup t v u y‖ ≤
      (‖v‖ * t⁻¹ * heatC2 V * ‖u‖) * ‖x - y‖ := by
  exact (convex_univ : Convex ℝ (univ : Set V)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (heatD1Sup_hasFDerivAt ht v u z).hasFDerivWithinAt)
    (fun z _ => heatD2ConvMap_norm_le_of_bounded ht v u z) (mem_univ y) (mem_univ x)

theorem heatD1Sup_sub_norm_le_halfHolder {t : ℝ} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x y : V) :
    ‖heatD1Sup t v u x - heatD1Sup t v u y‖ ≤
      (2 * heatC1 V + heatC2 V) * ‖v‖ * ‖u‖ *
        heatScale34 t * Real.sqrt ‖x - y‖ := by
  let c := (2 * heatC1 V + heatC2 V) * ‖v‖ * ‖u‖
  let N := ‖heatD1Sup t v u x - heatD1Sup t v u y‖
  have hC1 := heatC1_nonneg (V := V)
  have hC2 := heatC2_nonneg (V := V)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs12 : 0 ≤ heatScale12 t := Real.rpow_nonneg ht.le _
  have hs34 : 0 ≤ heatScale34 t := Real.rpow_nonneg ht.le _
  have hfirst : N ≤ c * heatScale12 t := by
    calc
      _ ≤ ‖heatD1Sup t v u x‖ + ‖heatD1Sup t v u y‖ := norm_sub_le _ _
      _ ≤ (‖v‖ * (heatScale t)⁻¹ * heatC1 V) * ‖u‖ +
          (‖v‖ * (heatScale t)⁻¹ * heatC1 V) * ‖u‖ :=
        add_le_add (heatD1Sup_norm ht v u x) (heatD1Sup_norm ht v u y)
      _ = (2 * heatC1 V) * ‖v‖ * ‖u‖ * heatScale12 t := by
        rw [heatScale12_eq ht]
        ring
      _ ≤ c * heatScale12 t := by
        dsimp [c]
        gcongr
        exact le_add_of_nonneg_right hC2
  have hsecond : N ≤ c * t⁻¹ * ‖x - y‖ := by
    calc
      _ ≤ (‖v‖ * t⁻¹ * heatC2 V * ‖u‖) * ‖x - y‖ :=
        heatD1Sup_sub_norm_le_of_bounded ht v u x y
      _ = heatC2 V * ‖v‖ * ‖u‖ * t⁻¹ * ‖x - y‖ := by ring
      _ ≤ c * t⁻¹ * ‖x - y‖ := by
        dsimp [c]
        gcongr
        exact le_add_of_nonneg_left (mul_nonneg (by norm_num) hC1)
  have hscale : heatScale12 t * t⁻¹ = heatScale34 t ^ 2 := by
    unfold heatScale12 heatScale34
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht, ← Real.rpow_mul_natCast ht.le]
    congr 1
    norm_num
  have hprod : N ^ 2 ≤ (c * heatScale12 t) * (c * t⁻¹ * ‖x - y‖) := by
    simpa only [pow_two] using mul_le_mul hfirst hsecond (norm_nonneg _) (mul_nonneg hc hs12)
  have heq : (c * heatScale34 t * Real.sqrt ‖x - y‖) ^ 2 =
      (c * heatScale12 t) * (c * t⁻¹ * ‖x - y‖) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (norm_nonneg _), ← hscale]
    ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg hc hs34) (Real.sqrt_nonneg _))).mp (hprod.trans_eq heq.symm)

theorem heatD1Duh_sub_norm_le_halfHolder {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : ℝ) t, ‖f s‖ ≤ K)
    (v : V)
    (hmeas : ∀ x, AEStronglyMeasurable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x)
      (volume.restrict (uIoc (0 : ℝ) t))) (x y : V) :
    ‖heatD1Duh t v f x - heatD1Duh t v f y‖ ≤
      4 * (2 * heatC1 V + heatC2 V) * t ^ (1 / 4 : ℝ) *
        (K : ℝ) * ‖v‖ * Real.sqrt ‖x - y‖ := by
  let c := (2 * heatC1 V + heatC2 V) * ‖v‖ * (K : ℝ) * Real.sqrt ‖x - y‖
  have hx := heatD1Duh_int ht f hf v x (hmeas x)
  have hy := heatD1Duh_int ht f hf v y (hmeas y)
  have hmajor : IntervalIntegrable (fun s => c * heatScale34 (t - s)) volume 0 t :=
    scale34_intble.const_mul c
  unfold heatD1Duh
  rw [← intervalIntegral.integral_sub hx hy]
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, ‖heatD1Sup (t - s) v (f s) x -
        heatD1Sup (t - s) v (f s) y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, c * heatScale34 (t - s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le (hx.sub hy).norm hmajor
      intro s hs
      have hpos : 0 < t - s := sub_pos.mpr hs.2
      have hC1 := heatC1_nonneg (V := V)
      have hC2 := heatC2_nonneg (V := V)
      have hC : 0 ≤ 2 * heatC1 V + heatC2 V := by
        positivity
      have hs34 : 0 ≤ heatScale34 (t - s) := Real.rpow_nonneg hpos.le _
      calc
        _ ≤ (2 * heatC1 V + heatC2 V) * ‖v‖ * ‖f s‖ *
            heatScale34 (t - s) * Real.sqrt ‖x - y‖ :=
          heatD1Sup_sub_norm_le_halfHolder hpos v (f s) x y
        _ ≤ (2 * heatC1 V + heatC2 V) * ‖v‖ * (K : ℝ) *
            heatScale34 (t - s) * Real.sqrt ‖x - y‖ := by
          gcongr
          exact hf s ⟨hs.1.le, hs.2.le⟩
        _ = _ := by dsimp [c]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, timeScale34_int]
      dsimp [c]
      ring

end Poincare.Parabolic.Interior.Kernel

namespace Poincare.Parabolic.Interior

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem aestronglyMeasurable_heatD1Sup_compactSlice {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (v x : V) :
    AEStronglyMeasurable
      (fun s : ℝ => Kernel.heatD1Sup (t - s) v (compactSlice f hf.continuous hc s) x)
      (volume.restrict (uIoc (0 : ℝ) t)) := by
  let du := compactSlice (spatialDerivative f) (contDiff_spatialDerivative hf).continuous
    (hasCompactSupport_spatialDerivative hc)
  have hcont : Continuous (fun s => Kernel.heatScaled (t - s) (du s) x v) :=
    (continuous_heatScaled_compactSlice (contDiff_spatialDerivative hf)
      (hasCompactSupport_spatialDerivative hc) t x).clm_apply continuous_const
  apply hcont.aestronglyMeasurable.congr
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : ℝ) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  have hpos := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  rw [← heatSupGradient_eq_heatScaled_derivative hpos
    (compactSlice f hf.continuous hc s) (du s)
    (fun z => hasFDerivAt_spatialSlice (hf.differentiable (by simp)) z s) x,
    Kernel.heatSupGradient_apply hpos]

theorem fderiv_heatDuh_compactSlice_apply {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (x v : V) :
    fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) x v =
      Kernel.heatD1Duh t v (compactSlice f hf.continuous hc) x := by
  let du := compactSlice (spatialDerivative f) (contDiff_spatialDerivative hf).continuous
    (hasCompactSupport_spatialDerivative hc)
  have hcont : Continuous (fun s => Kernel.heatScaled (t - s) (du s) x) :=
    continuous_heatScaled_compactSlice (contDiff_spatialDerivative hf)
      (hasCompactSupport_spatialDerivative hc) t x
  rw [(hasFDerivAt_heatDuh_compactSlice hf hc ht x).fderiv,
    heatDuh_eq_integral_heatScaled ht]
  change (∫ s in (0 : ℝ)..t, Kernel.heatScaled (t - s) (du s) x) v = _
  rw [ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable 0 t) v]
  unfold Kernel.heatD1Duh
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hst
  intro hs
  rw [uIoc_of_le ht.le] at hs
  have hpos := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  rw [← heatSupGradient_eq_heatScaled_derivative hpos
    (compactSlice f hf.continuous hc s) (du s)
    (fun z => hasFDerivAt_spatialSlice (hf.differentiable (by simp)) z s) x,
    Kernel.heatSupGradient_apply hpos]

theorem norm_fderiv_heatDuh_compactSlice_sub_le {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (hbound : ∀ s ∈ Icc (0 : ℝ) t, ∀ x, ‖f (x, s)‖ ≤ K) (x y : V) :
    ‖fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) x -
      fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) y‖ ≤
      4 * (2 * Kernel.heatC1 V + Kernel.heatC2 V) * t ^ (1 / 4 : ℝ) *
        (K : ℝ) * Real.sqrt ‖x - y‖ := by
  have hC1 := Kernel.heatC1_nonneg (V := V)
  have hC2 := Kernel.heatC2_nonneg (V := V)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [sub_apply, fderiv_heatDuh_compactSlice_apply hf hc ht]
  have hnorm (s) (hs : s ∈ Icc (0 : ℝ) t) : ‖compactSlice f hf.continuous hc s‖ ≤ K :=
    (BoundedContinuousFunction.norm_le K.coe_nonneg).mpr (hbound s hs)
  exact (Kernel.heatD1Duh_sub_norm_le_halfHolder ht (compactSlice f hf.continuous hc)
    hnorm v (fun z => aestronglyMeasurable_heatD1Sup_compactSlice hf hc ht v z) x y).trans_eq
      (by ring)

theorem exists_uniform_heat_potential_gradient_halfHolder {T : ℝ} (_hT : 0 < T) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {f : V × ℝ → F} (hf : ContDiff ℝ ∞ f)
      (hc : HasCompactSupport f) {t : ℝ}, 0 < t → t ≤ T → ∀ {K : ℝ≥0},
      (∀ s ∈ Icc (0 : ℝ) t, ∀ x, ‖f (x, s)‖ ≤ K) → ∀ x y : V,
      ‖fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) x -
        fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) y‖ ≤
        C * (K : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  let C := max 1 (4 * (2 * Kernel.heatC1 V + Kernel.heatC2 V) * T ^ (1 / 4 : ℝ))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro f hf hc t ht htT K hbound x y
  have hC1 := Kernel.heatC1_nonneg (V := V)
  have hC2 := Kernel.heatC2_nonneg (V := V)
  have htime : t ^ (1 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow ht.le htT (by norm_num)
  rw [← Real.sqrt_eq_rpow]
  calc
    _ ≤ 4 * (2 * Kernel.heatC1 V + Kernel.heatC2 V) * t ^ (1 / 4 : ℝ) *
        (K : ℝ) * Real.sqrt ‖x - y‖ :=
      norm_fderiv_heatDuh_compactSlice_sub_le hf hc ht hbound x y
    _ ≤ (4 * (2 * Kernel.heatC1 V + Kernel.heatC2 V) * T ^ (1 / 4 : ℝ)) *
        (K : ℝ) * Real.sqrt ‖x - y‖ := by gcongr
    _ ≤ C * (K : ℝ) * Real.sqrt ‖x - y‖ := by
      gcongr
      exact le_max_right _ _

end Poincare.Parabolic.Interior
