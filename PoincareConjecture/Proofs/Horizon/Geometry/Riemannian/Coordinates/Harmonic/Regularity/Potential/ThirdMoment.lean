/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernelSchauderHigher.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Additional source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernelHigher.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: The heat-kernel moment and integrability helpers are specialized to the half-order
weight and local scaling conventions.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.HolderMoment
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.HigherDerivatives

noncomputable section
set_option autoImplicit false

open MeasureTheory Real Set
open scoped NNReal RealInnerProductSpace

namespace Poincare.Parabolic.Interior.Kernel

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def baseD3Half (x : V) : ℝ := Real.sqrt ‖x‖ * baseD3Maj x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD3Half_nonneg (x : V) : 0 ≤ baseD3Half x :=
  mul_nonneg (Real.sqrt_nonneg _) (baseD3Maj_nonneg x)

private theorem baseD3First_int : Integrable (fun x : V => ‖x‖ * baseD3Maj x) := by
  have h4 := (gaussMoment_int (V := V) 4
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((8 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h2 := (gaussMoment_int (V := V) 2
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((3 / 4 : ℝ) * (baseHeatMass V)⁻¹)
  have heq : (fun x : V => ‖x‖ * baseD3Maj x) = fun x : V =>
      ((8 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 4 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((3 / 4 : ℝ) * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 2 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD3Maj baseHeat
    ring
  rw [heq]
  exact h4.add h2

theorem baseD3Half_int : Integrable (baseD3Half : V → ℝ) := by
  have hmajor : Integrable (fun x : V => (1 + ‖x‖) * baseD3Maj x) := by
    have heq : (fun x : V => (1 + ‖x‖) * baseD3Maj x) =
        (fun x : V => baseD3Maj x + ‖x‖ * baseD3Maj x) := by
      funext x
      ring
    rw [heq]
    exact (baseD3Maj_int (V := V)).add (baseD3First_int (V := V))
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold baseD3Half baseD3Maj baseHeat baseHeatMass
    fun_prop
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseD3Half_nonneg x)]
  have hroot : Real.sqrt ‖x‖ ≤ 1 + ‖x‖ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [norm_nonneg x]⟩
  exact mul_le_mul_of_nonneg_right hroot (baseD3Maj_nonneg x)

def heatC3Half (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD3Half x

omit [Nontrivial V] in
theorem heatC3Half_nonneg : 0 ≤ heatC3Half V := integral_nonneg baseD3Half_nonneg

def heatD3Half (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * t⁻¹ * (heatScale t)⁻¹ *
    Real.sqrt (heatScale t) * baseD3Half ((heatScale t)⁻¹ • x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3Half_nonneg {t : ℝ} (ht : 0 < t) (x : V) : 0 ≤ heatD3Half t x := by
  unfold heatD3Half
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
          (inv_nonneg.mpr ht.le))
        (inv_nonneg.mpr (heatScale_pos ht).le)) (Real.sqrt_nonneg _))
    (baseD3Half_nonneg _)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3Half_eq {t : ℝ} (ht : 0 < t) (x : V) :
    heatD3Half t x = Real.sqrt ‖x‖ * heatD3Maj t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by simp [hr.ne']
  have hroot : Real.sqrt ‖x‖ =
      Real.sqrt (heatScale t) * Real.sqrt ‖(heatScale t)⁻¹ • x‖ := by
    calc
      Real.sqrt ‖x‖ = Real.sqrt ‖heatScale t • ((heatScale t)⁻¹ • x)‖ :=
        congrArg (fun z : V => Real.sqrt ‖z‖) hx
      _ = Real.sqrt (heatScale t * ‖(heatScale t)⁻¹ • x‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = _ := Real.sqrt_mul hr.le _
  have hsquare : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  have hscale : t⁻¹ = (heatScale t)⁻¹ * (heatScale t)⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsquare]
  unfold heatD3Half heatD3Maj baseD3Half
  rw [hroot, hscale]
  ring

theorem heatD3Half_int {t : ℝ} (ht : 0 < t) : Integrable (heatD3Half t : V → ℝ) := by
  unfold heatD3Half
  exact (baseD3Half_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

private theorem third_half_scale {t : ℝ} (ht : 0 < t) :
    t⁻¹ * (heatScale t)⁻¹ * Real.sqrt (heatScale t) = t ^ (-(5 : ℝ) / 4) := by
  calc
    _ = t ^ (-1 : ℝ) * (t ^ (1 / 2 : ℝ)) ^ (-1 : ℝ) *
        (t ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
      simp only [Real.rpow_neg_one, Real.sqrt_eq_rpow, heatScale]
    _ = _ := by
      rw [← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
        ← Real.rpow_add ht, ← Real.rpow_add ht]
      norm_num

omit [Nontrivial V] in

theorem integral_heatD3Half {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD3Half t x = t ^ (-(5 : ℝ) / 4) * heatC3Half V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hscaled : (∫ x : V, heatD3Half t x) =
      (t⁻¹ * (heatScale t)⁻¹ * Real.sqrt (heatScale t)) * heatC3Half V := by
    unfold heatD3Half heatC3Half
    rw [integral_const_mul,
      Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD3Half hr.le]
    simp only [smul_eq_mul]
    field_simp [hr.ne']
  rw [hscaled, third_half_scale ht]

theorem integrable_half_weight_heatD3Maj {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : V => ‖x‖ ^ (1 / 2 : ℝ) * heatD3Maj t x) := by
  have heq : (heatD3Half t : V → ℝ) =
      (fun x : V => ‖x‖ ^ (1 / 2 : ℝ) * heatD3Maj t x) := by
    funext x
    rw [heatD3Half_eq ht, Real.sqrt_eq_rpow]
  rw [← heq]
  exact heatD3Half_int ht

omit [Nontrivial V] in

theorem integral_half_weight_heatD3Maj {t : ℝ} (ht : 0 < t) :
    (∫ x : V, ‖x‖ ^ (1 / 2 : ℝ) * heatD3Maj t x) =
      t ^ (-(5 : ℝ) / 4) * heatC3Half V := by
  simpa only [heatD3Half_eq ht, Real.sqrt_eq_rpow] using (integral_heatD3Half (V := V) ht)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3_half_bound {t : ℝ} (ht : 0 < t) (u v w x : V) :
    ‖heatD3 t u v w x‖ * Real.sqrt ‖x‖ ≤
      ‖u‖ * ‖v‖ * ‖w‖ * heatD3Half t x := by
  rw [heatD3Half_eq ht]
  exact (mul_le_mul_of_nonneg_right (heatD3_bound ht u v w x)
    (Real.sqrt_nonneg _)).trans_eq (by ring)

theorem heatD3_int {t : ℝ} (ht : 0 < t) (u v w : V) : Integrable (heatD3 t u v w) := by
  refine ((heatD3Maj_int (V := V) ht).const_mul (‖u‖ * ‖v‖ * ‖w‖)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  · exact Filter.Eventually.of_forall (heatD3_bound ht u v w)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3_neg (t : ℝ) (u v w x : V) :
    heatD3 t u v w (-x) = -heatD3 t u v w x := by
  simp only [heatD3, smul_neg, baseD3, inner_neg_left, baseHeat, norm_neg]
  ring

omit [Nontrivial V] in

theorem integral_heatD3_zero (t : ℝ) (u v w : V) : ∫ x : V, heatD3 t u v w x = 0 := by
  have h := integral_neg_eq_self (heatD3 t u v w) (volume : Measure V)
  simp_rw [heatD3_neg, integral_neg] at h
  linarith

section Source

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [CompleteSpace F] in
theorem norm_heatD3_smul_le_of_centered_half_bound
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t) {f : V → F}
    (hf : ∀ y, ‖f y‖ ≤ K * Real.sqrt ‖y‖) (u v w y : V) :
    ‖heatD3 t u v w y • f y‖ ≤
      (‖u‖ * ‖v‖ * ‖w‖ * K) * heatD3Half t y := by
  calc
    _ = ‖heatD3 t u v w y‖ * ‖f y‖ := norm_smul _ _
    _ ≤ ‖heatD3 t u v w y‖ * (K * Real.sqrt ‖y‖) :=
      mul_le_mul_of_nonneg_left (hf y) (norm_nonneg _)
    _ = K * (‖heatD3 t u v w y‖ * Real.sqrt ‖y‖) := by ring
    _ ≤ K * (‖u‖ * ‖v‖ * ‖w‖ * heatD3Half t y) :=
      mul_le_mul_of_nonneg_left (heatD3_half_bound ht u v w y) hK
    _ = _ := by ring

omit [CompleteSpace F] in
theorem integrable_heatD3_smul_of_centered_half_bound
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t) {f : V → F}
    (hm : AEStronglyMeasurable f) (hf : ∀ y, ‖f y‖ ≤ K * Real.sqrt ‖y‖)
    (u v w : V) : Integrable (fun y => heatD3 t u v w y • f y) := by
  refine ((heatD3Half_int ht).const_mul (‖u‖ * ‖v‖ * ‖w‖ * K)).mono' ?_ ?_
  · exact (heatD3_int ht u v w).aestronglyMeasurable.smul hm
  · exact Filter.Eventually.of_forall (norm_heatD3_smul_le_of_centered_half_bound hK ht hf u v w)

omit [CompleteSpace F] in

theorem norm_integral_heatD3_smul_le_of_centered_half_bound
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t) {f : V → F}
    (hf : ∀ y, ‖f y‖ ≤ K * Real.sqrt ‖y‖) (u v w : V) :
    ‖∫ y, heatD3 t u v w y • f y‖ ≤
      ‖u‖ * ‖v‖ * ‖w‖ * K * t ^ (-(5 : ℝ) / 4) * heatC3Half V := by
  calc
    _ ≤ ∫ y, (‖u‖ * ‖v‖ * ‖w‖ * K) * heatD3Half t y :=
      norm_integral_le_of_norm_le ((heatD3Half_int ht).const_mul _)
        (Filter.Eventually.of_forall (norm_heatD3_smul_le_of_centered_half_bound hK ht hf u v w))
    _ = _ := by rw [integral_const_mul, integral_heatD3Half ht]; ring

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem half_holder_centered_bound {K : ℝ≥0} {f : V → F}
    (hf : HolderWith K (1 / 2) f) (x y : V) :
    ‖f (x - y) - f x‖ ≤ (K : ℝ) * Real.sqrt ‖y‖ := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have heq : (x - y) - x = -y := by abel
    rw [heq, norm_neg]
  have h := hf.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    Real.sqrt_eq_rpow] using h

def heatD3Cancel (t : ℝ) (u v w : V) (f : V → F) (x : V) : F :=
  ∫ y, heatD3 t u v w y • (f (x - y) - f x)

def heatD3Conv (t : ℝ) (u v w : V) (f : V → F) (x : V) : F :=
  ∫ y, heatD3 t u v w y • f (x - y)

omit [CompleteSpace F] in
theorem heatD3Cancel_int_of_half_holder {K : ℝ≥0} {t : ℝ} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K (1 / 2) f) (u v w x : V) :
    Integrable (fun y => heatD3 t u v w y • (f (x - y) - f x)) := by
  have hfcont := hf.continuous (by norm_num : (0 : ℝ≥0) < 1 / 2)
  exact integrable_heatD3_smul_of_centered_half_bound K.coe_nonneg ht
    ((hfcont.comp (continuous_const.sub continuous_id)).sub continuous_const).aestronglyMeasurable
    (half_holder_centered_bound hf x) u v w

omit [CompleteSpace F] in
theorem heatD3Conv_int_of_half_holder {K : ℝ≥0} {t : ℝ} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K (1 / 2) f) (u v w x : V) :
    Integrable (fun y => heatD3 t u v w y • f (x - y)) := by
  have hc := heatD3Cancel_int_of_half_holder ht hf u v w x
  have hk := (heatD3_int ht u v w).smul_const (f x)
  refine (hc.add hk).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, smul_sub, sub_add_cancel]

theorem heatD3Conv_eq_cancel_of_half_holder {K : ℝ≥0} {t : ℝ} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K (1 / 2) f) (u v w x : V) :
    heatD3Conv t u v w f x = heatD3Cancel t u v w f x := by
  have hc := heatD3Cancel_int_of_half_holder ht hf u v w x
  have hk := (heatD3_int ht u v w).smul_const (f x)
  unfold heatD3Conv heatD3Cancel
  calc
    _ = ∫ y, heatD3 t u v w y • (f (x - y) - f x) + heatD3 t u v w y • f x := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [smul_sub, sub_add_cancel]
    _ = (∫ y, heatD3 t u v w y • (f (x - y) - f x)) +
        ∫ y, heatD3 t u v w y • f x := integral_add hc hk
    _ = _ := by
      rw [integral_smul_const, integral_heatD3_zero, zero_smul, add_zero]

omit [CompleteSpace F] in
theorem heatD3Cancel_norm_of_half_holder {K : ℝ≥0} {t : ℝ} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K (1 / 2) f) (u v w x : V) :
    ‖heatD3Cancel t u v w f x‖ ≤
      ‖u‖ * ‖v‖ * ‖w‖ * (K : ℝ) * t ^ (-(5 : ℝ) / 4) * heatC3Half V :=
  norm_integral_heatD3_smul_le_of_centered_half_bound K.coe_nonneg ht
    (half_holder_centered_bound hf x) u v w

theorem exists_uniform_heatD3_half_holder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ≥0) (f : V → F), HolderWith K (1 / 2) f →
      ∀ t : ℝ, 0 < t → ∀ u v w x : V,
        ‖heatD3Conv t u v w f x‖ ≤ C * (K : ℝ) * t ^ (-(5 : ℝ) / 4) *
          ‖u‖ * ‖v‖ * ‖w‖ := by
  refine ⟨heatC3Half V, heatC3Half_nonneg, fun K f hf t ht u v w x => ?_⟩
  rw [heatD3Conv_eq_cancel_of_half_holder ht hf]
  exact (heatD3Cancel_norm_of_half_holder ht hf u v w x).trans_eq (by ring)

end Source
end Poincare.Parabolic.Interior.Kernel
