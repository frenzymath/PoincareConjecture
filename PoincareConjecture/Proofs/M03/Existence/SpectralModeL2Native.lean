import PoincareConjecture.Proofs.M03.Existence.SpectralModeNative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace PoincareConjecture

theorem absolutelyContinuousOnInterval_spectralMode
    {lambda c T : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T) :
    AbsolutelyContinuousOnInterval (spectralMode lambda c f) 0 T := by
  have he : Continuous (fun s : ℝ => Real.exp (lambda * s)) := by fun_prop
  have hi := hf.continuousOn_mul he.continuousOn
  have hprimitive := hi.absolutelyContinuousOnInterval_intervalIntegral
    (c := (0 : ℝ)) (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => c)
      (uIcc (0 : ℝ) T)).absolutelyContinuousOnInterval
  have hdecay : AbsolutelyContinuousOnInterval
      (fun s : ℝ => Real.exp (-lambda * s)) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  exact hdecay.fun_mul (hconst.fun_add hprimitive)

theorem ae_hasDerivAt_spectralMode
    {lambda c T : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T) :
    ∀ᵐ t, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (spectralMode lambda c f)
        (f t - lambda * spectralMode lambda c f t) t := by
  have he : Continuous (fun s : ℝ => Real.exp (lambda * s)) := by fun_prop
  have hi := hf.continuousOn_mul he.continuousOn
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
  have hprimitive := (hasDerivAt_const t c).add (ht hmem 0 (by simp))
  have hdecay : HasDerivAt (fun s : ℝ => Real.exp (-lambda * s))
      (-lambda * Real.exp (-lambda * t)) t := by
    have h := ((hasDerivAt_id t).const_mul (-lambda)).exp
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  have hp := hdecay.mul hprimitive
  change HasDerivAt (spectralMode lambda c f) _ t at hp
  apply hp.congr_deriv
  have hcancel : Real.exp (-lambda * t) * Real.exp (lambda * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  dsimp only [spectralMode]
  calc
    -lambda * Real.exp (-lambda * t) *
          (c + ∫ s in (0 : ℝ)..t, Real.exp (lambda * s) * f s) +
        Real.exp (-lambda * t) * (0 + Real.exp (lambda * t) * f t) =
      -lambda * (Real.exp (-lambda * t) *
          (c + ∫ s in (0 : ℝ)..t, Real.exp (lambda * s) * f s)) +
        (Real.exp (-lambda * t) * Real.exp (lambda * t)) * f t := by ring
    _ = f t - lambda * (Real.exp (-lambda * t) *
          (c + ∫ s in (0 : ℝ)..t, Real.exp (lambda * s) * f s)) := by
      rw [hcancel]
      ring

theorem intervalIntegrable_spectralMode_defect_sq
    {lambda c T : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 T) :
    IntervalIntegrable
      (fun t => (f t - lambda * spectralMode lambda c f t) ^ 2) volume 0 T := by
  have hu := (absolutelyContinuousOnInterval_spectralMode
    (lambda := lambda) (c := c) hf).continuousOn
  have hcross : IntervalIntegrable
      (fun t => 2 * lambda * spectralMode lambda c f t * f t) volume 0 T :=
    hf.continuousOn_mul (continuousOn_const.mul hu)
  have hA : IntervalIntegrable
      (fun t => (lambda * spectralMode lambda c f t) ^ 2) volume 0 T :=
    ((continuousOn_const.mul hu).pow 2).intervalIntegrable
  apply ((hf2.sub hcross).add hA).congr
  intro t ht
  ring

theorem spectralMode_energy_identity_of_integrable
    {lambda c T : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T, (f t - lambda * spectralMode lambda c f t) ^ 2) +
        (∫ t in (0 : ℝ)..T, (lambda * spectralMode lambda c f t) ^ 2) +
        lambda * spectralMode lambda c f T ^ 2 =
      (∫ t in (0 : ℝ)..T, f t ^ 2) + lambda * c ^ 2 := by
  let u := spectralMode lambda c f
  have huAC : AbsolutelyContinuousOnInterval u 0 T :=
    absolutelyContinuousOnInterval_spectralMode hf
  have hu := huAC.continuousOn
  have hdu : IntervalIntegrable (fun t => f t - lambda * u t) volume 0 T :=
    hf.sub ((continuousOn_const.mul hu).intervalIntegrable)
  have hD : IntervalIntegrable (fun t => (f t - lambda * u t) ^ 2) volume 0 T :=
    intervalIntegrable_spectralMode_defect_sq hf hf2
  have hA : IntervalIntegrable (fun t => (lambda * u t) ^ 2) volume 0 T :=
    ((continuousOn_const.mul hu).pow 2).intervalIntegrable
  have hR : IntervalIntegrable
      (fun t => 2 * lambda * u t * (f t - lambda * u t)) volume 0 T :=
    hdu.continuousOn_mul (continuousOn_const.mul hu)
  have hqAC : AbsolutelyContinuousOnInterval (fun t => lambda * u t ^ 2) 0 T := by
    simpa only [pow_two] using (huAC.fun_mul huAC).const_mul lambda
  have hqderiv : ∀ᵐ t, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (fun s => lambda * u s ^ 2)
        (2 * lambda * u t * (f t - lambda * u t)) t := by
    filter_upwards [ae_hasDerivAt_spectralMode (lambda := lambda) (c := c) hf]
      with t ht hmem
    have hd := ((ht hmem).pow 2).const_mul lambda
    change HasDerivAt (fun s => lambda * u s ^ 2) _ t at hd
    apply hd.congr_deriv
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have hftc : (∫ t in (0 : ℝ)..T, 2 * lambda * u t * (f t - lambda * u t)) =
      lambda * u T ^ 2 - lambda * u 0 ^ 2 := by
    rw [← hqAC.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqderiv] with t ht hmem
    exact (ht (uIoc_subset_uIcc hmem)).deriv.symm
  have hsplit : (∫ t in (0 : ℝ)..T, f t ^ 2) =
      (∫ t in (0 : ℝ)..T, (f t - lambda * u t) ^ 2) +
      (∫ t in (0 : ℝ)..T, (lambda * u t) ^ 2) +
      (∫ t in (0 : ℝ)..T, 2 * lambda * u t * (f t - lambda * u t)) := by
    rw [← intervalIntegral.integral_add hD hA,
      ← intervalIntegral.integral_add (hD.add hA) hR]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hftc] at hsplit
  have hzero : u 0 = c := spectralMode_zero lambda c f
  rw [hzero] at hsplit
  change (∫ t in (0 : ℝ)..T, (f t - lambda * u t) ^ 2) +
      (∫ t in (0 : ℝ)..T, (lambda * u t) ^ 2) + lambda * u T ^ 2 = _
  linarith

theorem intervalIntegrable_and_sq_of_memLp_two
    {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    IntervalIntegrable f volume 0 T ∧
      IntervalIntegrable (fun t => f t ^ 2) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT,
    intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact ⟨hf.integrable (by norm_num), hf.integrable_sq⟩

theorem spectralMode_energy_identity_of_memLp
    {lambda c T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    (∫ t in (0 : ℝ)..T, (f t - lambda * spectralMode lambda c f t) ^ 2) +
        (∫ t in (0 : ℝ)..T, (lambda * spectralMode lambda c f t) ^ 2) +
        lambda * spectralMode lambda c f T ^ 2 =
      (∫ t in (0 : ℝ)..T, f t ^ 2) + lambda * c ^ 2 := by
  obtain ⟨hfi, hfi2⟩ := intervalIntegrable_and_sq_of_memLp_two hT hf
  exact spectralMode_energy_identity_of_integrable hfi hfi2

theorem spectralMode_zero_initial_generator_energy_le_of_memLp
    {lambda T : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda) (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    (∫ t in (0 : ℝ)..T, (lambda * spectralMode lambda 0 f t) ^ 2) ≤
      ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  have he := spectralMode_energy_identity_of_memLp (lambda := lambda) (c := 0) hT hf
  have hD : 0 ≤ ∫ t in (0 : ℝ)..T,
      (f t - lambda * spectralMode lambda 0 f t) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)
  have htrace : 0 ≤ lambda * spectralMode lambda 0 f T ^ 2 :=
    mul_nonneg hlambda (sq_nonneg _)
  nlinarith

end PoincareConjecture
