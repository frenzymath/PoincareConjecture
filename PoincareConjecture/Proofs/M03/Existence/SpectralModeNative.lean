import PoincareConjecture.Proofs.M03.Existence.VolterraPicard
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow










set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace PoincareConjecture


def spectralMode (lambda c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-lambda * t) *
    (c + ∫ s in (0 : ℝ)..t, Real.exp (lambda * s) * f s)

@[simp] theorem spectralMode_zero (lambda c : ℝ) (f : ℝ → ℝ) :
    spectralMode lambda c f 0 = c := by
  simp [spectralMode]

private theorem hasDerivAt_modeDecay (lambda t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-lambda * s))
      (-lambda * Real.exp (-lambda * t)) t := by
  have h := ((hasDerivAt_id t).const_mul (-lambda)).exp
  apply h.congr_deriv
  simp only [id_eq, mul_one]
  ring

theorem hasDerivWithinAt_spectralMode
    {lambda c T t : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (spectralMode lambda c f)
      (f t - lambda * spectralMode lambda c f t) (Icc (0 : ℝ) T) t := by
  have he : Continuous (fun s : ℝ => Real.exp (lambda * s)) := by fun_prop
  have hsrc := he.continuousOn.mul hf
  have hi := hasDerivWithinAt_volterraPath_Icc (x₀ := c) hsrc ht
  have hp := (hasDerivAt_modeDecay lambda t).hasDerivWithinAt.mul hi
  change HasDerivWithinAt (spectralMode lambda c f) _ (Icc (0 : ℝ) T) t at hp
  apply hp.congr_deriv
  have hcancel : Real.exp (-lambda * t) * Real.exp (lambda * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  dsimp [spectralMode, volterraPath]
  calc
    -lambda * Real.exp (-lambda * t) *
          (c + ∫ s in (0 : ℝ)..t, Real.exp (lambda * s) * f s) +
        Real.exp (-lambda * t) * (Real.exp (lambda * t) * f t) =
      -lambda * (Real.exp (-lambda * t) *
          (c + ∫ s in (0 : ℝ)..t, Real.exp (lambda * s) * f s)) +
        (Real.exp (-lambda * t) * Real.exp (lambda * t)) * f t := by ring
    _ = f t - lambda * (Real.exp (-lambda * t) *
          (c + ∫ s in (0 : ℝ)..t, Real.exp (lambda * s) * f s)) := by
      rw [hcancel]
      ring

theorem continuousOn_spectralMode
    {lambda c T : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    ContinuousOn (spectralMode lambda c f) (Icc (0 : ℝ) T) := by
  intro t ht
  exact (hasDerivWithinAt_spectralMode hf ht).continuousWithinAt

theorem hasDerivAt_spectralMode_of_mem_Ioo
    {lambda c T t : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (spectralMode lambda c f)
      (f t - lambda * spectralMode lambda c f t) t := by
  exact (hasDerivWithinAt_spectralMode hf ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)


theorem spectralMode_energy_identity
    {lambda c T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, (f t - lambda * spectralMode lambda c f t) ^ 2) +
        (∫ t in (0 : ℝ)..T, (lambda * spectralMode lambda c f t) ^ 2) +
        lambda * spectralMode lambda c f T ^ 2 =
      (∫ t in (0 : ℝ)..T, f t ^ 2) + lambda * c ^ 2 := by
  let u := spectralMode lambda c f
  have hu : ContinuousOn u (Icc (0 : ℝ) T) := continuousOn_spectralMode hf
  have hdu : ContinuousOn (fun t => f t - lambda * u t) (Icc (0 : ℝ) T) :=
    hf.sub (continuousOn_const.mul hu)
  have hD : IntervalIntegrable (fun t => (f t - lambda * u t) ^ 2) volume 0 T :=
    (hdu.pow 2).intervalIntegrable_of_Icc hT
  have hA : IntervalIntegrable (fun t => (lambda * u t) ^ 2) volume 0 T :=
    ((continuousOn_const.mul hu).pow 2).intervalIntegrable_of_Icc hT
  have hR : ContinuousOn (fun t => 2 * lambda * u t * (f t - lambda * u t))
      (Icc (0 : ℝ) T) := (continuousOn_const.mul hu).mul hdu
  have hRint : IntervalIntegrable
      (fun t => 2 * lambda * u t * (f t - lambda * u t)) volume 0 T :=
    hR.intervalIntegrable_of_Icc hT
  have hqderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s => lambda * u s ^ 2)
        (2 * lambda * u t * (f t - lambda * u t)) t := by
    intro t ht
    have hd := hasDerivAt_spectralMode_of_mem_Ioo (lambda := lambda) (c := c) hf ht
    have hq := (hd.pow 2).const_mul lambda
    change HasDerivAt (fun s => lambda * u s ^ 2) _ t at hq
    apply hq.congr_deriv
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (continuousOn_const.mul (hu.pow 2)) hqderiv hRint
  have hsplit : (∫ t in (0 : ℝ)..T, f t ^ 2) =
      (∫ t in (0 : ℝ)..T, (f t - lambda * u t) ^ 2) +
      (∫ t in (0 : ℝ)..T, (lambda * u t) ^ 2) +
      (∫ t in (0 : ℝ)..T, 2 * lambda * u t * (f t - lambda * u t)) := by
    rw [← intervalIntegral.integral_add hD hA,
      ← intervalIntegral.integral_add (hD.add hA) hRint]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hftc] at hsplit
  simp only [Pi.mul_apply, Pi.pow_apply] at hsplit
  have hzero : u 0 = c := spectralMode_zero lambda c f
  rw [hzero] at hsplit
  change (∫ t in (0 : ℝ)..T, (f t - lambda * u t) ^ 2) +
      (∫ t in (0 : ℝ)..T, (lambda * u t) ^ 2) + lambda * u T ^ 2 = _
  linarith


theorem spectralMode_energy_le
    {lambda c T : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, (f t - lambda * spectralMode lambda c f t) ^ 2) +
        (∫ t in (0 : ℝ)..T, (lambda * spectralMode lambda c f t) ^ 2) ≤
      (∫ t in (0 : ℝ)..T, f t ^ 2) + lambda * c ^ 2 := by
  have h := spectralMode_energy_identity (lambda := lambda) (c := c) hT hf
  have hn : 0 ≤ lambda * spectralMode lambda c f T ^ 2 :=
    mul_nonneg hlambda (sq_nonneg _)
  linarith



theorem spectralMode_zero_initial_generator_energy_le
    {lambda T : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, (lambda * spectralMode lambda 0 f t) ^ 2) ≤
      ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  have h := spectralMode_energy_le (c := 0) hlambda hT hf
  have hn : 0 ≤ ∫ t in (0 : ℝ)..T,
      (f t - lambda * spectralMode lambda 0 f t) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)
  nlinarith


theorem spectralMode_eq_convolution (lambda c t : ℝ) (f : ℝ → ℝ) :
    spectralMode lambda c f t = Real.exp (-lambda * t) * c +
      ∫ s in (0 : ℝ)..t, Real.exp (-lambda * (t - s)) * f s := by
  unfold spectralMode
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have he : Real.exp (-lambda * t) * Real.exp (lambda * s) =
      Real.exp (-lambda * (t - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [← mul_assoc, he]


theorem spectralMode_trace_energy_le
    {lambda c T t : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (ht : t ∈ Icc (0 : ℝ) T) :
    lambda * spectralMode lambda c f t ^ 2 ≤
      (∫ s in (0 : ℝ)..t, f s ^ 2) + lambda * c ^ 2 := by
  have hft : ContinuousOn f (Icc (0 : ℝ) t) :=
    hf.mono (Icc_subset_Icc le_rfl ht.2)
  have h := spectralMode_energy_identity (lambda := lambda) (c := c) ht.1 hft
  have hD : 0 ≤ ∫ s in (0 : ℝ)..t,
      (f s - lambda * spectralMode lambda c f s) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
  have hA : 0 ≤ ∫ s in (0 : ℝ)..t,
      (lambda * spectralMode lambda c f s) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
  linarith



theorem spectralMode_zero_initial_intermediate_energy_le
    {lambda T : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, lambda * spectralMode lambda 0 f t ^ 2) ≤
      T * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  have hu := continuousOn_spectralMode (lambda := lambda) (c := 0) hf
  have hfint : IntervalIntegrable (fun t => f t ^ 2) volume 0 T :=
    (hf.pow 2).intervalIntegrable_of_Icc hT
  have hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      lambda * spectralMode lambda 0 f t ^ 2 ≤ ∫ s in (0 : ℝ)..T, f s ^ 2 := by
    intro t ht
    have htrace : lambda * spectralMode lambda 0 f t ^ 2 ≤
        ∫ s in (0 : ℝ)..t, f s ^ 2 := by
      simpa using spectralMode_trace_energy_le (c := 0) hlambda hf ht
    have hmono := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun s => sq_nonneg (f s))) hfint
    exact htrace.trans hmono
  have hint : IntervalIntegrable
      (fun t => lambda * spectralMode lambda 0 f t ^ 2) volume 0 T :=
    (continuousOn_const.mul (hu.pow 2)).intervalIntegrable_of_Icc hT
  have hle := intervalIntegral.integral_mono_on hT hint
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ∫ s in (0 : ℝ)..T, f s ^ 2) volume 0 T) hpoint
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hle

end PoincareConjecture
