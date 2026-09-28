import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy

open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem cutoff_integrable {χ g : Spacetime n → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hg : Continuous g) :
    Integrable (fun z => χ z * g z) :=
  (hχ.mul hg).integrable_of_hasCompactSupport hχc.mul_right

private theorem test_directional_pairing {p g : Spacetime n → ℝ}
    (hp : ContDiff ℝ ∞ p) (hpc : HasCompactSupport p)
    (hg : ContDiff ℝ ∞ g) (v : Spacetime n) :
    (∫ z, p z * fderiv ℝ g z v) = -(∫ z, fderiv ℝ p z v * g z) := by
  have hdp : ContDiff ℝ ∞ (fun z => fderiv ℝ p z v) :=
    (hp.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const
  have hdg : ContDiff ℝ ∞ (fun z => fderiv ℝ g z v) :=
    (hg.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (cutoff_integrable hdp.continuous (hpc.fderiv_apply ℝ v) hg.continuous)
    (cutoff_integrable hp.continuous hpc hdg.continuous)
    (cutoff_integrable hp.continuous hpc hg.continuous)
    (fun z _ => hp.differentiable (by simp) z)
    (fun z _ => hg.differentiable (by simp) z)

private theorem cutoff_test_derivative {χ u : Spacetime n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) (z v : Spacetime n) :
    fderiv ℝ (fun y => χ y ^ 2 * u y) z v =
      χ z ^ 2 * fderiv ℝ u z v + 2 * χ z * u z * fderiv ℝ χ z v := by
  have hdχ := hχ.differentiable (by simp) z
  have hdu := hu.differentiable (by simp) z
  simp only [pow_two]
  erw [fderiv_fun_mul (hdχ.mul hdχ) hdu, fderiv_fun_mul hdχ hdχ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.mul_apply]
  ring

private theorem cutoff_time_pairing {χ u : Spacetime n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hu : ContDiff ℝ ∞ u) :
    (∫ z, χ z ^ 2 * u z * timeDeriv u z) =
      -(∫ z, χ z * timeDeriv χ z * u z ^ 2) := by
  have hp : ContDiff ℝ ∞ (fun z => χ z ^ 2 * u z) := (hχ.pow 2).mul hu
  have hpc : HasCompactSupport (fun z => χ z ^ 2 * u z) := by
    simp only [pow_two]
    change HasCompactSupport (χ * χ * u)
    exact (hχc.mul_right (f' := χ)).mul_right (f' := u)
  have hT : Integrable (fun z => χ z ^ 2 * u z * timeDeriv u z) := by
    convert cutoff_integrable hχ.continuous hχc
      ((hχ.continuous.mul hu.continuous).mul (contDiff_timeDeriv hu).continuous) using 1
    funext z; simp only [Pi.mul_apply]; ring
  have hC : Integrable (fun z => χ z * timeDeriv χ z * u z ^ 2) := by
    convert cutoff_integrable hχ.continuous hχc
      ((contDiff_timeDeriv hχ).continuous.mul (hu.continuous.pow 2)) using 1
    funext z; simp only [Pi.mul_apply, Pi.pow_apply]; ring
  have hpairs := test_directional_pairing hp hpc hu (0, 1)
  have hexpand : (fun z => fderiv ℝ (fun y => χ y ^ 2 * u y) z (0, 1) * u z) =
      fun z => χ z ^ 2 * u z * timeDeriv u z +
        2 * (χ z * timeDeriv χ z * u z ^ 2) := by
    funext z
    rw [cutoff_test_derivative hχ hu]
    simp only [timeDeriv]
    ring
  rw [hexpand, integral_add hT (hC.const_mul 2), integral_const_mul] at hpairs
  change (∫ z, χ z ^ 2 * u z * timeDeriv u z) = _ at hpairs
  linarith

private theorem cutoff_divergence_pairing
    {χ u : Spacetime n → ℝ} {Q : Fin n → Spacetime n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hu : ContDiff ℝ ∞ u)
    (hQ : ∀ i, ContDiff ℝ ∞ (Q i)) :
    (∫ z, χ z ^ 2 * u z * ∑ i, spatialDeriv i (Q i) z) =
      -(∫ z, ∑ i, χ z ^ 2 * Q i z * spatialDeriv i u z) -
        2 * (∫ z, ∑ i, χ z * u z * Q i z * spatialDeriv i χ z) := by
  have hp : ContDiff ℝ ∞ (fun z => χ z ^ 2 * u z) := (hχ.pow 2).mul hu
  have hpc : HasCompactSupport (fun z => χ z ^ 2 * u z) := by
    simp only [pow_two]
    change HasCompactSupport (χ * χ * u)
    exact (hχc.mul_right (f' := χ)).mul_right (f' := u)
  have hL (i : Fin n) : Integrable (fun z => χ z ^ 2 * u z * spatialDeriv i (Q i) z) :=
    cutoff_integrable hp.continuous hpc (contDiff_spatialDeriv (hQ i) i).continuous
  have hR (i : Fin n) : Integrable (fun z => χ z ^ 2 * Q i z * spatialDeriv i u z) := by
    convert cutoff_integrable hχ.continuous hχc
      ((hχ.continuous.mul (hQ i).continuous).mul (contDiff_spatialDeriv hu i).continuous) using 1
    funext z; simp only [Pi.mul_apply]; ring
  have hC (i : Fin n) : Integrable (fun z => χ z * u z * Q i z * spatialDeriv i χ z) := by
    convert cutoff_integrable hχ.continuous hχc
      ((hu.continuous.mul (hQ i).continuous).mul (contDiff_spatialDeriv hχ i).continuous) using 1
    funext z; simp only [Pi.mul_apply]; ring
  have he (i : Fin n) :
      (∫ z, χ z ^ 2 * u z * spatialDeriv i (Q i) z) =
        -(∫ z, χ z ^ 2 * Q i z * spatialDeriv i u z) -
          2 * (∫ z, χ z * u z * Q i z * spatialDeriv i χ z) := by
    have h := test_directional_pairing hp hpc (hQ i) (spatialDirection i)
    have he : (fun z => fderiv ℝ (fun y => χ y ^ 2 * u y) z (spatialDirection i) * Q i z) =
        fun z => χ z ^ 2 * Q i z * spatialDeriv i u z +
          2 * (χ z * u z * Q i z * spatialDeriv i χ z) := by
      funext z
      rw [cutoff_test_derivative hχ hu]
      simp only [spatialDeriv]
      ring
    rw [he, integral_add (hR i) ((hC i).const_mul 2), integral_const_mul] at h
    change (∫ z, χ z ^ 2 * u z * spatialDeriv i (Q i) z) = _ at h
    linarith
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hL i),
    integral_finsetSum _ (fun i _ => hR i), integral_finsetSum _ (fun i _ => hC i)]
  simp only [he, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]

theorem parabolic_cutoff_energy_identity
    {a : Fin n → Fin n → Spacetime n → ℝ}
    {F : Fin n → Spacetime n → ℝ} {u f χ : Spacetime n → ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (heq : ∀ z ∈ tsupport χ, timeDeriv u z -
      ∑ i, spatialDeriv i (fun y => ∑ j, a i j y * spatialDeriv j u y) z =
      f z + ∑ i, spatialDeriv i (F i) z) :
    (∫ z, ∑ i, ∑ j, χ z ^ 2 * a i j z * spatialDeriv i u z * spatialDeriv j u z) =
      (∫ z, χ z ^ 2 * f z * u z) + (∫ z, χ z * timeDeriv χ z * u z ^ 2) -
        (∫ z, ∑ i, χ z ^ 2 * F i z * spatialDeriv i u z) -
        2 * (∫ z, ∑ i, χ z * u z * F i z * spatialDeriv i χ z) -
        2 * (∫ z, ∑ i, ∑ j,
          χ z * u z * spatialDeriv i χ z * a i j z * spatialDeriv j u z) := by
  let Q : Fin n → Spacetime n → ℝ := fun i z => ∑ j, a i j z * spatialDeriv j u z
  have hQ (i : Fin n) : ContDiff ℝ ∞ (Q i) :=
    ContDiff.sum (fun j _ => (ha i j).mul (contDiff_spatialDeriv hu j))
  have hp : ContDiff ℝ ∞ (fun z => χ z ^ 2 * u z) := (hχ.pow 2).mul hu
  have hpc : HasCompactSupport (fun z => χ z ^ 2 * u z) := by
    simp only [pow_two]
    change HasCompactSupport (χ * χ * u)
    exact (hχc.mul_right (f' := χ)).mul_right (f' := u)
  have hT : Integrable (fun z => χ z ^ 2 * u z * timeDeriv u z) :=
    cutoff_integrable hp.continuous hpc (contDiff_timeDeriv hu).continuous
  have hDQ : Integrable (fun z => χ z ^ 2 * u z * ∑ i, spatialDeriv i (Q i) z) :=
    cutoff_integrable hp.continuous hpc
      (continuous_finsetSum _ (fun i _ => (contDiff_spatialDeriv (hQ i) i).continuous))
  have hDF : Integrable (fun z => χ z ^ 2 * u z * ∑ i, spatialDeriv i (F i) z) :=
    cutoff_integrable hp.continuous hpc
      (continuous_finsetSum _ (fun i _ => (contDiff_spatialDeriv (hF i) i).continuous))
  have hS : Integrable (fun z => χ z ^ 2 * u z * f z) :=
    cutoff_integrable hp.continuous hpc hf.continuous
  have hEqI :
      (∫ z, χ z ^ 2 * u z * timeDeriv u z -
        χ z ^ 2 * u z * ∑ i, spatialDeriv i (Q i) z) =
      ∫ z, χ z ^ 2 * u z * f z +
        χ z ^ 2 * u z * ∑ i, spatialDeriv i (F i) z := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ tsupport χ
    · have h := congrArg (χ z ^ 2 * u z * ·) (heq z hz)
      dsimp only [Q]
      nlinarith [h]
    · simp only [image_eq_zero_of_notMem_tsupport hz, zero_pow (by decide : 2 ≠ 0),
        zero_mul, sub_zero, add_zero]
  rw [integral_sub hT hDQ, integral_add hS hDF,
    cutoff_time_pairing hχ hχc hu,
    cutoff_divergence_pairing hχ hχc hu hQ,
    cutoff_divergence_pairing hχ hχc hu hF] at hEqI
  have hE : (fun z => ∑ i, χ z ^ 2 * Q i z * spatialDeriv i u z) =
      (fun z => ∑ i, ∑ j,
        χ z ^ 2 * a i j z * spatialDeriv i u z * spatialDeriv j u z) := by
    funext z
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Q, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hC : (fun z => ∑ i, χ z * u z * Q i z * spatialDeriv i χ z) =
      (fun z => ∑ i, ∑ j,
        χ z * u z * spatialDeriv i χ z * a i j z * spatialDeriv j u z) := by
    funext z
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Q, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsource : (fun z => χ z ^ 2 * u z * f z) =
      (fun z => χ z ^ 2 * f z * u z) := by funext z; ring
  rw [hE, hC, hsource] at hEqI
  linarith

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
