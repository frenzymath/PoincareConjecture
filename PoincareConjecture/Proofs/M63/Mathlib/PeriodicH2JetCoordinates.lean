import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSobolevJets









set_option autoImplicit false

namespace PoincareConjecture.M63

variable {L : ℝ}




theorem periodicH2JetMultiplier_bound {j : ℕ} (hj : j ≤ 1) (n : ℤ) :
    ‖periodicSobolevMoment L 0 j n‖ ≤ 1 := by
  let ω : ℝ := 2 * Real.pi * (n : ℝ) / L
  let ρ : ℝ := Real.sqrt (1 + ω ^ 2)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = 1 + ω ^ 2 := Real.sq_sqrt (by positivity)
  have hρ1 : 1 ≤ ρ := by nlinarith [sq_nonneg ω]
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hω : |ω| ≤ ρ := by nlinarith [sq_abs ω, abs_nonneg ω]
  have hpow : |ω| ^ j ≤ ρ := by
    have h := (pow_le_pow_left₀ (abs_nonneg ω) hω j).trans
      (pow_le_pow_right₀ hρ1 hj)
    simpa only [pow_one] using h
  change ‖(Complex.I * (ω : ℂ)) ^ j / (ρ : ℂ) ^ (0 + 1)‖ ≤ 1
  simp only [zero_add, pow_one, norm_div, norm_pow, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
  exact (div_le_one hρpos).mpr hpow




noncomputable def periodicH2JetCoordinates (j : ℕ) (hj : j ≤ 1) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  lp.mapCLM 2 (fun n : ℤ => ContinuousLinearMap.mul ℂ ℂ
    (periodicSobolevMoment L 0 j n)) zero_le_one (fun n => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro z
      change ‖periodicSobolevMoment L 0 j n * z‖ ≤ 1 * ‖z‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (periodicH2JetMultiplier_bound hj n) (norm_nonneg z))

variable [Fact (0 < L)]




theorem periodicH2JetCoordinates_spec (j : ℕ) (hj : j ≤ 1)
    (u : lp (fun _ : ℤ => ℂ) 2) :
    ‖periodicH2JetCoordinates (L := L) j hj u‖ ≤ ‖u‖ ∧
      periodicSobolevJet (L := L) 0 0 (by omega)
        (periodicH2JetCoordinates (L := L) j hj u) =
      periodicSobolevJet (L := L) 1 j hj u := by
  constructor
  · apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro n
    change ‖periodicSobolevMoment L 0 j n * u n‖ ≤ ‖u n‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (periodicH2JetMultiplier_bound hj n)
  · have hc (n : ℤ) : periodicSobolevMoment L 0 0 n *
        periodicH2JetCoordinates (L := L) j hj u n =
        periodicSobolevMoment L 1 j n * u n := by
      change periodicSobolevMoment L 0 0 n *
        (periodicSobolevMoment L 0 j n * u n) = _
      simp only [periodicSobolevMoment, pow_zero, zero_add, pow_one, div_eq_mul_inv]
      ring
    have hs := weightedFourier_hasSum (L := L)
      ⟨periodicSobolevMoment L 0 0, (periodicSobolevMoment_bound (by omega)).2⟩
      (periodicH2JetCoordinates (L := L) j hj u)
    change HasSum (fun n : ℤ => (periodicSobolevMoment L 0 0 n *
      periodicH2JetCoordinates (L := L) j hj u n) • fourier n)
      (periodicSobolevJet (L := L) 0 0 (by omega)
        (periodicH2JetCoordinates (L := L) j hj u)) at hs
    simp_rw [hc] at hs
    exact hs.unique (weightedFourier_hasSum (L := L)
      ⟨periodicSobolevMoment L 1 j, (periodicSobolevMoment_bound hj).2⟩ u)

end PoincareConjecture.M63
