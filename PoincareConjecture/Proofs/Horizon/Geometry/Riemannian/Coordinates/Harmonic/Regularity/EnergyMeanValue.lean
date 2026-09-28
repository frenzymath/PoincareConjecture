import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.EnergyStep
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.IterationBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.LpPowers
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.LpLimit

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.HarmonicCoordinates

private theorem le_root_mul_of_energy_rpow_le {u v F t : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hF : 0 ≤ F) (ht : 0 < t)
    (h : u ^ t ≤ F * v ^ t) : u ≤ F ^ (1 / t) * v := by
  apply (Real.rpow_le_rpow_iff hu (mul_nonneg (Real.rpow_nonneg hF _) hv) ht).mp
  rw [Real.mul_rpow (Real.rpow_nonneg hF _) hv, one_div,
    Real.rpow_inv_rpow hF ht.ne']
  exact h

theorem exists_uniform_energy_mean_value {n : ℕ} (hn : 2 ≤ n)
    {a b P Λ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hP : 0 ≤ P) (hΛ : 0 ≤ Λ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 r, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ z : EuclideanSpace ℝ (Fin n), Metric.closedBall z (r / 2) ⊆ Metric.ball 0 r →
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 < f x) →
          (∀ p : ℝ, 1 ≤ p → ∀ η : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Metric.ball 0 r →
            (∫ x, g.inner x (D.gradient (fun y => η y * f y ^ p) x)
              (D.gradient (fun y => η y * f y ^ p) x) ∂g.volumeMeasure) ≤
              P * p ^ 2 * ((Λ / r ^ 2) * (∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure) +
                ∫ x, (f x ^ p) ^ 2 *
                  g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure)) →
          f z ≤ M * r ^ (-(n : ℝ) / 2) *
            (eLpNorm f 2 (volume.restrict (Metric.closedBall z (r / 2)))).toReal := by
  obtain ⟨q, hqeq, hq, C, A, hC, hA, hstep⟩ := exists_uniform_energy_power_step hn ha hb hP
  let χ : ℝ := q / 2
  have hχ : 1 < χ := by
    have hq' : (2 : ℝ) < q := by exact_mod_cast hq
    dsimp only [χ]
    linarith
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hχeq : χ = (n : ℝ) / ((n : ℝ) - 1) := by
    dsimp only [χ]
    rw [hqeq]
    ring
  have hα : χ / (2 * (χ - 1)) = (n : ℝ) / 2 := by
    have heq : χ * ((n : ℝ) - 1) = n := by
      rw [hχeq]
      exact div_mul_cancel₀ _ hn1
    apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      (sub_pos.mpr hχ).ne')).mpr
    nlinarith
  let B : ℝ := max 1 (C * (Λ + 4 * A ^ 2 / a))
  let L : ℝ := 4 * χ ^ 2
  have hB : 1 ≤ B := le_max_left _ _
  have hL : 1 ≤ L := by
    have hs : 1 ≤ χ ^ 2 := one_le_pow₀ hχ.le
    dsimp only [L]
    linarith
  obtain ⟨M, hM, hiter⟩ := exists_uniform_scaled_iteration_bound hχ hB hL
  refine ⟨M, hM, fun r hr hr1 g D hell z hball f hf hpos henergy => ?_⟩
  let ρ := r / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let u : ℕ → ℝ := fun k =>
    (eLpNorm f (ENNReal.ofReal (2 * χ ^ k))
      (volume.restrict (Metric.closedBall z (ρ / (2 : ℝ) ^ k)))).toReal
  have hu (k) : 0 ≤ u k := ENNReal.toReal_nonneg
  have hrad (k : ℕ) : ρ / (2 : ℝ) ^ k ≤ ρ :=
    div_le_self hρ.le (one_le_pow₀ (by norm_num))
  have hcontain (k : ℕ) : Metric.closedBall z (ρ / (2 : ℝ) ^ k) ⊆
      Metric.closedBall z ρ := Metric.closedBall_subset_closedBall (hrad k)
  have hrec (k : ℕ) : u (k + 1) ≤ ((B / r) * L ^ k) ^ (1 / (2 * χ ^ k)) * u k := by
    have hp : 1 ≤ χ ^ k := one_le_pow₀ hχ.le
    have hp0 : 0 < χ ^ k := pow_pos hχ0 k
    have hkρ : 0 < ρ / (2 : ℝ) ^ k := div_pos hρ (by positivity)
    have hs := hstep r hr g D hell z (ρ / (2 : ℝ) ^ k) hkρ
      ((hcontain k).trans hball) f hf hpos (χ ^ k) (Λ / r ^ 2) hp
      (div_nonneg hΛ (sq_nonneg r)) (henergy (χ ^ k) hp)
    rw [eLpNorm_rpow_toReal_sq (fun x => (hpos x).le) q hp0,
      setIntegral_rpow_sq_eq_eLpNorm_rpow (isCompact_closedBall _ _) hf.continuous
        (fun x => (hpos x).le) hp0] at hs
    have hexponent : (q : ℝ≥0∞) * ENNReal.ofReal (χ ^ k) =
        ENNReal.ofReal (2 * χ ^ (k + 1)) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul q.coe_nonneg]
      congr 1
      dsimp only [χ]
      rw [pow_succ]
      ring
    have hradius : ρ / (2 : ℝ) ^ k / 2 = ρ / (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ, div_div]
    rw [hexponent, hradius] at hs
    change u (k + 1) ^ (2 * χ ^ k) ≤
      C * r * (χ ^ k) ^ 2 * (Λ / r ^ 2 + (A / (ρ / (2 : ℝ) ^ k)) ^ 2 / a) *
        u k ^ (2 * χ ^ k) at hs
    have hfactor : C * r * (χ ^ k) ^ 2 *
        (Λ / r ^ 2 + (A / (ρ / (2 : ℝ) ^ k)) ^ 2 / a) ≤ (B / r) * L ^ k := by
      have htwo : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
        rw [← pow_mul, mul_comm k 2, pow_mul]
        norm_num
      have hχpow : (χ ^ k) ^ 2 = (χ ^ 2) ^ k := by
        rw [← pow_mul, mul_comm k 2, pow_mul]
      have hcut : (A / (ρ / (2 : ℝ) ^ k)) ^ 2 / a =
          (4 * A ^ 2 / a) / r ^ 2 * (4 : ℝ) ^ k := by
        dsimp only [ρ]
        rw [div_div_eq_mul_div, div_div_eq_mul_div, div_pow, mul_pow, mul_pow, htwo]
        norm_num
        ring
      have hscale : C * r * (χ ^ k) ^ 2 *
          (Λ / r ^ 2 + (A / (ρ / (2 : ℝ) ^ k)) ^ 2 / a) =
          (C / r) * (χ ^ 2) ^ k * (Λ + (4 * A ^ 2 / a) * (4 : ℝ) ^ k) := by
        rw [hcut, hχpow]
        field_simp [hr.ne', ha.ne']
      have hΛscale : Λ ≤ Λ * (4 : ℝ) ^ k :=
        le_mul_of_one_le_right hΛ (one_le_pow₀ (by norm_num))
      calc
        _ = _ := hscale
        _ ≤ (C / r) * (χ ^ 2) ^ k * ((Λ + 4 * A ^ 2 / a) * (4 : ℝ) ^ k) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith only [hΛscale]
        _ = (C * (Λ + 4 * A ^ 2 / a) / r) * L ^ k := by
          dsimp only [L]
          rw [mul_pow]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (le_max_right _ _) hr.le) (by positivity)
    apply le_root_mul_of_energy_rpow_le (hu _) (hu _) (by positivity) (by positivity)
    exact hs.trans (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (hu _) _))
  have hub := hiter r hr hr1 u hu hrec
  have hpoint : |f z| ≤ M * r ^ (-(χ / (2 * (χ - 1)))) * u 0 := by
    apply continuousAt_abs_le_of_shrinking_eLpNorm hf.continuous.continuousAt hρ hχ
    · intro k
      exact (continuous_memLp_restrict_ball hf.continuous z _ _).eLpNorm_ne_top
    · intro k
      apply le_trans _ (hub k)
      exact ENNReal.toReal_mono
        (continuous_memLp_restrict_closedBall hf.continuous z _ _).eLpNorm_ne_top
        (eLpNorm_mono_measure f (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl))
  simpa only [hα, neg_div, abs_of_pos (hpos z), u, ρ, pow_zero, mul_one, div_one,
    ENNReal.ofReal_ofNat] using hpoint

end PoincareConjecture.HarmonicCoordinates
