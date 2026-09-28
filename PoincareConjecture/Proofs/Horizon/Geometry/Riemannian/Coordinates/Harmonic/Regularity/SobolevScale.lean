import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Sobolev
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal Manifold

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}

theorem exists_euclidean_ball_sobolev_scale (hn : 2 ≤ n) :
    ∃ q : ℝ≥0, (q : ℝ) = 2 * n / (n - 1) ∧ 2 < q ∧
      ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f →
          tsupport f ⊆ Metric.ball 0 R →
          (eLpNorm f q volume).toReal ^ 2 ≤
            C * R * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let p : ℝ≥0 := ⟨2 * n / (n + 1), by positivity⟩
  let q : ℝ≥0 := ⟨2 * n / (n - 1), div_nonneg (by positivity) (by linarith)⟩
  have hp : (1 : ℝ≥0) ≤ p := by
    change (1 : ℝ) ≤ 2 * n / (n + 1)
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hp2 : p ≤ 2 := by
    change 2 * (n : ℝ) / (n + 1) ≤ 2
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hq : 2 < q := by
    change (2 : ℝ) < 2 * n / (n - 1)
    exact (lt_div_iff₀ (by linarith)).mpr (by linarith)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have hinv : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ -
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)⁻¹ := by
    rw [hdim]
    change (2 * (n : ℝ) / (n - 1))⁻¹ = (2 * (n : ℝ) / (n + 1))⁻¹ - (n : ℝ)⁻¹
    field_simp [hn0.ne']
    ring
  let G := eLpNormLESNormFDerivOfEqInnerConst
    (volume : Measure (EuclideanSpace ℝ (Fin n))) p
  let α : ℝ := 1 / (p : ℝ) - 1 / 2
  have hα : 0 ≤ α := by
    dsimp [α]
    have hpR : (0 : ℝ) < p := (by norm_num : (0 : ℝ) < 1).trans_le
      (by exact_mod_cast hp)
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hpR (by exact_mod_cast hp2))
  have hα2 : α * 2 = (n : ℝ)⁻¹ := by
    change (1 / (2 * (n : ℝ) / (n + 1)) - 1 / 2) * 2 = (n : ℝ)⁻¹
    field_simp [hn0.ne']
    ring
  let A : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^
    (n : ℝ)⁻¹
  have hA : 0 ≤ A := Real.rpow_nonneg ENNReal.toReal_nonneg _
  refine ⟨q, rfl, hq, (G : ℝ) ^ 2 * A + 1, by positivity,
    fun R hR f hf hs => ?_⟩
  let S := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
  let V : ℝ≥0 := (volume S).toNNReal ^ α
  have hV : (V : ℝ≥0∞) = volume S ^ α := by
    dsimp only [V]
    rw [ENNReal.coe_rpow_of_nonneg _ hα,
      ENNReal.coe_toNNReal Metric.isBounded_ball.measure_lt_top.ne]
  have hvol : (volume S).toReal =
      R ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    dsimp only [S]
    rw [Measure.addHaar_ball_of_pos volume _ hR,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp only [finrank_euclideanSpace_fin]
  have hV2 : (V : ℝ) ^ 2 = R * A := by
    change ((volume S).toReal ^ α) ^ 2 = R * A
    rw [← Real.rpow_mul_natCast ENNReal.toReal_nonneg α 2]
    norm_num only [Nat.cast_ofNat]
    rw [hα2, hvol, Real.mul_rpow (by positivity) ENNReal.toReal_nonneg,
      Real.pow_rpow_inv_natCast hR.le (by omega)]
  have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    ((subset_tsupport f).trans (hs.trans Metric.ball_subset_closedBall))
  have hdS : Function.support (fderiv ℝ f) ⊆ S :=
    (subset_tsupport _).trans ((tsupport_fderiv_subset ℝ).trans hs)
  have hderiv : eLpNorm (fderiv ℝ f) p volume ≤
      eLpNorm (fderiv ℝ f) 2 volume * V := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict S) (f := fderiv ℝ f)
      (show (p : ℝ≥0∞) ≤ 2 by exact_mod_cast hp2)
      (hf.continuous_fderiv (by simp)).aestronglyMeasurable
    simpa only [eLpNorm_restrict_eq_of_support_subset (f := fderiv ℝ f) hdS,
      Measure.restrict_apply_univ, ENNReal.coe_toReal, ENNReal.toReal_ofNat,
      ← hV, α] using h
  have hSob : eLpNorm f q volume ≤ (G * V : ℝ≥0) * eLpNorm (fderiv ℝ f) 2 volume := by
    calc
      _ ≤ (G : ℝ≥0∞) * eLpNorm (fderiv ℝ f) p volume :=
        eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume (hf.of_le (by simp)) hfc hp
          (by rw [hdim]; omega) hinv
      _ ≤ G * (eLpNorm (fderiv ℝ f) 2 volume * V) := by gcongr
      _ = _ := by rw [ENNReal.coe_mul]; ac_rfl
  have hd : MemLp (fun x => ‖fderiv ℝ f x‖) 2 volume :=
    (hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport (hfc.fderiv ℝ).norm
  rw [← eLpNorm_norm (f := fderiv ℝ f)] at hSob
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hd.eLpNorm_lt_top.ne) hSob
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at hreal
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mpr hreal
  rw [mul_pow, Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral hd,
    NNReal.coe_mul, mul_pow, hV2] at hsquare
  calc
    _ ≤ (G : ℝ) ^ 2 * (R * A) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := hsquare
    _ ≤ ((G : ℝ) ^ 2 * A + 1) * R * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
      have hi : 0 ≤ ∫ x, ‖fderiv ℝ f x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
      nlinarith [mul_nonneg hR.le hi]

theorem exists_uniform_coordinate_sobolev_scale (hn : 2 ≤ n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ≥0, (q : ℝ) = 2 * n / (n - 1) ∧ 2 < q ∧
      ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
        ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
          (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
            a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
              g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
          ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f →
            HasCompactSupport f → tsupport f ⊆ Metric.ball 0 R →
            (eLpNorm f q volume).toReal ^ 2 ≤ C * R *
              ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
  obtain ⟨q, hqeq, hq, C, hC, hSob⟩ := exists_euclidean_ball_sobolev_scale hn
  refine ⟨q, hqeq, hq, C * (b / Real.sqrt (a ^ n)) + 1, by positivity,
    fun R hR g D hell f hf hfc hfs => ?_⟩
  have henergy : 0 ≤ ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
    apply integral_nonneg
    intro x
    by_cases hx : D.gradient f x = 0
    · simp [hx]
    · exact (g.pos x _ hx).le
  calc
    _ ≤ C * R * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := hSob R hR f hf hfs
    _ ≤ C * R * ((b / Real.sqrt (a ^ n)) *
        ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure) :=
      mul_le_mul_of_nonneg_left
        (integral_fderiv_sq_le_of_ellipticity D ha hb hell hf hfc hfs)
        (mul_nonneg hC.le hR.le)
    _ ≤ (C * (b / Real.sqrt (a ^ n)) + 1) * R *
        ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
      nlinarith [mul_nonneg hR.le henergy]

end PoincareConjecture.HarmonicCoordinates
