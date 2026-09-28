import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.EnergyBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Caccioppoli
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal Manifold

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}

theorem exists_euclidean_ball_sobolev (hn : 2 ≤ n) (R : ℝ) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ≥0,
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f →
        tsupport f ⊆ Metric.ball 0 R →
        eLpNorm f q volume ≤ C * eLpNorm (fderiv ℝ f) 2 volume := by
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
  let S := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
  let G := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (EuclideanSpace ℝ (Fin n))) p
  let α : ℝ := 1 / (p : ℝ) - 1 / 2
  have hα : 0 ≤ α := by
    dsimp [α]
    have hpR : (0 : ℝ) < p := (by norm_num : (0 : ℝ) < 1).trans_le (by exact_mod_cast hp)
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hpR (by exact_mod_cast hp2))
  let V : ℝ≥0 := (volume S).toNNReal ^ α
  have hV : (V : ℝ≥0∞) = volume S ^ α := by
    dsimp only [V]
    rw [ENNReal.coe_rpow_of_nonneg _ hα,
      ENNReal.coe_toNNReal Metric.isBounded_ball.measure_lt_top.ne]
  refine ⟨q, hq, G * V, fun f hf hs => ?_⟩
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
    simpa only [eLpNorm_restrict_eq_of_support_subset (f := fderiv ℝ f) hdS, Measure.restrict_apply_univ,
      ENNReal.coe_toReal, ENNReal.toReal_ofNat, ← hV, α] using h
  calc
    _ ≤ (G : ℝ≥0∞) * eLpNorm (fderiv ℝ f) p volume :=
      eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume (hf.of_le (by simp)) hfc hp
        (by rw [hdim]; omega) hinv
    _ ≤ G * (eLpNorm (fderiv ℝ f) 2 volume * V) := by gcongr
    _ = _ := by rw [ENNReal.coe_mul]; ac_rfl

theorem exists_uniform_coordinate_sobolev (hn : 2 ≤ n)
    (R : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f →
          HasCompactSupport f → tsupport f ⊆ Metric.ball 0 R →
          (eLpNorm f q volume).toReal ^ 2 ≤ C *
            ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
  obtain ⟨q, hq, A, hA⟩ := exists_euclidean_ball_sobolev hn R
  refine ⟨q, hq, (A : ℝ) ^ 2 * (b / Real.sqrt (a ^ n)), by positivity,
    fun g D hell f hf hfc hfs => ?_⟩
  have hd : MemLp (fun x => ‖fderiv ℝ f x‖) 2 volume :=
    (hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport (hfc.fderiv ℝ).norm
  have hs := hA f hf hfs
  rw [← eLpNorm_norm (f := fderiv ℝ f)] at hs
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    hd.eLpNorm_lt_top.ne) hs
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at hreal
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mpr hreal
  rw [mul_pow, Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral hd] at hsquare
  calc
    _ ≤ (A : ℝ) ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := hsquare
    _ ≤ (A : ℝ) ^ 2 * ((b / Real.sqrt (a ^ n)) *
        ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure) :=
      mul_le_mul_of_nonneg_left
        (integral_fderiv_sq_le_of_ellipticity D ha hb hell hf hfc hfs) (sq_nonneg _)
    _ = _ := by ring

theorem exists_uniform_cutoff_sobolev (hn : 2 ≤ n)
    (R : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ η U : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ η → ContDiff ℝ ∞ U →
          HasCompactSupport η → tsupport η ⊆ Metric.ball 0 R →
          ∀ κ : ℝ, (∀ x ∈ tsupport η, -(κ * U x ^ 2) ≤ U x * D.laplacian U x) →
          (eLpNorm (fun x => η x * U x) q volume).toReal ^ 2 ≤ C *
            (κ * (∫ x, η x ^ 2 * U x ^ 2 ∂g.volumeMeasure) +
              ∫ x, U x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) := by
  obtain ⟨q, hq, C, hC, hSob⟩ := exists_uniform_coordinate_sobolev hn R ha hb
  refine ⟨q, hq, C, hC, fun g D hell η U hη hU hηc hηs κ hlap => ?_⟩
  exact (hSob g D hell (fun x => η x * U x) (hη.mul hU) hηc.mul_right
    (tsupport_mul_subset_left.trans hηs)).trans
    (mul_le_mul_of_nonneg_left
      (D.integral_gradient_cutoff_mul_le (contMDiff_iff_contDiff.mpr hη)
        (contMDiff_iff_contDiff.mpr hU) hηc hlap) hC)

end PoincareConjecture.HarmonicCoordinates
