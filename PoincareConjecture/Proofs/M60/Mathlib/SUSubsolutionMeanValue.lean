import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.EnergyMeanValue
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Powers

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.M60

theorem exists_plane_subsolution_mean_value {a b Λ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (g : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 r, ∀ v : EuclideanSpace ℝ (Fin 2),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ,
          ContDiff ℝ ∞ f → (∀ x, 0 < f x) →
          (∀ x ∈ Metric.ball 0 r, -(Λ / r ^ 2) * f x ≤ D.laplacian f x) →
          f 0 ≤ (C / r) *
            (eLpNorm f 2 (volume.restrict (Metric.closedBall 0 (r / 2)))).toReal := by
  obtain ⟨C, hC, hmean⟩ := HarmonicCoordinates.exists_uniform_energy_mean_value
    (n := 2) (by norm_num) ha hb (P := 1) (by norm_num) hΛ
  refine ⟨C, hC, fun r hr hr1 g D hell f hf hpos hlap => ?_⟩
  have hfs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have henergy (p : ℝ) (hp : 1 ≤ p)
      (η : EuclideanSpace ℝ (Fin 2) → ℝ) (hη : ContDiff ℝ ∞ η)
      (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Metric.ball 0 r) :
      (∫ x, g.inner x (D.gradient (fun y => η y * f y ^ p) x)
        (D.gradient (fun y => η y * f y ^ p) x) ∂g.volumeMeasure) ≤
        1 * p ^ 2 * ((Λ / r ^ 2) *
          (∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure) +
          ∫ x, (f x ^ p) ^ 2 *
            g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) := by
    have hpow := LeviCivitaData.contMDiff_rpow_of_pos hfs hpos p
    have hcut := D.integral_gradient_cutoff_mul_le
      (contMDiff_iff_contDiff.mpr hη) hpow hηc (κ := p * (Λ / r ^ 2))
      (fun x hx => by
        have h := mul_le_mul_of_nonneg_left
          (D.laplacian_rpow_lower hfs hpos hp x (hlap x (hηs hx)))
          (Real.rpow_nonneg (hpos x).le p)
        nlinarith only [h])
    have hmass : 0 ≤ ∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hgrad : 0 ≤ ∫ x, (f x ^ p) ^ 2 *
        g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
      apply integral_nonneg
      intro x
      apply mul_nonneg (sq_nonneg _)
      by_cases hx : D.gradient η x = 0
      · simp [hx]
      · exact (g.pos x _ hx).le
    have hzero : 0 ≤ Λ / r ^ 2 := div_nonneg hΛ (sq_nonneg _)
    have hp2 : p ≤ p ^ 2 := by nlinarith
    have hp1 : 1 ≤ p ^ 2 := by nlinarith
    calc
      _ ≤ _ := hcut
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_right hp2 (mul_nonneg hzero hmass)
        have hg := mul_le_mul_of_nonneg_right hp1 hgrad
        nlinarith only [hm, hg]
  have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (r / 2) ⊆
      Metric.ball 0 r := Metric.closedBall_subset_ball (by linarith)
  have h := hmean r hr hr1 g D hell 0 hball f hf hpos henergy
  norm_num only [Nat.cast_ofNat, neg_div, neg_neg, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_neg_one] at h
  simpa only [div_eq_mul_inv] using h

end PoincareConjecture.M60
