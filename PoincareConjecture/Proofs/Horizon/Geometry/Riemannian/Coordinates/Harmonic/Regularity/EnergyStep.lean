import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.SobolevScale
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.IterationStep








noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}


theorem exists_scaled_energy_cutoff :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : EuclideanSpace ℝ (Fin n), ∀ ρ : ℝ, 0 < ρ →
      ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        tsupport η ⊆ Metric.closedBall z ρ ∧ (∀ x, η x ∈ Icc 0 1) ∧
        (∀ x ∈ Metric.closedBall z (ρ / 2), η x = 1) ∧
        (∀ x, ‖fderiv ℝ η x‖ ≤ A / ρ) := by
  obtain ⟨A, _, hA, _, hAderiv, _⟩ :=
    Poincare.Parabolic.Interior.exists_unit_cutoff_derivative_bounds
      (E := EuclideanSpace ℝ (Fin n))
  refine ⟨A, hA, fun z ρ hρ => ?_⟩
  let χ := Poincare.Parabolic.Interior.unitSpatialBump (E := EuclideanSpace ℝ (Fin n))
  let η := Poincare.Parabolic.Interior.rescaledCutoff χ z ρ
  refine ⟨η, Poincare.Parabolic.Interior.contDiff_rescaledCutoff χ.contDiff z ρ,
    Poincare.Parabolic.Interior.hasCompactSupport_rescaled_unit_cutoff hρ z,
    Poincare.Parabolic.Interior.tsupport_rescaled_unit_cutoff_subset hρ z,
    Poincare.Parabolic.Interior.rescaled_unit_cutoff_mem_Icc z ρ, ?_, ?_⟩
  · intro x hx
    apply χ.one_of_mem_closedBall
    change dist (ρ⁻¹ • (x - z)) 0 ≤ (1 / 2 : ℝ)
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),
      ← div_eq_inv_mul, div_le_iff₀ hρ]
    have hx' : ‖x - z‖ ≤ ρ / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    linarith
  · exact Poincare.Parabolic.Interior.norm_fderiv_rescaledCutoff_le χ.contDiff hρ hAderiv z



theorem exists_uniform_energy_power_step (hn : 2 ≤ n)
    {a b P : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hP : 0 ≤ P) :
    ∃ q : ℝ≥0, (q : ℝ) = 2 * n / (n - 1) ∧ 2 < q ∧
      ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ R : ℝ, 0 < R →
        ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
          (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
            a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
              g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
          ∀ z : EuclideanSpace ℝ (Fin n), ∀ ρ : ℝ, 0 < ρ →
            Metric.closedBall z ρ ⊆ Metric.ball 0 R →
          ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 < f x) →
          ∀ p κ : ℝ, 1 ≤ p → 0 ≤ κ →
            (∀ η : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ η →
              HasCompactSupport η → tsupport η ⊆ Metric.ball 0 R →
              (∫ x, g.inner x (D.gradient (fun y => η y * f y ^ p) x)
                (D.gradient (fun y => η y * f y ^ p) x) ∂g.volumeMeasure) ≤
                P * p ^ 2 * (κ * (∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure) +
                  ∫ x, (f x ^ p) ^ 2 *
                    g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure)) →
            (eLpNorm (fun x => f x ^ p) q
              (volume.restrict (Metric.closedBall z (ρ / 2)))).toReal ^ 2 ≤
              C * R * p ^ 2 * (κ + (A / ρ) ^ 2 / a) *
                ∫ x in Metric.closedBall z ρ, (f x ^ p) ^ 2 := by
  obtain ⟨q, hqeq, hq, S, hS, hSob⟩ := exists_uniform_coordinate_sobolev_scale hn ha hb
  obtain ⟨A, hA, hcut⟩ := exists_scaled_energy_cutoff (n := n)
  refine ⟨q, hqeq, hq, S * P * Real.sqrt (b ^ n), A, by positivity, hA,
    fun R hR g D hell z ρ hρ hball f hf hpos p κ hp hκ henergy => ?_⟩
  obtain ⟨η, hη, hηc, hηS, hηbound, hone, hderiv⟩ := hcut z ρ hρ
  have hfp : ContDiff ℝ ∞ (fun x => f x ^ p) := contMDiff_iff_contDiff.mp
    (LeviCivitaData.contMDiff_rpow_of_pos (contMDiff_iff_contDiff.mpr hf) hpos p)
  have hηfp : ContDiff ℝ ∞ (fun x => η x * f x ^ p) := hη.mul hfp
  have hηfpc : HasCompactSupport (fun x => η x * f x ^ p) := hηc.mul_right
  have hηfps : tsupport (fun x => η x * f x ^ p) ⊆ Metric.ball 0 R :=
    (tsupport_mul_subset_left (f := η) (g := fun x => f x ^ p)).trans (hηS.trans hball)
  have hmem : MemLp (fun x => η x * f x ^ p) q volume :=
    hηfp.continuous.memLp_of_hasCompactSupport hηfpc
  have hnorm := ENNReal.toReal_mono hmem.eLpNorm_ne_top
    (eLpNorm_inner_le_cutoff Metric.isClosed_closedBall.measurableSet hone q)
  have hnorm2 := (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hnorm
  have hs := hSob R hR g D hell _ hηfp hηfpc hηfps
  have he := henergy η hη hηc (hηS.trans hball)
  have hweight := weighted_cutoff_energy_le D (isCompact_closedBall z ρ) hη hfp.continuous
    hηS (fun x _ => by rw [abs_of_nonneg (hηbound x).1]; exact (hηbound x).2)
    ha (div_nonneg hA hρ.le) hκ (fun x hx v => (hell x (hball hx) v).1)
    (fun x _ => hderiv x)
  have hvol := setIntegral_sq_le_of_ellipticity (g := g) (isCompact_closedBall z ρ) ha
    (fun x hx => hell x (hball hx)) hfp.continuous
  calc
    _ ≤ S * R * (P * p ^ 2 *
        ((κ + (A / ρ) ^ 2 / a) * ∫ x in Metric.closedBall z ρ, (f x ^ p) ^ 2
          ∂g.volumeMeasure)) :=
      hnorm2.trans (hs.trans (mul_le_mul_of_nonneg_left
        (he.trans (mul_le_mul_of_nonneg_left hweight (by positivity))) (by positivity)))
    _ ≤ S * R * (P * p ^ 2 *
        ((κ + (A / ρ) ^ 2 / a) * (Real.sqrt (b ^ n) *
          ∫ x in Metric.closedBall z ρ, (f x ^ p) ^ 2))) := by
      gcongr
    _ = _ := by ring

end PoincareConjecture.HarmonicCoordinates
