import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.LocalGain
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateEnergy

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem setIntegral_sq_le_of_ellipticity
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    {a b : ℝ} (ha : 0 < a)
    (hell : ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hV : Continuous V) :
    (∫ x in S, V x ^ 2 ∂g.volumeMeasure) ≤ Real.sqrt (b ^ n) * ∫ x in S, V x ^ 2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := OpenPartialHomeomorph.refl E
  have heq : (e : E → E) = id := rfl
  have himage : e '' S = S := by simp only [heq, image_id]
  have hint := integral_compact_image_eq_pullback_density (g := g) e
    contMDiffOn_id contMDiffOn_id hS (by simp [e]) (hV.pow 2).measurable
  rw [himage] at hint
  simp only [heq, id_eq] at hint
  change (∫ x in S, V x ^ 2 ∂g.volumeMeasure) =
    ∫ x in S, V x ^ 2 * g.pullbackVolumeDensity id x at hint
  rw [hint, ← integral_const_mul]
  have hρ : Continuous (g.pullbackVolumeDensity id) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (g.contDiffAt_pullbackVolumeDensity contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt
  apply setIntegral_mono_on
    (((hV.pow 2).mul hρ).continuousOn.integrableOn_compact hS)
    ((continuous_const.mul (hV.pow 2)).continuousOn.integrableOn_compact hS) hS.measurableSet
  intro x hx
  change V x ^ 2 * g.pullbackVolumeDensity id x ≤ Real.sqrt (b ^ n) * V x ^ 2
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (g.pullbackVolumeDensity_id_bounds x ha (hell x hx)).2 (sq_nonneg (V x))

theorem eLpNorm_inner_le_cutoff {η V : EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hone : ∀ x ∈ S, η x = 1) (q : ℝ≥0∞) :
    eLpNorm V q (volume.restrict S) ≤ eLpNorm (fun x => η x * V x) q volume := by
  have heq : V =ᵐ[volume.restrict S] fun x => η x * V x := by
    filter_upwards [ae_restrict_mem hS] with x hx
    simp [hone x hx]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

theorem exists_uniform_ball_power_step (hn : 2 ≤ n)
    (R : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ z : EuclideanSpace ℝ (Fin n), ∀ ρ : ℝ, 0 < ρ →
          Metric.closedBall z ρ ⊆ Metric.ball 0 R →
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 < f x) →
        ∀ p κ : ℝ, 1 ≤ p → 0 ≤ κ →
          (∀ x ∈ Metric.closedBall z ρ, -κ * f x ≤ D.laplacian f x) →
          (eLpNorm (fun x => f x ^ p) q (volume.restrict (Metric.closedBall z (ρ / 2)))).toReal ^ 2 ≤
            (C * (p * κ + (A / ρ) ^ 2 / a)) *
              ∫ x in Metric.closedBall z ρ, (f x ^ p) ^ 2 := by
  obtain ⟨q, hq, C, A, hC, hA, hgain⟩ := exists_uniform_scaled_cutoff_power_gain hn R ha hb
  refine ⟨q, hq, C * Real.sqrt (b ^ n), A, mul_nonneg hC (Real.sqrt_nonneg _), hA,
    fun g D hell z ρ hρ hball f hf hpos p κ hp hκ hlap => ?_⟩
  obtain ⟨η, hη, hηc, -, -, hone, hstep⟩ := hgain g D hell z ρ hρ hball
  have hfp : ContDiff ℝ ∞ (fun x => f x ^ p) := contMDiff_iff_contDiff.mp
    (LeviCivitaData.contMDiff_rpow_of_pos (contMDiff_iff_contDiff.mpr hf) hpos p)
  have hmem : MemLp (fun x => η x * f x ^ p) q volume :=
    (hη.continuous.mul hfp.continuous).memLp_of_hasCompactSupport hηc.mul_right
  have hnorm := ENNReal.toReal_mono hmem.eLpNorm_ne_top
    (eLpNorm_inner_le_cutoff Metric.isClosed_closedBall.measurableSet hone q)
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hnorm
  have hvolume := setIntegral_sq_le_of_ellipticity (g := g) (isCompact_closedBall z ρ) ha
    (fun x hx => hell x (hball hx)) hfp.continuous
  calc
    _ ≤ (C * (p * κ + (A / ρ) ^ 2 / a)) *
        ∫ x in Metric.closedBall z ρ, (f x ^ p) ^ 2 ∂g.volumeMeasure :=
      hsquare.trans (hstep f hf hpos p κ hp hκ hlap)
    _ ≤ (C * (p * κ + (A / ρ) ^ 2 / a)) *
        (Real.sqrt (b ^ n) * ∫ x in Metric.closedBall z ρ, (f x ^ p) ^ 2) :=
      mul_le_mul_of_nonneg_left hvolume (by positivity)
    _ = _ := by ring

end PoincareConjecture.HarmonicCoordinates
