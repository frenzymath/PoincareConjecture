import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Powers
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Cutoffs







noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem weighted_cutoff_energy_le (D : LeviCivitaData g)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    {η V : EuclideanSpace ℝ (Fin n) → ℝ} (hη : ContDiff ℝ ∞ η) (hV : Continuous V)
    (hηS : tsupport η ⊆ S) (hηbound : ∀ x ∈ S, |η x| ≤ 1)
    {a L κ : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hell : ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v)
    (hderiv : ∀ x ∈ S, ‖fderiv ℝ η x‖ ≤ L) :
    κ * (∫ x, η x ^ 2 * V x ^ 2 ∂g.volumeMeasure) +
      (∫ x, V x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) ≤
      (κ + L ^ 2 / a) * ∫ x in S, V x ^ 2 ∂g.volumeMeasure := by
  have hηs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η := contMDiff_iff_contDiff.mpr hη
  have hmass : (∫ x, η x ^ 2 * V x ^ 2 ∂g.volumeMeasure) ≤
      ∫ x in S, V x ^ 2 ∂g.volumeMeasure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := S) (fun x hx => by
        have hxs : x ∉ tsupport η := fun h => hx (hηS h)
        simp [image_eq_zero_of_notMem_tsupport hxs])]
    apply setIntegral_mono_on
      (((hη.continuous.pow 2).mul (hV.pow 2)).continuousOn.integrableOn_compact hS)
      ((hV.pow 2).continuousOn.integrableOn_compact hS) hS.measurableSet
    intro x hx
    change η x ^ 2 * V x ^ 2 ≤ V x ^ 2
    have hs : η x ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ (abs_nonneg (η x)) (by norm_num)).mpr (hηbound x hx)
      simpa only [sq_abs, one_pow] using h
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (V x))
  have herror : (∫ x, V x ^ 2 *
      g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) ≤
      (L ^ 2 / a) * ∫ x in S, V x ^ 2 ∂g.volumeMeasure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := S) (fun x hx => by
        have hxs : x ∉ tsupport η := fun h => hx (hηS h)
        simp [D.gradient_eq_zero_of_notMem_tsupport hxs]), ← integral_const_mul]
    apply setIntegral_mono_on
      (((hV.pow 2).mul (D.continuous_inner_gradient hηs hηs)).continuousOn.integrableOn_compact hS)
      ((continuous_const.mul (hV.pow 2)).continuousOn.integrableOn_compact hS) hS.measurableSet
    intro x hx
    change V x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ≤ (L ^ 2 / a) * V x ^ 2
    have hgrad := (gradient_energy_le_fderiv_sq D η x ha (hell x hx)).trans
      (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hL).mpr (hderiv x hx)) ha.le)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hgrad (sq_nonneg (V x))
  calc
    _ ≤ κ * (∫ x in S, V x ^ 2 ∂g.volumeMeasure) +
        (L ^ 2 / a) * ∫ x in S, V x ^ 2 ∂g.volumeMeasure :=
      add_le_add (mul_le_mul_of_nonneg_left hmass hκ) herror
    _ = _ := by ring



theorem exists_uniform_local_power_gain (hn : 2 ≤ n)
    (R : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S → S ⊆ Metric.ball 0 R →
        ∀ η f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ η → ContDiff ℝ ∞ f →
          tsupport η ⊆ S → (∀ x ∈ S, |η x| ≤ 1) → (∀ x, 0 < f x) →
        ∀ p κ L : ℝ, 1 ≤ p → 0 ≤ κ → 0 ≤ L →
          (∀ x ∈ S, ‖fderiv ℝ η x‖ ≤ L) →
          (∀ x ∈ tsupport η, -κ * f x ≤ D.laplacian f x) →
          (eLpNorm (fun x => η x * f x ^ p) q volume).toReal ^ 2 ≤
            (C * (p * κ + L ^ 2 / a)) * ∫ x in S, (f x ^ p) ^ 2 ∂g.volumeMeasure := by
  obtain ⟨q, hq, C, hC, hSob⟩ := exists_uniform_subsolution_power_sobolev hn R ha hb
  refine ⟨q, hq, C, hC, fun g D hell S hS hSR η f hη hf hηS hηbound hpos p κ L
    hp hκ hL hderiv hlap => ?_⟩
  have hηc : HasCompactSupport η := hS.of_isClosed_subset (isClosed_tsupport η) hηS
  have hfp : ContDiff ℝ ∞ (fun x => f x ^ p) := contMDiff_iff_contDiff.mp
    (LeviCivitaData.contMDiff_rpow_of_pos (contMDiff_iff_contDiff.mpr hf) hpos p)
  have h := hSob g D hell η f hη hf hηc (hηS.trans hSR) hpos p κ hp hlap
  have hweight := weighted_cutoff_energy_le D hS hη hfp.continuous hηS hηbound ha hL
    (mul_nonneg (le_trans (by norm_num) hp) hκ) (fun x hx v => (hell x (hSR hx) v).1) hderiv
  exact (h.trans (mul_le_mul_of_nonneg_left hweight hC)).trans_eq (by ring)



theorem exists_uniform_scaled_cutoff_power_gain (hn : 2 ≤ n)
    (R : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ z : EuclideanSpace ℝ (Fin n), ∀ ρ : ℝ, 0 < ρ →
          Metric.closedBall z ρ ⊆ Metric.ball 0 R →
          ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
            ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
            tsupport η ⊆ Metric.closedBall z ρ ∧ (∀ x, η x ∈ Icc 0 1) ∧
            (∀ x ∈ Metric.closedBall z (ρ / 2), η x = 1) ∧
            ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 < f x) →
            ∀ p κ : ℝ, 1 ≤ p → 0 ≤ κ →
              (∀ x ∈ Metric.closedBall z ρ, -κ * f x ≤ D.laplacian f x) →
              (eLpNorm (fun x => η x * f x ^ p) q volume).toReal ^ 2 ≤
                (C * (p * κ + (A / ρ) ^ 2 / a)) *
                  ∫ x in Metric.closedBall z ρ, (f x ^ p) ^ 2 ∂g.volumeMeasure := by
  obtain ⟨q, hq, C, hC, hgain⟩ := exists_uniform_local_power_gain hn R ha hb
  obtain ⟨A, _, hA, _, hAderiv, _⟩ :=
    Poincare.Parabolic.Interior.exists_unit_cutoff_derivative_bounds
      (E := EuclideanSpace ℝ (Fin n))
  refine ⟨q, hq, C, A, hC, hA, fun g D hell z ρ hρ hball => ?_⟩
  let χ := Poincare.Parabolic.Interior.unitSpatialBump (E := EuclideanSpace ℝ (Fin n))
  let η := Poincare.Parabolic.Interior.rescaledCutoff χ z ρ
  have hη : ContDiff ℝ ∞ η := Poincare.Parabolic.Interior.contDiff_rescaledCutoff χ.contDiff z ρ
  have hc : HasCompactSupport η :=
    Poincare.Parabolic.Interior.hasCompactSupport_rescaled_unit_cutoff hρ z
  have hs : tsupport η ⊆ Metric.closedBall z ρ :=
    Poincare.Parabolic.Interior.tsupport_rescaled_unit_cutoff_subset hρ z
  have hrange (x) : η x ∈ Icc (0 : ℝ) 1 :=
    Poincare.Parabolic.Interior.rescaled_unit_cutoff_mem_Icc z ρ x
  refine ⟨η, hη, hc, hs, hrange, ?_, ?_⟩
  · intro x hx
    apply χ.one_of_mem_closedBall
    change dist (ρ⁻¹ • (x - z)) 0 ≤ (1 / 2 : ℝ)
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),
      ← div_eq_inv_mul, div_le_iff₀ hρ]
    have hx' : ‖x - z‖ ≤ ρ / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    linarith
  · intro f hf hpos p κ hp hκ hlap
    apply hgain g D hell (Metric.closedBall z ρ) (isCompact_closedBall z ρ) hball
      η f hη hf hs (fun x _ => by rw [abs_of_nonneg (hrange x).1]; exact (hrange x).2)
      hpos p κ (A / ρ) hp hκ (div_nonneg hA hρ.le)
    · intro x _
      exact Poincare.Parabolic.Interior.norm_fderiv_rescaledCutoff_le χ.contDiff hρ hAderiv z x
    · exact fun x hx => hlap x (hs hx)

end PoincareConjecture.HarmonicCoordinates
