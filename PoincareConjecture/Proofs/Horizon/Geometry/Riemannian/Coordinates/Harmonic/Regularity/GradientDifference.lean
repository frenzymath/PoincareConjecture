import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorCaccioppoli
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.ReferenceFieldBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.EnergyMeanValue








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal BigOperators

namespace PoincareConjecture.HarmonicCoordinates




theorem exists_uniform_gradient_difference_mean_value {n : ℕ} (hn : 2 ≤ n)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 r, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 r, D.curvatureTensorNorm x ≤ K) →
        ∀ z : EuclideanSpace ℝ (Fin n), Metric.closedBall z (r / 2) ⊆ Metric.ball 0 r →
        ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          ContDiff ℝ ∞ f → ContDiff ℝ ∞ X →
          (∀ x ∈ Metric.ball 0 r, D.laplacian f =ᶠ[𝓝 x] fun _ => 0) →
          ∀ B s : ℝ, 0 < s → r ^ 2 * (n : ℝ) * K * B ≤ s →
            (∀ x ∈ Metric.ball 0 r, g.tangentNorm x (X x) ≤ B) →
            (∀ x ∈ Metric.ball 0 r,
              (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
                (D.connection X x (g.orthonormalBasis x i))) ≤ (s / r) ^ 2) →
            let V := fun x => (show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x
            g.inner z (V z) (V z) + s ^ 2 ≤
              C * r ^ (-(n : ℝ)) *
                ((∫ x in Metric.closedBall z (r / 2), g.inner x (V x) (V x)) +
                  volume.real (Metric.closedBall z (r / 2)) * s ^ 2) := by
  let Λ := (n : ℝ) * K + 2
  have hΛ : 0 ≤ Λ := by dsimp only [Λ]; positivity
  obtain ⟨M, hM, hmean⟩ := exists_uniform_energy_mean_value hn ha hb
    (by norm_num : (0 : ℝ) ≤ 22) hΛ
  refine ⟨M ^ 2, by nlinarith, fun r hr hr1 g D hell hcurv z hball f X hf hX hharm
    B s hs hscale hXB hXE => ?_⟩
  let V := fun x => (show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x
  let Q := fun x => g.inner x (V x) (V x)
  let w := fun x => Real.sqrt (Q x + s ^ 2)
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hV : ContDiff ℝ ∞ V :=
    (contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient hfs)).sub hX
  have hVs := contMDiff_vectorSpace_iff_contDiff.mpr hV
  have hQ : Continuous Q := (LeviCivitaData.contMDiff_vector_normSq hVs).continuous
  have hQ0 (x) : 0 ≤ Q x := by
    by_cases hx : V x = 0
    · simp [Q, hx]
    · exact (g.pos x _ hx).le
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hw : ContDiff ℝ ∞ w := contMDiff_iff_contDiff.mp
    (LeviCivitaData.contMDiff_regularized_vector_norm hVs hs2)
  have hwpos (x) : 0 < w x := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (hQ0 x) hs2)
  have hw2 (x) : w x ^ 2 = Q x + s ^ 2 := Real.sq_sqrt (add_nonneg (hQ0 x) hs2.le)
  have hmass : (n : ℝ) * K + (r ^ 2)⁻¹ + (r ^ 2)⁻¹ ≤ Λ / r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hr21 : r ^ 2 ≤ 1 := by nlinarith
    apply (le_div_iff₀ hr2).mpr
    dsimp only [Λ]
    rw [add_mul, add_mul, inv_mul_cancel₀ hr2.ne']
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK
    nlinarith
  have henergy (p : ℝ) (hp : 1 ≤ p) (η : EuclideanSpace ℝ (Fin n) → ℝ)
      (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Metric.ball 0 r) :
      (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
        (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
        22 * p ^ 2 * ((Λ / r ^ 2) * (∫ x, η x ^ 2 * (w x ^ p) ^ 2 ∂g.volumeMeasure) +
          ∫ x, (w x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)
            ∂g.volumeMeasure) := by
    have hRic (x) (hx : x ∈ tsupport η) :
        -((n : ℝ) * K + (r ^ 2)⁻¹) * (Q x + s ^ 2) ≤
          D.ricci x (D.gradient f x) (V x) := by
      have h := D.ricci_reference_lower_bound x (D.gradient f x) (X x) hr hs
        (hcurv x (hηs hx)) (hXB x (hηs hx)) hscale
      change -(((n : ℝ) * K + (r ^ 2)⁻¹) * w x ^ 2) ≤ _ at h
      simpa only [hw2, neg_mul] using h
    have hconn (x) (hx : x ∈ tsupport η) :
        (∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
          (D.connection X x (g.orthonormalBasis x i))) ≤ (r ^ 2)⁻¹ * (Q x + s ^ 2) := by
      have h := D.reference_connection_energy_le X x (V x) (hXE x (hηs hx))
      change _ ≤ (r ^ 2)⁻¹ * w x ^ 2 at h
      simpa only [hw2] using h
    have h := D.regularized_gradient_sub_power_caccioppoli hf hX hη hηc hs2 hp
      (show 0 ≤ (n : ℝ) * K + (r ^ 2)⁻¹ by positivity)
      (show 0 ≤ (r ^ 2)⁻¹ by positivity)
      (fun x hx => hharm x (hηs hx)) hRic hconn
    refine h.trans ?_
    change 22 * p ^ 2 * (_ + (((n : ℝ) * K + (r ^ 2)⁻¹) + (r ^ 2)⁻¹) * _) ≤ _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [add_comm]
    apply add_le_add _ le_rfl
    exact mul_le_mul_of_nonneg_right hmass
      (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have h := hmean r hr hr1 g D hell z hball w hw hwpos henergy
  have hsquare := (sq_le_sq₀ (hwpos z).le
    (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (Real.rpow_nonneg hr.le _))
      ENNReal.toReal_nonneg)).mpr h
  rw [hw2, mul_pow, mul_pow,
    Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral
      (continuous_memLp_restrict_closedBall hw.continuous z (r / 2) 2)] at hsquare
  have hrpow : (r ^ (-(n : ℝ) / 2)) ^ 2 = r ^ (-(n : ℝ)) := by
    rw [← Real.rpow_mul_natCast hr.le]
    congr 1
    ring
  rw [hrpow] at hsquare
  simp_rw [hw2] at hsquare
  have hQi : IntegrableOn Q (Metric.closedBall z (r / 2)) :=
    hQ.continuousOn.integrableOn_compact (isCompact_closedBall z (r / 2))
  rw [integral_add hQi (integrableOn_const (isCompact_closedBall z (r / 2)).measure_lt_top.ne),
    setIntegral_const, smul_eq_mul] at hsquare
  exact hsquare

end PoincareConjecture.HarmonicCoordinates
