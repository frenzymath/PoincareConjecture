import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.Caccioppoli
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.SourceBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.EnergyMeanValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal BigOperators

namespace PoincareConjecture.HarmonicCoordinates

theorem exists_uniform_hessian_mean_value {n : ℕ} (hn : 2 ≤ n)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 r, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 r, D.curvatureTensorNorm x ≤ K) →
        ∀ G : ℝ, 0 ≤ G → ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
          ContDiff ℝ ∞ f →
          (∀ x ∈ Metric.ball 0 r, D.laplacian f =ᶠ[𝓝 x] fun _ => 0) →
          (∀ x ∈ Metric.ball 0 r, g.tangentNorm x (D.gradient f x) ≤ G) →
          ∀ z : EuclideanSpace ℝ (Fin n), Metric.closedBall z (r / 2) ⊆ Metric.ball 0 r →
            let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
              fun y v => D.hessian f y (v 0) (v 1)
            let Q := g.tensorPairingTwo H H
            let σ := 1 + Real.sqrt ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * K ^ 2 * G ^ 2)
            let s := σ * r
            Q z + s ^ 2 ≤ C * r ^ (-(n : ℝ)) *
              ((∫ x in Metric.closedBall z (r / 2), Q x) +
                volume.real (Metric.closedBall z (r / 2)) * s ^ 2) := by
  let κ := 2 * (n : ℝ) ^ 2 * K
  let Λ := κ + 1
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have hΛ : 0 ≤ Λ := by dsimp only [Λ]; positivity
  obtain ⟨M, hM, hmean⟩ := exists_uniform_energy_mean_value hn ha hb
    (by norm_num : (0 : ℝ) ≤ 22) hΛ
  refine ⟨M ^ 2, by nlinarith, fun r hr hr1 g D hell hcurv G _hG f hf hharm hgrad z hball => ?_⟩
  let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
    fun y v => D.hessian f y (v 0) (v 1)
  let Q := g.tensorPairingTwo H H
  let B₀ := (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * K ^ 2 * G ^ 2
  let σ := 1 + Real.sqrt B₀
  let s := σ * r
  let w := fun x => Real.sqrt (Q x + s ^ 2)
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hs : 0 < s := mul_pos hσ hr
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hscale : B₀ ≤ (r ^ 2)⁻¹ * s ^ 2 := by
    have hσsq : B₀ ≤ σ ^ 2 := by
      have hsqrt := Real.sq_sqrt hB₀
      dsimp only [σ]
      nlinarith only [hsqrt, Real.sqrt_nonneg B₀]
    have hcancel : (r ^ 2)⁻¹ * s ^ 2 = σ ^ 2 := by
      dsimp only [s]
      rw [mul_pow]
      field_simp [hr.ne']
    rw [hcancel]
    exact hσsq
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hH : IsSmoothCovariantTensor H := D.hessian_isSmoothCovariantTensor hfs
  have hQ : Continuous Q := (D.contMDiff_tensorPairingTwo hH hH).continuous
  have hQ0 (x) : 0 ≤ Q x := g.tensorPairingTwo_self_nonneg H x
  have hw : ContDiff ℝ ∞ w := contMDiff_iff_contDiff.mp
    (D.contMDiff_regularized_tensor_norm hH hs2)
  have hwpos (x) : 0 < w x := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (hQ0 x) hs2)
  have hw2 (x) : w x ^ 2 = Q x + s ^ 2 := Real.sq_sqrt (add_nonneg (hQ0 x) hs2.le)
  have hmass : κ + (r ^ 2)⁻¹ ≤ Λ / r ^ 2 := by
    have hr21 : r ^ 2 ≤ 1 := by nlinarith
    apply (le_div_iff₀ hr2).mpr
    dsimp only [Λ]
    rw [add_mul, inv_mul_cancel₀ hr2.ne']
    nlinarith only [mul_le_mul_of_nonneg_left hr21 hκ]
  have henergy (p : ℝ) (hp : 1 ≤ p) (η : EuclideanSpace ℝ (Fin n) → ℝ)
      (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Metric.ball 0 r) :
      (∫ x, g.inner x (D.gradient (fun y => η y * w y ^ p) x)
        (D.gradient (fun y => η y * w y ^ p) x) ∂g.volumeMeasure) ≤
        22 * p ^ 2 * ((Λ / r ^ 2) * (∫ x, η x ^ 2 * (w x ^ p) ^ 2 ∂g.volumeMeasure) +
          ∫ x, (w x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)
            ∂g.volumeMeasure) := by
    have hA (x) (hx : x ∈ tsupport η) :
        -κ * (Q x + s ^ 2) ≤ g.tensorPairingTwo (D.twoTensorCurvatureTrace H) H x :=
      D.twoTensorCurvatureTrace_regularized_lower hH x (hcurv x (hηs hx)) hs2.le
    have hB (x) (hx : x ∈ tsupport η) :
        g.tensorPairingThree (D.hessianCurvatureFlux f) (D.hessianCurvatureFlux f) x ≤
          (r ^ 2)⁻¹ * (Q x + s ^ 2) :=
      D.hessianCurvatureFlux_regularized_energy_le f x
        (show 0 ≤ (r ^ 2)⁻¹ by positivity) (hcurv x (hηs hx)) (hgrad x (hηs hx)) hscale
    have h := D.regularized_hessian_power_caccioppoli hf hη hηc hs2 hp hκ
      (show 0 ≤ (r ^ 2)⁻¹ by positivity) (fun x hx => hharm x (hηs hx)) hA hB
    refine h.trans ?_
    change 22 * p ^ 2 * (_ + (κ + (r ^ 2)⁻¹) * _) ≤ _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [add_comm]
    apply add_le_add _ le_rfl
    exact mul_le_mul_of_nonneg_right hmass
      (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have h := hmean r hr hr1 g D hell z hball w hw hwpos henergy
  have hsquare := (sq_le_sq₀ (hwpos z).le
    (mul_nonneg (mul_nonneg (zero_le_one.trans hM) (Real.rpow_nonneg hr.le _))
      ENNReal.toReal_nonneg)).mpr h
  rw [hw2, mul_pow (M * r ^ (-(n : ℝ) / 2)) _ 2,
    mul_pow M (r ^ (-(n : ℝ) / 2)) 2,
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
