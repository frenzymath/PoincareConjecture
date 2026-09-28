import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.MeanValue
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.Seed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.MetricDerivative









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle BigOperators

namespace PoincareConjecture.HarmonicCoordinates



theorem exists_uniform_hessian_bound {n : ℕ} (hn : 2 ≤ n)
    {R a b K G : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f →
          (∀ x ∈ Metric.ball 0 R, D.laplacian f =ᶠ[𝓝 x] fun _ => 0) →
          (∀ x ∈ Metric.ball 0 R, g.tangentNorm x (D.gradient f x) ≤ G) →
          ∀ z ∈ Metric.ball 0 (R / 8),
            g.tensorNorm (k := 2) (fun y v => D.hessian f y (v 0) (v 1)) z ≤ L := by
  obtain ⟨A, hA, hseed⟩ := exists_uniform_hessian_energy_seed (n := n) ha hb
  obtain ⟨M, hM, hmean⟩ := exists_uniform_hessian_mean_value hn ha hb hK
  let r := R / 4
  let ρ := R / 2
  let V := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ)
  let s := (1 + Real.sqrt ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * K ^ 2 * G ^ 2)) * r
  let C := M * r ^ (-(n : ℝ)) *
    (A * (K + (ρ ^ 2)⁻¹) * G ^ 2 * V + V * s ^ 2)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hC : 0 ≤ C := by dsimp only [C, V]; positivity
  refine ⟨Real.sqrt C + 1, by linarith [Real.sqrt_nonneg C],
    fun g D hell hcurv f hf hharm hgrad z hz => ?_⟩
  let H : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2 :=
    fun y v => D.hessian f y (v 0) (v 1)
  let Q := g.tensorPairingTwo H H
  have hH : IsSmoothCovariantTensor H :=
    D.hessian_isSmoothCovariantTensor (contMDiff_iff_contDiff.mpr hf)
  have hQ : Continuous Q := (D.contMDiff_tensorPairingTwo hH hH).continuous
  have hQ0 (x) : 0 ≤ Q x := g.tensorPairingTwo_self_nonneg H x
  have hrR : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by dsimp only [r]; linarith)
  have hz' : ‖z‖ < r / 2 := by
    have hz0 : ‖z‖ < R / 8 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    dsimp only [r]
    linarith
  have hball : Metric.closedBall z (r / 2) ⊆ Metric.ball 0 r := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x - z‖ ≤ r / 2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have htri := norm_add_le (x - z) z
    rw [sub_add_cancel] at htri
    linarith
  have hmean' := hmean r hr (by dsimp only [r]; linarith) g D
    (fun x hx => hell x (hrR hx)) (fun x hx => hcurv x (hrR hx)) G hG f hf
    (fun x hx => hharm x (hrR hx)) (fun x hx => hgrad x (hrR hx)) z hball
  change Q z + s ^ 2 ≤ M * r ^ (-(n : ℝ)) *
    ((∫ x in Metric.closedBall z (r / 2), Q x) +
      volume.real (Metric.closedBall z (r / 2)) * s ^ 2) at hmean'
  have hρ2 : 2 * ρ = R := by dsimp only [ρ]; ring
  have hseed' := hseed ρ hρ K hK g D
    (by simpa only [hρ2] using hell) (by simpa only [hρ2] using hcurv)
    f hf G hG (by simpa only [hρ2] using hgrad) (by simpa only [hρ2] using hharm)
  have hρhalf : ρ / 2 = r := by dsimp only [ρ, r]; ring
  rw [hρhalf] at hseed'
  have hmass : (∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, Q x) ≤
      A * (K + (ρ ^ 2)⁻¹) * G ^ 2 * V := by
    simpa [Q, H, V, RiemannianMetric.tensorPairingTwo, pow_two] using hseed'
  have hsub : Metric.closedBall z (r / 2) ⊆ Metric.closedBall 0 r :=
    hball.trans Metric.ball_subset_closedBall
  have hmass' : (∫ x in Metric.closedBall z (r / 2), Q x) ≤
      A * (K + (ρ ^ 2)⁻¹) * G ^ 2 * V := by
    refine (setIntegral_mono_set
      (hQ.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
      (Filter.Eventually.of_forall hQ0)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))).trans hmass
  have hvol : volume.real (Metric.closedBall z (r / 2)) ≤ V := by
    apply measureReal_mono (hsub.trans (Metric.closedBall_subset_closedBall ?_))
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ).measure_lt_top.ne
    dsimp only [r, ρ]
    linarith
  have hQC : Q z ≤ C := by
    refine (le_add_of_nonneg_right (sq_nonneg s)).trans (hmean'.trans ?_)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add hmass' (mul_le_mul_of_nonneg_right hvol (sq_nonneg s))
  have hnorm : g.tensorNorm H z ≤ Real.sqrt C := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
    change g.tensorNorm H z ^ 2 ≤ Real.sqrt C ^ 2
    rw [Real.sq_sqrt hC, ← g.tensorPairingTwo_self_eq_tensorNorm_sq]
    exact hQC
  exact hnorm.trans (le_add_of_nonneg_right zero_le_one)



theorem exists_uniform_harmonic_metric_derivative_bound {n : ℕ} (hn : 2 ≤ n)
    {R a b K : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        (∀ x ∈ Metric.ball 0 R, ∀ i : Fin n,
          D.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y i) x = 0) →
        ∀ x ∈ Metric.ball 0 (R / 8), ‖fderiv ℝ g.euclideanCoefficients x‖ ≤ B := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_hessian_bound hn hR hR1 ha hb hK
    (Real.sqrt_nonneg (1 / a))
  refine ⟨2 * Real.sqrt n * L * b ^ 2 + 1, by positivity,
    fun g D hell hcurv hharm x hx => ?_⟩
  have hxR : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R :=
    Metric.ball_subset_ball (by linarith) hx
  have hcoord (i : Fin n) : g.tensorNorm (k := 2)
      (fun y v => D.hessian (fun z : EuclideanSpace ℝ (Fin n) => z i) y (v 0) (v 1)) x ≤ L := by
    apply hbound g D hell hcurv _ (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
      (fun y hy => ?_) (fun y hy => ?_) x hx
    · filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      exact hharm z hz i
    · have hproj : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro v
        simpa only [EuclideanSpace.coe_proj, one_mul] using PiLp.norm_apply_le v i
      have henergy := gradient_energy_le_fderiv_sq D
        (EuclideanSpace.proj (𝕜 := ℝ) i) y ha (fun v => (hell y hy v).1)
      rw [ContinuousLinearMap.fderiv] at henergy
      have henergy' := henergy.trans (div_le_div_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hproj) ha.le)
      simpa only [one_pow, RiemannianMetric.tangentNorm] using Real.sqrt_le_sqrt henergy'
  exact (D.norm_fderiv_euclideanCoefficients_le_of_coordinate_hessian_bound x hb
    (zero_le_one.trans hL) (fun v => (hell x hxR v).2) hcoord).trans
      (le_add_of_nonneg_right zero_le_one)

end PoincareConjecture.HarmonicCoordinates
