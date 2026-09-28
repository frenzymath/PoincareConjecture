import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Lipschitz

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

theorem exists_uniform_divergence_error_extension {n : ℕ} (hn : 2 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    let V := EuclideanSpace ℝ (Fin n)
    let B₀ : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
    ∃ δ : ℝ, 0 < δ ∧ ∀ R a b K : ℝ,
      0 < R → R ≤ 1 → 0 < a → 0 ≤ b → 0 ≤ K →
      ∃ L : ℝ, 0 < L ∧
      ∀ (g : RiemannianMetric n V) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : V,
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        (∀ x ∈ Metric.ball 0 R, ∀ i : Fin n,
          D.laplacian (fun y : V => y i) x = 0) →
        (∀ x ∈ Metric.ball 0 R, ‖g.euclideanCoefficients x - B₀‖ < δ) →
        ∃ E : V → V →L[ℝ] V,
          ContDiff ℝ ∞ E ∧ HasCompactSupport E ∧
          (∀ x ∈ Metric.closedBall 0 (R / 32),
            E x = ContinuousLinearMap.id ℝ V - g.euclideanDivergenceOperator x) ∧
          (∀ x, ‖E x‖ ≤ ε) ∧ (∀ x, ‖fderiv ℝ E x‖ ≤ L) := by
  obtain ⟨δ, hδ, hcoeff⟩ := exists_uniform_divergence_operator_lipschitz hn hε
  refine ⟨δ, hδ, fun R a b K hR hR1 ha hb hK => ?_⟩
  obtain ⟨L, hL, hcoeff⟩ := hcoeff R a b K hR hR1 ha hb hK
  obtain ⟨C, hC, hcut⟩ := exists_scaled_energy_cutoff (n := n)
  let ρ := R / 16
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨η, hη, hηc, hηS, hηbound, hηone, hηder⟩ := hcut 0 ρ hρ
  refine ⟨L + C / ρ * ε, by positivity,
    fun g D hell hcurv hharm hnear => ?_⟩
  obtain ⟨hsmall, hder, _⟩ := hcoeff g D hell hcurv hharm hnear
  let A := fun x => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
    g.euclideanDivergenceOperator x
  have hA : ContDiff ℝ ∞ A := contDiff_const.sub g.contDiff_euclideanDivergenceOperator
  have hsub : tsupport η ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 8) :=
    hηS.trans (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith))
  have hsubR : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 8) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hAnorm (x) (hx : x ∈ tsupport η) : ‖A x‖ ≤ ε := by
    simpa only [A, norm_sub_rev] using (hsmall x (hsubR (hsub hx))).le
  have hAder (x) (hx : x ∈ tsupport η) : ‖fderiv ℝ A x‖ ≤ L := by
    simpa only [A, fderiv_const_sub, norm_neg] using hder x (hsub hx)
  have hηnorm (x) : ‖η x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hηbound x).1]
    exact (hηbound x).2
  refine ⟨fun x => η x • A x, hη.smul hA, hηc.smul_right, ?_, ?_, ?_⟩
  · intro x hx
    have hρhalf : ρ / 2 = R / 32 := by dsimp [ρ]; ring
    have hx' : x ∈ Metric.closedBall 0 (ρ / 2) := by simpa only [hρhalf] using hx
    change η x • A x = A x
    rw [hηone x hx', one_smul]
  · intro x
    by_cases hx : x ∈ tsupport η
    · rw [norm_smul]
      exact (mul_le_mul (hηnorm x) (hAnorm x hx) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul ε)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_smul, norm_zero]
      exact hε.le
  · intro x
    by_cases hx : x ∈ tsupport η
    · rw [fderiv_fun_smul (hη.differentiable (by simp) x) (hA.differentiable (by simp) x)]
      calc
        _ ≤ ‖η x • fderiv ℝ A x‖ + ‖(fderiv ℝ η x).smulRight (A x)‖ := norm_add_le _ _
        _ = ‖η x‖ * ‖fderiv ℝ A x‖ + ‖fderiv ℝ η x‖ * ‖A x‖ := by
          rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
        _ ≤ 1 * L + (C / ρ) * ε := add_le_add
          (mul_le_mul (hηnorm x) (hAder x hx) (norm_nonneg _) zero_le_one)
          (mul_le_mul (hηder x) (hAnorm x hx) (norm_nonneg _) (by positivity))
        _ = _ := by ring
    · have hout : x ∉ tsupport (fun y => η y • A y) :=
        fun hx' => hx (tsupport_smul_subset_left η A hx')
      rw [fderiv_of_notMem_tsupport ℝ hout, norm_zero]
      positivity

end PoincareConjecture.HarmonicCoordinates
