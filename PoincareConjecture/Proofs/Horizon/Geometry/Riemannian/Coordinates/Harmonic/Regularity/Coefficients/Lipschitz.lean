import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.Bounds
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

theorem exists_uniform_divergence_operator_lipschitz {n : ℕ} (hn : 2 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ∃ δ : ℝ, 0 < δ ∧ ∀ R a b K : ℝ,
      0 < R → R ≤ 1 → 0 < a → 0 ≤ b → 0 ≤ K →
      ∃ L : ℝ, 0 < L ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        (∀ x ∈ Metric.ball 0 R, ∀ i : Fin n,
          D.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y i) x = 0) →
        (∀ x ∈ Metric.ball 0 R, ‖g.euclideanCoefficients x - B₀‖ < δ) →
        (∀ x ∈ Metric.ball 0 R,
          ‖g.euclideanDivergenceOperator x -
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ < ε) ∧
        (∀ x ∈ Metric.ball 0 (R / 8),
          ‖fderiv ℝ g.euclideanDivergenceOperator x‖ ≤ L) ∧
        (∀ x ∈ Metric.ball 0 (R / 8), ∀ y ∈ Metric.ball 0 (R / 8),
          ‖g.euclideanDivergenceOperator x - g.euclideanDivergenceOperator y‖ ≤
            L * ‖x - y‖) := by
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_divergence_coefficient_tolerance (n := n) hε
  obtain ⟨δ₁, C, hδ₁, hC, hchain⟩ := exists_divergence_operator_derivative_bound (n := n)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun R a b K hR hR1 ha hb hK => ?_⟩
  obtain ⟨B, hB, hmetric⟩ :=
    exists_uniform_harmonic_metric_derivative_bound hn hR hR1 ha hb hK
  refine ⟨C * B, mul_pos hC hB,
    fun g D hell hcurv hharm hnear => ?_⟩
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 8) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hder : ∀ x ∈ Metric.ball 0 (R / 8),
      ‖fderiv ℝ g.euclideanDivergenceOperator x‖ ≤ C * B := by
    intro x hx
    exact (hchain g x ((hnear x (hsub hx)).trans_le (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_left (hmetric g D hell hcurv hharm x hx) hC.le)
  refine ⟨fun x hx => hsmall g x ((hnear x hx).trans_le (min_le_left _ _)), hder, ?_⟩
  intro x hx y hy
  exact (convex_ball (0 : EuclideanSpace ℝ (Fin n)) (R / 8)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => g.contDiff_euclideanDivergenceOperator.differentiable (by simp) z)
    hder hy hx

end PoincareConjecture.HarmonicCoordinates
