import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.GradientDifference
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal BigOperators

namespace PoincareConjecture.HarmonicCoordinates




theorem exists_uniform_local_gradient_difference_mean_value {n : ℕ} (hn : 2 ≤ n)
    {a b K : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R r : ℝ, 0 < r → r ≤ 1 →
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 R →
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 r, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 r, D.curvatureTensorNorm x ≤ K) →
        ∀ z : EuclideanSpace ℝ (Fin n), Metric.closedBall z (r / 2) ⊆ Metric.ball 0 r →
        ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
          (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
          ContDiffOn ℝ ∞ f (Metric.ball 0 R) → ContDiff ℝ ∞ X →
          (∀ x ∈ Metric.ball 0 R, D.laplacian f x = 0) →
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
  obtain ⟨C, hC, hmean⟩ := exists_uniform_gradient_difference_mean_value hn ha hb hK
  refine ⟨C, hC, fun R r hr hr1 hclosed g D hell hcurv z hball f X hf hX hharm
    B s hs hscale hXB hXE => ?_⟩
  obtain ⟨F, hF, -, hFf⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball hclosed hf
  have hharmF (x) (hx : x ∈ Metric.ball 0 r) :
      D.laplacian F =ᶠ[𝓝 x] fun _ => 0 := by
    have hxcl := Metric.ball_subset_closedBall hx
    filter_upwards [(hFf x hxcl).eventually_nhds,
      Metric.isOpen_ball.mem_nhds (hclosed hxcl)] with y hy hyR
    rw [D.laplacian_eq_of_eventuallyEq hy]
    exact hharm y hyR
  have hgrad (x) (hx : x ∈ Metric.closedBall 0 r) : D.gradient F x = D.gradient f x := by
    simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq (hFf x hx)]
  have h := hmean r hr hr1 g D hell hcurv z hball F X hF hX hharmF
    B s hs hscale hXB hXE
  dsimp only at h ⊢
  have hz : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r :=
    Metric.ball_subset_closedBall (hball (Metric.mem_closedBall_self (by positivity)))
  rw [hgrad z hz] at h
  have hint : (∫ x in Metric.closedBall z (r / 2),
      g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient F x) - X x)
        ((show EuclideanSpace ℝ (Fin n) from D.gradient F x) - X x)) =
      ∫ x in Metric.closedBall z (r / 2),
        g.inner x ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x)
          ((show EuclideanSpace ℝ (Fin n) from D.gradient f x) - X x) := by
    apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
    intro x hx
    dsimp only
    rw [hgrad x (Metric.ball_subset_closedBall (hball hx))]
  rw [hint] at h
  exact h

end PoincareConjecture.HarmonicCoordinates
