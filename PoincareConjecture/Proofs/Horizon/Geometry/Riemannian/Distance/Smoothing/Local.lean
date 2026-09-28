import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.CoordinateSemiconcavity
import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Semiconcavity









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle NNReal

namespace PoincareConjecture.RiemannianMetric



theorem exists_local_distance_smoothing
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p x : M) (hpx : p ≠ x) :
    let c := extChartAt (𝓡 n) x
    ∃ r C : ℝ, ∃ L : ℝ≥0, 0 < r ∧ 0 ≤ C ∧
      Metric.ball (c x) (2 * r) ⊆ c.target ∧
      (∀ z ∈ Metric.ball (c x) (2 * r), c.symm z ≠ p) ∧
      ∀ ε : ℝ, 0 < ε → ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ u ∧ LipschitzWith L u ∧
        (∀ z ∈ Metric.ball (c x) (2 * r),
          |u z - (g.edist p (c.symm z)).toReal| ≤ ε) ∧
        ∀ z ∈ Metric.ball (c x) r, ∀ v : EuclideanSpace ℝ (Fin n),
          fderiv ℝ (fderiv ℝ u) z v v ≤ C * ‖v‖ ^ 2 := by
  dsimp only
  obtain ⟨R, C, L, hR, hC, htarget, hne, hc, hLip⟩ :=
    g.exists_distance_coordinate_semiconcave_ball D hcomplete hK hsec p x hpx
  refine ⟨R / 2, C, L, half_pos hR, hC, ?_, ?_, ?_⟩
  · simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using htarget
  · simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hne
  · intro ε hε
    obtain ⟨u, hu, hLu, herr, hess⟩ :=
      Poincare.exists_contDiff_hessian_approx_of_lipschitzOn_ball
        (half_lt_self hR) hLip hc hε
    refine ⟨u, hu, hLu, ?_, hess⟩
    intro z hz
    have hz' : z ∈ Metric.ball ((extChartAt (𝓡 n) x) x) R := by
      simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hz
    simpa only [Real.dist_eq] using herr z hz'

end PoincareConjecture.RiemannianMetric
