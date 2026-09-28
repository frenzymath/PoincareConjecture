import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundModelBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PullbackMetricJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactGauss











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)





theorem exists_round_model_coordinate_bounds :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g),
      IsCompact (univ : Set M) →
      (∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
        D.sectionalCurvature x v w = 1) →
      ∀ p : M, ∃ e : E → M,
        e 0 = p ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (Metric.ball 0 (2 * r)) ∧
        (∀ x ∈ Metric.ball 0 (2 * r), (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) ∧
        (∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w) ∧
        (∀ x ∈ Metric.closedBall (0 : E) r, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e x v v ∧
            g.pullbackCoefficients e x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
        ∀ j, ∀ x ∈ Metric.closedBall (0 : E) r,
          ‖iteratedFDeriv ℝ j (g.pullbackCoefficients e) x‖ ≤ B j := by
  obtain ⟨r, hr, hr1, hsmall⟩ :=
    RiemannianMetric.exists_uniform_radial_comparison_radius
      (by norm_num : (0 : ℝ) < 1) 9
  obtain ⟨B, hB, hjet⟩ := CoordinateExponential.exists_uniform_pullback_metric_jet_bounds
    3 hr (by linarith : r < 2 * r) (fun _ => (9 : ℝ)) (fun _ => by norm_num)
  refine ⟨r, hr, B, hB, ?_⟩
  intro M _ _ _ _ g D hcompact hsec p
  have hball : IsCompact (closure (g.ball p 1)) :=
    hcompact.of_isClosed_subset isClosed_closure (subset_univ _)
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p
      (by norm_num : (0 : ℝ) < 1) hball
  have hnorm : ∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w :=
    g.pullbackCoefficients_zero_of_normalized_chart
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num))))
      he0 hed hL
  have hbound := g.radial_exponential_uniform_bounds D hr1 hsmall he hnorm hgeo
    (fun x _ => curvatureTensorNorm_le_nine_of_sectional_one D hsec x)
  have he' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (Metric.ball 0 (2 * r)) :=
    he.mono (Metric.ball_subset_ball hr1.le)
  have hinv (x : E) (hx : x ∈ Metric.ball 0 (2 * r)) :
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible :=
    (hbound x (Metric.ball_subset_closedBall hx)).1
  have hgauss (x : E) (hx : x ∈ Metric.ball 0 (2 * r)) (w : E) :
      g.pullbackCoefficients e x x w = inner ℝ x w :=
    CoordinateExponential.gauss_identity_of_radial_family g he
      (fun v hv => (hgeo v hv).1) (fun v hv t ht => ((hgeo v hv).2 t ht).1)
      x (Metric.ball_subset_ball hr1.le hx) w
  refine ⟨e, he0, he', hinv, hnorm, ?_, ?_⟩
  · intro x hx v
    exact ((hbound x (Metric.closedBall_subset_closedBall (by linarith) hx)).2 v).2
  · exact hjet g D e he' hinv hnorm hgauss
      (fun m x _ => curvatureDerivativeNorm_le_nine_of_sectional_one D hsec m (e x))

end PoincareConjecture.M44
