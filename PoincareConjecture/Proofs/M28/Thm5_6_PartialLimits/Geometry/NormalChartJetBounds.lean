import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Orthonormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactGauss

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option maxHeartbeats 800000 in

theorem exists_uniform_normal_chart_metric_jet_bound
    (n m : ℕ) {rho R : ℝ} (hrho : 0 < rho) (hrhoR : rho < R)
    (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
        (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
        (Phi : PartialDiffeomorph (𝓡 n) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) M ∞),
        Phi.source = Metric.ball 0 R →
        Phi 0 = p →
        (∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) →
        HasFDerivAt (fun w => extChartAt (𝓡 n) p (Phi w))
          L.toContinuousLinearMap 0 →
        (∀ v ∈ Metric.ball 0 R,
          g.IsGeodesicOn (fun t => Phi (t • v))
            {t : ℝ | t • v ∈ Metric.ball 0 R}) →
        (∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (Phi (t • v))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => Phi (s • v)) t 1) = ‖v‖) →
        (∀ l ≤ m, ∀ x ∈ Metric.ball 0 R,
          D.curvatureDerivativeNorm l (Phi x) ≤ C l) →
        ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) rho,
          ‖iteratedFDeriv ℝ m (g.pullbackCoefficients Phi) x‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    CoordinateExponential.exists_uniform_pullback_metric_jet_bound
      n m hrho hrhoR C hC
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ g D p L Phi hsource hzero hL hderiv hgeo hspeed hcurv
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hR : 0 < R := hrho.trans hrhoR
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Phi (Metric.ball 0 R) := by
    simpa only [hsource] using Phi.contMDiffOn
  have hi : ∀ x ∈ Metric.ball 0 R,
      (mfderiv (𝓡 n) (𝓡 n) Phi x).IsInvertible := by
    intro x hx
    exact ⟨(Phi.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      (hsource.symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)))
    hzero hderiv hL
  apply hbound g D Phi he
  · exact hi
  · exact hnorm
  · exact CoordinateExponential.gauss_identity_of_radial_family
      g he hgeo hspeed
  · exact hcurv

end PoincareConjecture.M28
