import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.LocalIsometry











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {G : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

namespace RiemannianMetric




theorem exists_uniform_pullback_extension_with_curvature
    (g : RiemannianMetric n M) (Dg : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hbound : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ∧
        g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ 3 * ‖v‖ / 2)
    (hgauss : ∀ x ∈ Metric.ball 0 R, ∀ v,
      g.pullbackCoefficients e x x v = inner ℝ x v) :
    ∃ (G : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DG : LeviCivitaData G),
      (∀ x ∈ Metric.closedBall 0 r,
        G.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e) ∧
      (∀ x v : EuclideanSpace ℝ (Fin n), ‖v‖ / 2 ≤ G.tangentNorm x v ∧
        G.tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
      (∀ x v, G.inner x x v = inner ℝ x v) ∧
      (∀ x, R ≤ ‖x‖ → G.euclideanCoefficients x = innerSL ℝ) ∧
      ∀ x ∈ Metric.closedBall 0 r, DG.curvatureTensorNorm x = Dg.curvatureTensorNorm (e x) := by
  obtain ⟨G, hag, hnorm, hGauss, hflat⟩ :=
    exists_uniform_pullback_extension g hr hrR he hbound hgauss
  let DG := G.euclideanLeviCivitaData
  refine ⟨G, DG, hag, hnorm, hGauss, hflat, ?_⟩
  intro x hx
  have hxR : x ∈ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR hx
  exact DG.curvatureTensorNorm_eq_of_pullback_germ Dg
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hxR)) (hag x hx)

end RiemannianMetric

end PoincareConjecture
