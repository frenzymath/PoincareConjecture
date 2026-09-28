import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Laplacian







noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




structure UniformHarmonicLift (g : RiemannianMetric n M)
    (p : M) (r C H : ℝ) where
  e : EuclideanSpace ℝ (Fin n) → M
  h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))
  D' : LeviCivitaData h
  he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 (2 * r))
  he0 : e 0 = p
  hlocal : ∀ x ∈ Metric.ball 0 (2 * r),
    (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible
  hpullback : ∀ x ∈ Metric.ball 0 (2 * r),
    h.euclideanCoefficients x = g.pullbackCoefficients e x
  helliptic : ∀ x ∈ Metric.ball 0 (2 * r), ∀ v,
    C⁻¹ * ‖v‖ ^ 2 ≤ h.euclideanCoefficients x v v ∧
      h.euclideanCoefficients x v v ≤ C * ‖v‖ ^ 2
  hderiv : ∀ x ∈ Metric.ball 0 (2 * r),
    ‖fderiv ℝ h.euclideanCoefficients x‖ ≤ H
  hholder : ∀ x y, x ∈ Metric.ball 0 (2 * r) → y ∈ Metric.ball 0 (2 * r) →
    ‖fderiv ℝ h.euclideanCoefficients x - fderiv ℝ h.euclideanCoefficients y‖ ≤
      H * ‖x - y‖ ^ (1 / 2 : ℝ)
  hharmonic : ∀ x ∈ Metric.ball 0 (2 * r), ∀ i : Fin n,
    D'.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y i) x = 0
  hdist : ∀ x ∈ Metric.ball 0 (2 * r),
    g.edist p (e x) ≤ ENNReal.ofReal (Real.sqrt C * ‖x‖)

end PoincareConjecture.RiemannianMetric
