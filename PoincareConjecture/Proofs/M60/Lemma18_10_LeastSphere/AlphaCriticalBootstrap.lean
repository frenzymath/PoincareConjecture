import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakAverages

















set_option autoImplicit false

open Set MeasureTheory ContinuousLinearMap
open scoped ContDiff Manifold Topology Convolution ENNReal

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





structure SUC1HolderGain {m : ℕ}
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (center : LoopPlane) (outerRadius : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < outerRadius
  coordinate_contDiff : ContDiffOn ℝ 1 u (Metric.ball center radius)
  column_ae : ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict (Metric.ball center radius),
    fderiv ℝ u z (EuclideanSpace.single i 1) = V i z
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  derivative_holder : ∀ x ∈ Metric.closedBall center (radius / 2),
    ∀ y ∈ Metric.closedBall center (radius / 2),
    dist (fderiv ℝ u x) (fderiv ℝ u y) ≤
      constant * Real.sqrt (Real.sqrt (dist x y))





theorem SUWeakAlphaCoordinate.kernel_derivative
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {center : LoopPlane} {radius : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center radius) (ha : 1 ≤ alpha)
    {φ : LoopPlane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : LoopPlane) (hs : tsupport (fun y => φ (x - y)) ⊆ Metric.ball center radius)
    (i : Fin 2) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (Metric.ball center radius).indicator u) x
        (EuclideanSpace.single i 1) =
      (φ ⋆[lsmul ℝ ℝ, volume] (Metric.ball center radius).indicator (V i)) x := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball center radius)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball center radius) < ⊤)⟩
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * alpha) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hu : Integrable ((Metric.ball center radius).indicator u) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      (S.coordinate_memLp.integrable hq)
  have hV : Integrable ((Metric.ball center radius).indicator (V i)) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      ((S.column_memLp i).integrable hq)
  exact suWeak_convolution_fderiv Metric.isOpen_ball.measurableSet
    (S.weak_derivative i) hu.locallyIntegrable hV.locallyIntegrable hφ hc x hs

end PoincareConjecture.M60

end
