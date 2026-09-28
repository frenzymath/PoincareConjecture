import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.Dirichlet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.Weights
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.Decay
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M} {Ω : Set M}

theorem setIntegral_setIntegral_heatKernelContinuousTime_ball_le
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (hc : MetricComplete g) {t : ℝ} (ht : 0 < t) (x y : M) (r : ℝ) :
    (∫ z in g.ball x r, ∫ w in g.ball y r,
      heatKernelContinuousTime D S t z w ∂g.volumeMeasure ∂g.volumeMeasure) ≤
      Real.sqrt (g.volumeMeasure.real (g.ball x r)) *
        Real.sqrt (g.volumeMeasure.real (g.ball y r)) *
          Real.exp (-(max ((g.edist x y).toReal - 2 * r) 0) ^ 2 / (16 * t)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hball (p : M) : MeasurableSet (g.ball p r) :=
    (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  apply gaussian_bound_of_smooth_weight_bounds ht
  intro a ha ε hε
  obtain ⟨ψ, hψ, hgrad, hx, hy⟩ := D.exists_smooth_weight_separating_balls
    (r := r) x y hε ha
  apply setIntegral_setIntegral_heatKernelContinuousTime_le D S
    (hball x) (hball y) (g.volumeMeasure_ball_lt_top hc x r).ne
    (g.volumeMeasure_ball_lt_top hc y r).ne ψ hψ (2 * a) (by positivity) ?_ hx hy ht
  intro z _
  exact (Real.sqrt_le_iff).mp (hgrad z) |>.2

end PoincareConjecture.LeviCivitaData.Dirichlet
