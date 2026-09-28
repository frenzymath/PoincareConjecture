import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem pullback_source_metric_eq_shifted_pointed_metric
    {n : ℕ} {T : ℝ}
    (S : PointedFlowSequence n (-T / 2) (T / 2))
    {N : ℕ → Type u} [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (N k)]
    [∀ k, IsManifold (𝓡 n) ∞ (N k)]
    (F : ∀ k, RicciFlow n (N k) (Icc (-T) 0))
    (e : ∀ k, (S.carrier k).carrier ≃ₘ⟮𝓡 n, 𝓡 n⟯ N k)
    (hmetric : ∀ (k : ℕ) (t : ℝ) (x : (S.carrier k).carrier)
      (v w : TangentSpace (𝓡 n) x),
      ((S.flow k).flow.metric t).inner x v w =
        ((F k).metric (t - T / 2)).inner (e k x)
          (mfderiv (𝓡 n) (𝓡 n) (e k) x v)
          (mfderiv (𝓡 n) (𝓡 n) (e k) x w)) :
    ∀ (k : ℕ) (t : ℝ),
      ((F k).pullbackDiffeomorph (e k)).metric t =
        (S.flow k).flow.metric (t + T / 2) := by
  intro k t
  have hext (g₁ g₂ : RiemannianMetric n (S.carrier k).carrier)
      (hinner : g₁.inner = g₂.inner) : g₁ = g₂ := by
    cases g₁
    cases g₂
    cases hinner
    rfl
  apply hext
  funext x
  ext v w
  rw [RicciFlow.pullbackDiffeomorph_inner]
  simpa only [add_sub_cancel_right] using (hmetric k (t + T / 2) x v w).symm

end PoincareConjecture.M30
