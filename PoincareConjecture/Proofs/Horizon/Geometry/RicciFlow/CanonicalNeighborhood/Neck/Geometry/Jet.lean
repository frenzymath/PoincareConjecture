import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.TensorNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators
universe u
namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

namespace EpsilonNeck

variable {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

noncomputable def normalized_pullback : RoundCylinderTwoTensor :=
  fun z v w ↦ N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w

theorem normalized_pullback_close :
    RoundCylinderClose N.epsilon 0 N.normalized_pullback := by
  change RoundCylinderClose N.epsilon 0
    (fun z v w ↦ N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
  exact N.metric_comparison.close

theorem normalized_pullback_zeroth_normSquared_lt
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        N.normalized_pullback 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) < N.epsilon ^ 2 := by
  rcases normalized_pullback_close N with ⟨_, ⟨bound, hbound, hjet⟩⟩
  have hterm :
      roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          N.normalized_pullback 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) ≤
        roundCylinderJetErrorSquared 0 N.normalized_pullback ⌊N.epsilon⁻¹⌋₊ z := by
    dsimp only [roundCylinderJetErrorSquared]
    apply Finset.single_le_sum (f := fun k =>
      roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          N.normalized_pullback k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)))
    · intro k hk
      exact roundCylinderTensorNormSquared_nonneg z.1
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          N.normalized_pullback k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2))
    · simp
  have hjet' := hjet z hz
  dsimp [roundCylinderJetErrorSquared] at hterm hjet'
  exact lt_of_le_of_lt hterm (lt_of_le_of_lt hjet' hbound)

end EpsilonNeck

end PoincareConjecture
