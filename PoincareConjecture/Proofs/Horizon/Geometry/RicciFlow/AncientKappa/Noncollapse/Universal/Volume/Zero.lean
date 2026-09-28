import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.BoundedAncient











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem M22UniversalNoncollapsingPredecessors.asymptotic_volume_ratio_zero
    {n : ℕ} (P : M22UniversalNoncollapsingPredecessors.{u} n)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) : AncientAsymptoticVolumeRatioZero K := by
  let hC : RicciFlowCurvatureCalculus.{u} := {
    tensor_calculus := P.tensor_calculus
    curvature_norm_zero := P.curvature_norm_zero
    scalar_regular := P.scalar_regular
    scalar_evolution := P.scalar_evolution
    curvature_evolution := P.curvature_evolution
    ricci_evolution := P.ricci_evolution
    local_derivative_estimates := P.local_derivative_estimates }
  apply K.asymptotic_volume_ratio_zero_of_curvature_and_differential hC
  exact P.ancient_differential n M K.flow K.complete K.nonnegative_curvature_operator
    (fun t ht => K.operator_bound_of_tensor_calculus t ht
      (P.tensor_calculus n M (K.flow.metric t) (K.flow.connection t))) K.nonflat

end PoincareConjecture
