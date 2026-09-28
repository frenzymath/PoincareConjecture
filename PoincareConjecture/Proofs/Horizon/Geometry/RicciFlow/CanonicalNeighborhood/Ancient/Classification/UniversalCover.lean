import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Covering.Completeness.UniversalCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

open Poincare.Topology

theorem exists_simplyConnected_covering_solution
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) :
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N)
      (_ : IsManifold (𝓡 3) ∞ N) (_ : SecondCountableTopology N)
      (_ : SimplyConnectedSpace N) (L : AncientKappaSolution 3 N) (p : N → M),
      L.kappa = K.kappa ∧ Function.Surjective p ∧ IsCoveringMap p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p ∧
      ∀ t : ℝ, ∀ (x : N) (v w : TangentSpace (𝓡 3) x),
        (L.flow.metric t).inner x v w = (K.flow.metric t).inner (p x)
          (mfderiv (𝓡 3) (𝓡 3) p x v) (mfderiv (𝓡 3) (𝓡 3) p x w) := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let : SemilocallySimplyConnectedSpace M :=
    semilocallySimplyConnectedSpace_of_chartedSpace 3 M
  let x₀ : M := Classical.choice inferInstance
  let N := UniversalCover x₀
  let := UniversalCover.chartedSpace x₀
  let := UniversalCover.isManifold x₀
  let := UniversalCover.t3Space x₀
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let p : N → M := UniversalCover.proj
  have hp := UniversalCover.isLocalDiffeomorph x₀
  let : SecondCountableTopology N :=
    ((K.flow.metric 0).pullbackOfLocalDiffeomorph p hp).secondCountableTopology
  obtain ⟨L, hκ, hmetric⟩ := K.exists_lift_of_covering p hp
    (UniversalCover.isCoveringMap x₀) (UniversalCover.surjective_proj x₀)
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    L, p, hκ, UniversalCover.surjective_proj x₀, UniversalCover.isCoveringMap x₀,
    hp, hmetric⟩

end PoincareConjecture.AncientKappaSolution
