import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Singleton
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere










noncomputable section

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)


def tubeCertificate (hε : N.epsilon ≤ 1 / 200) : EpsilonTubeCertificate g N.carrier where
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_le_threshold := hε
  carrier := N.carrier
  carrier_open := N.carrier_open
  contains_X := Set.Subset.rfl
  chain := BalancedNeckChain.singleton N
  carrier_eq_chain_union := (BalancedNeckChain.singleton_union N).symm
  cylinder := N.openCylinderModel
  central_sphere_isotopy := by
    intro i hi
    simpa only [BalancedNeckChain.singleton, N.openCylinderModel_middleSphere] using
      N.central_sphere_isotopic_self

end PoincareConjecture.EpsilonNeck
