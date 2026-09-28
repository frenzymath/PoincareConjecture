import PoincareConjecture.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

structure SmoothingBridgeInput where
  connected : IsConnected (Set.univ : Set M)
  nonempty : (Set.univ : Set M).Nonempty

structure SmoothingBridgeConclusion (P : SmoothingBridgeInput (M := M)) where
  model : Type u
  model_topology : TopologicalSpace model
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model
  model_manifold : IsManifold (𝓡 3) ∞ model
  model_t2 : T2Space model
  model_second_countable : SecondCountableTopology model
  model_compact : CompactSpace model
  model_connected : IsConnected (Set.univ : Set model)
  model_homeomorph : @Homeomorph M model inferInstance model_topology

end PoincareConjecture
