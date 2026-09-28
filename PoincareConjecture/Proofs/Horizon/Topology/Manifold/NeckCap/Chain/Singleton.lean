import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain







set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}


def BalancedNeckChain.singleton (N : EpsilonNeck g) : BalancedNeckChain g N.epsilon where
  shape := .finite 0 0
  neck := fun _ => N
  source_necks := {N}
  selected := by
    intro i hi
    refine ⟨N, Set.mem_singleton N, rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
    intro z hz
    simp
  active_nonempty := ⟨0, by simp [ChainShape.active]⟩
  epsilon_eq := by intros; rfl
  centers_distinct := by
    intro i hi j hj hij
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega
  adjacent_overlap := by
    intro i hi hj
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega
  overlap_contains_quarters := by
    intro i hi hj
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega
  overlap_within_three_quarters := by
    intro i hi hj
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega
  later_disjoint_negative_end := by
    intro i hi j hj hij
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega
  balanced_center_distance := by
    intro i hi hj
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega

@[simp] theorem BalancedNeckChain.singleton_union (N : EpsilonNeck g) :
    (⋃ i : {i // i ∈ (BalancedNeckChain.singleton N).shape.active},
      ((BalancedNeckChain.singleton N).neck i.1).carrier) = N.carrier := by
  have : Nonempty {i // i ∈ (BalancedNeckChain.singleton N).shape.active} :=
    ⟨⟨0, by simp [singleton, ChainShape.active]⟩⟩
  simp [singleton, ChainShape.active]

end PoincareConjecture
