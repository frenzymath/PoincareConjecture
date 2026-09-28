import PoincareConjecture.Proofs.M25.AppA_1_Necks.CentralSphere
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SingleNeckCylinder

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem sameUpToReversal_refl : N.SameUpToReversal N := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
  intro z hz
  simp only [one_mul]

private theorem no_adjacent_singleton {i : ℤ}
    (hi : i ∈ (ChainShape.finite 0 0).active)
    (hj : i + 1 ∈ (ChainShape.finite 0 0).active) : False := by
  simp only [ChainShape.active, Set.mem_Icc] at hi hj
  omega

def singletonChain : BalancedNeckChain g N.epsilon where
  shape := .finite 0 0
  neck := fun _ => N
  source_necks := {N}
  selected := fun _ _ => ⟨N, rfl, N.sameUpToReversal_refl⟩
  active_nonempty := ⟨0, le_rfl, le_rfl⟩
  epsilon_eq := fun _ _ => rfl
  centers_distinct := by
    intro i hi j hj hij
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega
  adjacent_overlap := fun _ hi hj => (no_adjacent_singleton hi hj).elim
  overlap_contains_quarters := fun _ hi hj => (no_adjacent_singleton hi hj).elim
  overlap_within_three_quarters := fun _ hi hj => (no_adjacent_singleton hi hj).elim
  later_disjoint_negative_end := by
    intro i hi j hj hij
    simp only [ChainShape.active, Set.mem_Icc] at hi hj
    omega
  balanced_center_distance := fun _ hi hj => (no_adjacent_singleton hi hj).elim

noncomputable def singletonTube {X : Set M} (hε : N.epsilon ≤ 1 / 200)
    (hX : X ⊆ N.carrier) : EpsilonTubeCertificate g X where
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_le_threshold := hε
  carrier := N.carrier
  carrier_open := N.carrier_open
  contains_X := hX
  chain := N.singletonChain
  carrier_eq_chain_union := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨0, le_rfl, le_rfl⟩, hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi
  cylinder := N.m25_openCylinderModel
  central_sphere_isotopy := by
    intro i hi
    change SmoothSphereIsotopicIn N.carrier N.central_sphere N.m25_openCylinderModel.middleSphere
    rw [N.m25_openCylinderModel_middleSphere]
    exact N.m25_central_sphere_isotopic_self

end PoincareConjecture.EpsilonNeck
