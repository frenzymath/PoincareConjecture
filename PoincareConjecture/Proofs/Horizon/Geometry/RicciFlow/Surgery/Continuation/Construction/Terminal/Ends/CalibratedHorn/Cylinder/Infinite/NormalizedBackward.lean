import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Infinite.Backward
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Backward
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.NormalizedTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem normalized_backward_cylinder_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ 1 / 200 → ∀ b : ℤ, C.shape = .backward b →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞) (r : ℝ),
          0 < r ∧
          (∀ p : RoundCylinderSpace, |p.2| < r →
            (D p : M) = (C.neck b).coordinate_map (p.1, -p.2)) ∧
          (fun p : RoundCylinderSpace => (D p : M)) '' {p | p.2 ≤ 0} =
            {x | x ∈ (C.neck b).carrier ∧ 0 ≤ ((C.neck b).coordinate_inverse x).2} := by
  intro M _ _ _ _ _ _ _ g ε C hε b hshape
  obtain ⟨D, T, hretain, _, _, hfst, r₀, hr₀, haffine⟩ := backward_cylinder_with_affine_tail_of_epsilon_le C hε b hshape
  have hb : b ∈ C.shape.active := by
    rw [hshape]
    change b ≤ b
    exact le_rfl
  have hepsilon := C.epsilon_eq b hb
  have hi : 0 < ε⁻¹ := inv_pos.mpr (hepsilon ▸ (C.neck b).epsilon_pos)
  have hcut : -(3 / 4 : ℝ) * ε⁻¹ ∈ Ioo (-(C.neck b).reversed.epsilon⁻¹) 0 := by
    rw [EpsilonNeck.reversed_epsilon, hepsilon]
    constructor <;> linarith
  have hNU : (C.neck b).reversed.carrier ⊆ C.unionOpen := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩
  have hfst' (p : RoundCylinderSpace) :
      ((C.neck b).reversed.coordinate_inverse (T p)).1 = p.1 := hfst p
  have haffine' (p : RoundCylinderSpace) (hp : |p.2| < r₀) :
      (C.neck b).reversed.coordinate_inverse (T p) =
        (p.1, -(3 / 4 : ℝ) * ε⁻¹ + p.2) := by
    rw [EpsilonNeck.reversed_coordinate_inverse, haffine p hp]
    apply Prod.ext
    · rfl
    · dsimp only
      ring
  obtain ⟨D', r, hr, hlocal, hhalf⟩ := (C.neck b).reversed.exists_normalized_retained_neck_tail
    C.unionOpen hNU D T (-(3 / 4 : ℝ) * ε⁻¹) hcut hretain hfst' r₀ hr₀ haffine'
  refine ⟨D', r, hr, ?_, ?_⟩
  · intro p hp
    simpa only [EpsilonNeck.reversed_coordinate_map] using hlocal p hp
  · simpa only [EpsilonNeck.reversed_carrier, EpsilonNeck.reversed_coordinate_inverse,
      neg_nonpos] using hhalf

end PoincareConjecture.BalancedNeckChain
