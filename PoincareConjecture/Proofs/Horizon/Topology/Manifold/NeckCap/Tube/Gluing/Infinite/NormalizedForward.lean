import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Forward
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.NormalizedTail










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem exists_normalized_forward_cylinder_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ a : ℤ, C.shape = .forward a →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞) (r : ℝ),
          0 < r ∧
          (∀ p : RoundCylinderSpace, |p.2| < r →
            (D p : M) = (C.neck a).coordinate_map p) ∧
          (fun p : RoundCylinderSpace => (D p : M)) '' {p | p.2 ≤ 0} =
            {x | x ∈ (C.neck a).carrier ∧ ((C.neck a).coordinate_inverse x).2 ≤ 0} := by
  obtain ⟨ε₀, hε₀, hsmall, hforward⟩ := exists_forward_cylinder_with_affine_tail_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε hsep a hshape
  obtain ⟨D, T, hretain, _, _, hfst, r₀, hr₀, haffine⟩ :=
    hforward C hε hsep a hshape
  have ha : a ∈ C.shape.active := by
    rw [hshape]
    change a ≤ a
    exact le_rfl
  have hepsilon := C.epsilon_eq a ha
  have hi : 0 < ε⁻¹ := inv_pos.mpr (hepsilon ▸ (C.neck a).epsilon_pos)
  have hcut : -(3 / 4 : ℝ) * ε⁻¹ ∈ Ioo (-(C.neck a).epsilon⁻¹) 0 := by
    rw [hepsilon]
    constructor <;> linarith
  have hNU : (C.neck a).carrier ⊆ C.unionOpen := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩
  exact (C.neck a).exists_normalized_retained_neck_tail C.unionOpen hNU
    D T (-(3 / 4 : ℝ) * ε⁻¹) hcut hretain hfst r₀ hr₀ haffine

end PoincareConjecture.BalancedNeckChain
