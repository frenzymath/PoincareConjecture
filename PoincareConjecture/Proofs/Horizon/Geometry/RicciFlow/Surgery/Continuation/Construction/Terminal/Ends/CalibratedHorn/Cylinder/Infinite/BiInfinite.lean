import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Infinite.NormalizedForward
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Infinite.NormalizedBackward
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.NormalizedForward
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.NormalizedBackward
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.TwoSidedCylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Restriction










set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem biInfinite_cylinder_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ 1 / 200 → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        C.shape = .biInfinite → ∀ a : ℤ,
        ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞,
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            (C.neck a).central_sphere := by
  intro M _ _ _ _ _ _ _ g ε C hε hsep hbi a
  have hactive (i : ℤ) : i ∈ C.shape.active := by rw [hbi]; trivial
  obtain ⟨F, rF, hrF, hFlocal, hFhalf⟩ := normalized_forward_cylinder_of_epsilon_le (C.forwardHalf hbi a)
    hε (fun i _ => hsep i (hactive i)) a rfl
  obtain ⟨B, rB, hrB, hBlocal, hBhalf⟩ := normalized_backward_cylinder_of_epsilon_le (C.backwardHalf hbi a)
    hε a rfl
  obtain ⟨D, _, hDzero⟩ := CylinderGluing.exists_two_sided_cylinder
    (C.neck a) (hsep a (hactive a))
    (C.forwardHalf hbi a).unionOpen (C.backwardHalf hbi a).unionOpen
    (C.neck_subset_forwardHalf_union hbi a) (C.neck_subset_backwardHalf_union hbi a)
    F B hFhalf hBhalf rF rB hrF hrB hFlocal hBlocal
  have hunion : (C.forwardHalf hbi a).unionOpen ⊔ (C.backwardHalf hbi a).unionOpen =
      C.unionOpen := by
    apply SetLike.coe_injective
    exact C.union_forwardHalf_backwardHalf hbi a
  have hout : ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace
      ↥((C.forwardHalf hbi a).unionOpen ⊔ (C.backwardHalf hbi a).unionOpen) ∞,
      range (fun q : UnitTwoSphere => (D (q, 0) : M)) = (C.neck a).central_sphere :=
    ⟨D, hDzero⟩
  exact hunion ▸ hout

end PoincareConjecture.BalancedNeckChain
