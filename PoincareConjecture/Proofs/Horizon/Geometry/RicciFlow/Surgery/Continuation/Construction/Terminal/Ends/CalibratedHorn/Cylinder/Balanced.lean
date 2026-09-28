import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Finite.Balanced
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Infinite.BiInfinite
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Certificate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.BiInfinite

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem cylinder_with_middle_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ 1 / 200 → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞,
        ∃ j ∈ C.shape.active, ∃ c ∈ Ioo (-ε⁻¹) ε⁻¹,
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => (C.neck j).coordinate_map (q, c)) := by
  intro M _ _ _ _ _ _ _ g ε C hε hsep
  have hεpos : 0 < ε := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact C.epsilon_eq i hi ▸ (C.neck i).epsilon_pos
  have hzero : (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr hεpos), inv_pos.mpr hεpos⟩
  cases hshape : C.shape with
  | finite a b => simpa only [hshape] using finite_cylinder_with_middle_of_epsilon_le C hε a b hshape
  | forward a =>
    obtain ⟨D, r, hr, hlocal, _⟩ := normalized_forward_cylinder_of_epsilon_le C hε hsep a hshape
    refine ⟨D, a, by change a ≤ a; exact le_rfl, 0, hzero, ?_⟩
    congr 1
    funext q
    exact hlocal (q, 0) (by simpa only [abs_zero] using hr)
  | backward b =>
    obtain ⟨D, r, hr, hlocal, _⟩ := normalized_backward_cylinder_of_epsilon_le C hε b hshape
    refine ⟨D, b, by change b ≤ b; exact le_rfl, 0, hzero, ?_⟩
    congr 1
    funext q
    simpa only [neg_zero] using hlocal (q, 0) (by simpa only [abs_zero] using hr)
  | biInfinite =>
    obtain ⟨D, hDzero⟩ := biInfinite_cylinder_of_epsilon_le C hε hsep hshape 0
    exact ⟨D, 0, by trivial, 0, hzero,
      hDzero.trans (C.neck 0).centralSphere_range.symm⟩

end PoincareConjecture.BalancedNeckChain
