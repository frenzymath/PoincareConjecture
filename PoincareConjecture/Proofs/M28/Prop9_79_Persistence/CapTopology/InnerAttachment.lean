import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem boundary_disjoint_end (N : CapCertificate g) :
    Disjoint N.boundary_sphere N.end_neck.carrier := by
  apply disjoint_left.mpr
  intro x hxS hxE
  have hxf : x ∈ frontier N.end_neck.carrier :=
    (N.boundary_eq_end_frontier ▸ hxS).2
  exact hxf.2 (N.end_neck.carrier_open.interior_eq.symm ▸ hxE)

omit [T2Space M] in

theorem boundary_subset_closed_core_m28 (N : CapCertificate g) :
    N.boundary_sphere ⊆ N.closed_core := by
  intro x hx
  rw [N.closed_core_eq_complement_end]
  exact ⟨N.boundary_subset hx, fun he => disjoint_left.mp N.boundary_disjoint_end hx he⟩

theorem boundary_subset_closure_inner_end (N : CapCertificate g) {c : ℝ}
    (hc : -N.epsilon⁻¹ < c) :
    N.boundary_sphere ⊆ closure (N.end_neck.region (-N.epsilon⁻¹) c) := by
  have heps : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hdhi : -N.epsilon⁻¹ / 2 < N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon]
    linarith
  by_cases hdc : -N.epsilon⁻¹ / 2 ≤ c
  · apply N.boundary_subset_negative_end_closure.trans (closure_mono ?_)
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans_le hdc⟩
  · let T : Set M := N.end_neck.coordinate_map ''
      (univ ×ˢ Icc c (-N.epsilon⁻¹ / 2))
    have hTcompact : IsCompact T :=
      N.end_neck.isCompact_coordinate_slab_intrinsic
        (by simpa only [N.end_neck_epsilon] using hc) hdhi
    have hTend : T ⊆ N.end_neck.carrier :=
      N.end_neck.coordinate_slab_subset_carrier_m28
        (by simpa only [N.end_neck_epsilon] using hc) hdhi
    have hsplit : N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
        N.end_neck.region (-N.epsilon⁻¹) c ∪ T := by
      intro x hx
      by_cases hxc : (N.end_neck.coordinate_inverse x).2 < c
      · exact Or.inl ⟨hx.1, hx.2.1, hxc⟩
      · exact Or.inr ⟨N.end_neck.coordinate_inverse x,
          ⟨mem_univ _, le_of_not_gt hxc, hx.2.2.le⟩,
          N.end_neck.coordinate_map_coordinate_inverse hx.1⟩
    intro x hxS
    have hx := closure_mono hsplit (N.boundary_subset_negative_end_closure hxS)
    rw [closure_union, hTcompact.isClosed.closure_eq] at hx
    rcases hx with hx | hx
    · exact hx
    · exact False.elim (disjoint_left.mp N.boundary_disjoint_end hxS (hTend hx))

end PoincareConjecture.CapCertificate
