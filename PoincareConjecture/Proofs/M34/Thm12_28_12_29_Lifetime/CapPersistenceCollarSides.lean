import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRegularCore
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem subset_core_or_end_of_preconnected {S : Set M}
    (hS : IsPreconnected S) (hSV : S ⊆ N.carrier)
    (hboundary : Disjoint S N.boundary_sphere) :
    S ⊆ N.core ∨ S ⊆ N.end_neck.carrier := by
  have hcore : IsOpen N.core := by rw [N.core_eq_interior_closed_core]; exact isOpen_interior
  apply hS.subset_or_subset hcore N.end_neck.carrier_open N.core_disjoint_end_neck
  intro x hx
  by_cases hxy : x ∈ N.closed_core
  · apply Or.inl
    rw [N.core_eq_interior_closed_core]
    by_contra hnot
    have hfront : x ∈ frontier N.closed_core := ⟨subset_closure hxy, hnot⟩
    exact Set.disjoint_left.mp hboundary hx (N.core_frontier_eq_boundary ▸ hfront)
  · apply Or.inr
    by_contra hnot
    apply hxy
    rw [N.closed_core_eq_complement_end]
    exact ⟨hSV hx, hnot⟩

theorem boundary_neck_region_subset_core_or_end {a b : ℝ}
    (ha : -N.boundary_neck.epsilon⁻¹ ≤ a) (hb : b ≤ N.boundary_neck.epsilon⁻¹)
    (hsign : b ≤ 0 ∨ 0 ≤ a) :
    N.boundary_neck.region a b ⊆ N.core ∨
      N.boundary_neck.region a b ⊆ N.end_neck.carrier := by
  apply N.subset_core_or_end_of_preconnected
    (N.boundary_neck.region_isPreconnected ha hb)
    (fun _ hx => N.boundary_neck_subset hx.1)
  apply Set.disjoint_left.mpr
  intro x hx hxB
  have hx0 := (N.boundary_neck.mem_central_sphere_iff_of_mem hx.1).mp
    (N.boundary_eq_neck_sphere ▸ hxB)
  rcases hsign with hs | hs
  · have ht := hx.2.2
    rw [hx0] at ht
    exact (not_lt_of_ge hs) ht
  · have ht := hx.2.1
    rw [hx0] at ht
    exact (not_lt_of_ge hs) ht

theorem boundary_neck_opposite_sides {r : ℝ} (hr : 0 < r)
    (hrN : r ≤ N.boundary_neck.epsilon⁻¹) :
    (N.boundary_neck.region (-r) 0 ⊆ N.core ∧
      N.boundary_neck.region 0 r ⊆ N.end_neck.carrier) ∨
    (N.boundary_neck.region 0 r ⊆ N.core ∧
      N.boundary_neck.region (-r) 0 ⊆ N.end_neck.carrier) := by
  have he : 0 < N.boundary_neck.epsilon⁻¹ := inv_pos.mpr N.boundary_neck.epsilon_pos
  have hA := N.boundary_neck_region_subset_core_or_end (neg_le_neg hrN) he.le
    (Or.inl le_rfl)
  have hB := N.boundary_neck_region_subset_core_or_end (neg_nonpos.mpr he.le) hrN
    (Or.inr le_rfl)
  have hcB : N.boundary_neck.center ∈ N.boundary_sphere :=
    N.boundary_eq_neck_sphere.symm ▸ N.boundary_neck.center_on_central_sphere
  have hcN := N.boundary_neck.central_sphere_subset N.boundary_neck.center_on_central_sphere
  have hc0 := (N.boundary_neck.mem_central_sphere_iff_of_mem hcN).mp
    N.boundary_neck.center_on_central_sphere
  have hc : N.boundary_neck.center ∈ N.boundary_neck.region (-r) r := by
    exact ⟨hcN, by rw [hc0]; exact neg_neg_of_pos hr, by rw [hc0]; exact hr⟩
  have hhalves {x : M} (hx : x ∈ N.boundary_neck.region (-r) r)
      (hxB : x ∉ N.boundary_sphere) :
      x ∈ N.boundary_neck.region (-r) 0 ∪ N.boundary_neck.region 0 r := by
    have hn : (N.boundary_neck.coordinate_inverse x).2 ≠ 0 := by
      intro hzero
      apply hxB
      rw [N.boundary_eq_neck_sphere]
      exact (N.boundary_neck.mem_central_sphere_iff_of_mem hx.1).mpr hzero
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Or.inl ⟨hx.1, hx.2.1, hneg⟩
    · exact Or.inr ⟨hx.1, hpos, hx.2.2⟩
  have hcore : ∃ x ∈ N.boundary_neck.region (-r) 0 ∪ N.boundary_neck.region 0 r,
      x ∈ N.core := by
    obtain ⟨x, hx, hxc⟩ := mem_closure_iff.mp (N.boundary_subset_closure_core hcB)
      _ (N.boundary_neck.region_isOpen (-r) r) hc
    refine ⟨x, hhalves hx ?_, hxc⟩
    intro hxB
    have hxfront : x ∈ frontier N.closed_core := N.core_frontier_eq_boundary.symm ▸ hxB
    exact hxfront.2 (N.core_eq_interior_closed_core ▸ hxc)
  have hend : ∃ x ∈ N.boundary_neck.region (-r) 0 ∪ N.boundary_neck.region 0 r,
      x ∈ N.end_neck.carrier := by
    have hcfront : N.boundary_neck.center ∈ frontier N.end_neck.carrier :=
      (N.boundary_eq_end_frontier ▸ hcB).2
    obtain ⟨x, hx, hxe⟩ := mem_closure_iff.mp (frontier_subset_closure hcfront)
      _ (N.boundary_neck.region_isOpen (-r) r) hc
    refine ⟨x, hhalves hx ?_, hxe⟩
    intro hxB
    have hy := N.boundary_subset_closed_core hxB
    rw [N.closed_core_eq_complement_end] at hy
    exact hy.2 hxe
  rcases hA with hAc | hAe
  · rcases hB with hBc | hBe
    · obtain ⟨x, hx, hxe⟩ := hend
      exact False.elim (Set.disjoint_left.mp N.core_disjoint_end_neck
        (hx.elim (fun h => hAc h) (fun h => hBc h)) hxe)
    · exact Or.inl ⟨hAc, hBe⟩
  · rcases hB with hBc | hBe
    · exact Or.inr ⟨hBc, hAe⟩
    · obtain ⟨x, hx, hxc⟩ := hcore
      exact False.elim (Set.disjoint_left.mp N.core_disjoint_end_neck hxc
        (hx.elim (fun h => hAe h) (fun h => hBe h)))

end PoincareConjecture.CapCertificate
