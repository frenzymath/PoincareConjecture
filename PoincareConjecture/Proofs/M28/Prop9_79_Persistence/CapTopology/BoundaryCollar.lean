import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.CoreClosure
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.InnerAttachment
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar

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

theorem core_disjoint_end (N : CapCertificate g) : Disjoint N.core N.end_neck.carrier := by
  apply disjoint_left.mpr
  intro x hxC hxE
  have hxY : x ∈ N.closed_core :=
    interior_subset (N.core_eq_interior_closed_core ▸ hxC)
  exact (N.closed_core_eq_complement_end ▸ hxY).2 hxE

omit [T2Space M] in
private theorem boundary_region_subset_core_or_end (N : CapCertificate g)
    {a b : ℝ} (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹)
    (hzero : 0 ∉ Ioo a b) :
    N.boundary_neck.region a b ⊆ N.core ∨
      N.boundary_neck.region a b ⊆ N.end_neck.carrier := by
  have hconn := N.boundary_neck.isPreconnected_region
    (by simpa only [N.boundary_neck_epsilon] using ha)
    (by simpa only [N.boundary_neck_epsilon] using hb)
  have hCoreOpen : IsOpen N.core := by
    rw [N.core_eq_interior_closed_core]
    exact isOpen_interior
  apply hconn.subset_or_subset hCoreOpen N.end_neck.carrier_open N.core_disjoint_end
  intro x hx
  have hxS : x ∉ N.boundary_sphere := by
    intro hxS
    have hz := (N.boundary_neck.mem_central_sphere_iff_of_mem_carrier hx.1).mp
      (N.boundary_eq_neck_sphere ▸ hxS)
    exact hzero (by simpa only [mem_Ioo, hz] using hx.2)
  by_cases hxY : x ∈ N.closed_core
  · left
    rw [N.core_eq_interior_closed_core]
    exact (mem_interior_iff_notMem_frontier hxY).mpr
      (fun hxf => hxS (N.core_frontier_eq_boundary ▸ hxf))
  · right
    by_contra hxE
    apply hxY
    rw [N.closed_core_eq_complement_end]
    exact ⟨N.boundary_neck_subset hx.1, hxE⟩

theorem isPreconnected_boundary_region_inter_end (N : CapCertificate g)
    {a b : ℝ} (ha : -N.epsilon⁻¹ ≤ a) (ha0 : a < 0)
    (hb0 : 0 < b) (hb : b ≤ N.epsilon⁻¹) :
    IsPreconnected (N.boundary_neck.region a b ∩ N.end_neck.carrier) := by
  have heps : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hm := boundary_region_subset_core_or_end N ha heps.le (by simp)
  have hp := boundary_region_subset_core_or_end N (le_of_lt (neg_neg_of_pos heps)) hb
    (by simp)
  have hmconn : IsPreconnected (N.boundary_neck.region a 0) :=
    N.boundary_neck.isPreconnected_region
      (by simpa only [N.boundary_neck_epsilon] using ha)
      (by simpa only [N.boundary_neck_epsilon] using heps.le)
  have hpconn : IsPreconnected (N.boundary_neck.region 0 b) :=
    N.boundary_neck.isPreconnected_region
      (by simpa only [N.boundary_neck_epsilon] using (neg_neg_of_pos heps).le)
      (by simpa only [N.boundary_neck_epsilon] using hb)
  have hparts {x : M} (hx : x ∈ N.boundary_neck.region a b) :
      x ∈ N.boundary_neck.region a 0 ∨ x ∈ N.boundary_sphere ∨
        x ∈ N.boundary_neck.region 0 b := by
    rw [N.boundary_neck.region_split_zero ha0 hb0] at hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl (N.boundary_eq_neck_sphere.symm ▸ hx))
    · exact Or.inr (Or.inr hx)
  have hmB : N.boundary_neck.region a 0 ⊆ N.boundary_neck.region a b := by
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans hb0⟩
  have hpB : N.boundary_neck.region 0 b ⊆ N.boundary_neck.region a b := by
    intro x hx
    exact ⟨hx.1, ha0.trans hx.2.1, hx.2.2⟩
  rcases hm with hm | hm <;> rcases hp with hp | hp
  · have hEmpty : N.boundary_neck.region a b ∩ N.end_neck.carrier = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxB, hxE⟩
      rcases hparts hxB with hxm | hxS | hxp
      · exact disjoint_left.mp N.core_disjoint_end (hm hxm) hxE
      · exact disjoint_left.mp N.boundary_disjoint_end hxS hxE
      · exact disjoint_left.mp N.core_disjoint_end (hp hxp) hxE
    rw [hEmpty]
    exact isPreconnected_empty
  · have hEq : N.boundary_neck.region a b ∩ N.end_neck.carrier =
        N.boundary_neck.region 0 b := by
      ext x
      constructor
      · rintro ⟨hxB, hxE⟩
        rcases hparts hxB with hxm | hxS | hxp
        · exact False.elim (disjoint_left.mp N.core_disjoint_end (hm hxm) hxE)
        · exact False.elim (disjoint_left.mp N.boundary_disjoint_end hxS hxE)
        · exact hxp
      · intro hx
        exact ⟨hpB hx, hp hx⟩
    rw [hEq]
    exact hpconn
  · have hEq : N.boundary_neck.region a b ∩ N.end_neck.carrier =
        N.boundary_neck.region a 0 := by
      ext x
      constructor
      · rintro ⟨hxB, hxE⟩
        rcases hparts hxB with hxm | hxS | hxp
        · exact hxm
        · exact False.elim (disjoint_left.mp N.boundary_disjoint_end hxS hxE)
        · exact False.elim (disjoint_left.mp N.core_disjoint_end (hp hxp) hxE)
      · intro hx
        exact ⟨hmB hx, hm hx⟩
    rw [hEq]
    exact hmconn
  · have hzS : N.boundary_neck.center ∈ N.boundary_sphere :=
      N.boundary_eq_neck_sphere.symm ▸ N.boundary_neck.center_on_central_sphere
    have hzB := N.boundary_neck.central_sphere_subset_region ha0 hb0
      N.boundary_neck.center_on_central_sphere
    have hzcl : N.boundary_neck.center ∈ closure N.core :=
      N.closed_core_eq_closure_core ▸ N.boundary_subset_closed_core_m28 hzS
    obtain ⟨x, hxB, hxC⟩ := mem_closure_iff.mp hzcl
      (N.boundary_neck.region a b) (N.boundary_neck.region_open a b) hzB
    rcases hparts hxB with hxm | hxS | hxp
    · exact False.elim (disjoint_left.mp N.core_disjoint_end hxC (hm hxm))
    · have hxf : x ∈ frontier N.closed_core := N.core_frontier_eq_boundary.symm ▸ hxS
      exact False.elim (hxf.2 (N.core_eq_interior_closed_core ▸ hxC))
    · exact False.elim (disjoint_left.mp N.core_disjoint_end hxC (hp hxp))

end PoincareConjecture.CapCertificate
