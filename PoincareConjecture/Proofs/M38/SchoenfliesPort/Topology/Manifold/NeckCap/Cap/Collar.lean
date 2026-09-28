import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions

open _root_.AddCircle
open _root_.PoincareConjecture

namespace M38Schoenflies

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

namespace CapCertificate

variable (C : CapCertificate g)

private theorem boundary_region_side {a b : ℝ}
    (ha : -C.boundary_neck.epsilon⁻¹ ≤ a)
    (hb : b ≤ C.boundary_neck.epsilon⁻¹) (hab : a < b)
    (hzero : b ≤ 0 ∨ 0 ≤ a) :
    C.boundary_neck.region a b ⊆ C.core ∨
      C.boundary_neck.region a b ⊆ C.end_neck.carrier := by
  have hd : Disjoint (C.boundary_neck.region a b) C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere]
    exact (C.boundary_neck.central_sphere_disjoint_region a b hzero).symm
  rcases (CapCertificate.subset_core_or_compl_closed_core C)
    (C.boundary_neck.isConnected_region ha hb hab).2 hd with h | h
  · exact Or.inl h
  · right
    intro x hx
    by_contra hn
    apply h hx
    rw [C.closed_core_eq_complement_end]
    exact ⟨C.boundary_neck_subset hx.1, hn⟩

theorem boundary_neck_sides :
    (C.boundary_neck.region (-C.boundary_neck.epsilon⁻¹) 0 ⊆ C.core ∧
      C.boundary_neck.region 0 C.boundary_neck.epsilon⁻¹ ⊆ C.end_neck.carrier) ∨
    (C.boundary_neck.region 0 C.boundary_neck.epsilon⁻¹ ⊆ C.core ∧
      C.boundary_neck.region (-C.boundary_neck.epsilon⁻¹) 0 ⊆ C.end_neck.carrier) := by
  have he : 0 < C.boundary_neck.epsilon⁻¹ := inv_pos.mpr C.boundary_neck.epsilon_pos
  have hn := boundary_region_side C le_rfl he.le (neg_lt_zero.mpr he) (Or.inl le_rfl)
  have hp := boundary_region_side C (neg_nonpos.mpr he.le) le_rfl he (Or.inr le_rfl)
  rcases hn with hn | hn <;> rcases hp with hp | hp
  · obtain ⟨x, hx, hxend⟩ := (CapCertificate.boundary_neck_inter_end_nonempty C)
    exfalso
    have hnot : x ∉ C.closed_core :=
      fun hxc => Set.disjoint_left.mp (CapCertificate.disjoint_closed_core_end C) hxc hxend
    rcases C.boundary_neck.carrier_subset_region_union_central_union_region hx with
      (hneg | hsphere) | hpos
    · exact hnot ((CapCertificate.core_subset_closed_core C) (hn hneg))
    · exact hnot (C.boundary_subset_closed_core (C.boundary_eq_neck_sphere.symm ▸ hsphere))
    · exact hnot ((CapCertificate.core_subset_closed_core C) (hp hpos))
  · exact Or.inl ⟨hn, hp⟩
  · exact Or.inr ⟨hp, hn⟩
  · obtain ⟨x, hx, hxcore⟩ := (CapCertificate.boundary_neck_inter_core_nonempty C)
    exfalso
    have hnot : x ∉ C.end_neck.carrier :=
      Set.disjoint_left.mp (CapCertificate.disjoint_closed_core_end C)
        (CapCertificate.core_subset_closed_core C hxcore)
    rcases C.boundary_neck.carrier_subset_region_union_central_union_region hx with
      (hneg | hsphere) | hpos
    · exact hnot (hn hneg)
    · exact Set.disjoint_left.mp (CapCertificate.disjoint_core_boundary C) hxcore
        (C.boundary_eq_neck_sphere.symm ▸ hsphere)
    · exact hnot (hp hpos)

end CapCertificate

end PoincareConjecture

end M38Schoenflies
