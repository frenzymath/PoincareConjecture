import PoincareConjecture.Definitions.Ch15.SurgeryEndPolicy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

def surgeryRetainedCollar
    (event : SurgeryEventData g0 K P slice metric T) (width : ℝ) :
    Set (slice event.tMinus).carrier :=
  event.regular_limit ∩ event.limit_identify.map ⁻¹'
    ⋃ i, (event.necks i).neck.region (-width) width

theorem surgeryRetainedCollar_isOpen
    (event : SurgeryEventData g0 K P slice metric T) (width : ℝ) :
    IsOpen (surgeryRetainedCollar event width) := by
  exact event.limit_identify.map_smooth.continuousOn.isOpen_inter_preimage
    event.regular_limit_open (isOpen_iUnion fun i => (event.necks i).neck.isOpen_region _ _)

theorem surgeryRetained_frontier_subset_collar
    (event : SurgeryEventData g0 K P slice metric T) {width : ℝ} (hwidth : 0 < width) :
    frontier event.retained_pre ⊆ surgeryRetainedCollar event width := by
  intro x hx
  rw [event.pre_boundary] at hx
  obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
  have hyreg : event.limit_identify.inverse y ∈ event.regular_limit := by
    exact (congrArg (fun V => event.limit_identify.inverse y ∈ V)
      event.limit_identify.inverse_image).mp
        (mem_image_of_mem event.limit_identify.inverse (mem_univ y))
  refine ⟨hyreg, ?_⟩
  change event.limit_identify.map (event.limit_identify.inverse y) ∈
    ⋃ i, (event.necks i).neck.region (-width) width
  rw [event.limit_identify.right_inverse (mem_univ y)]
  obtain ⟨hycarrier, hyzero⟩ := ((event.necks i).neck.mem_central_sphere_iff y).mp hy
  apply mem_iUnion.mpr
  refine ⟨i, hycarrier, ?_, ?_⟩ <;> rw [hyzero]
  · exact neg_neg_of_pos hwidth
  · exact hwidth

theorem surgeryRetainedCore_compact_interior
    (event : SurgeryEventData g0 K P slice metric T) {width : ℝ} (hwidth : 0 < width) :
    IsCompact (event.retained_pre \ surgeryRetainedCollar event width) ∧
      event.retained_pre \ surgeryRetainedCollar event width ⊆ interior event.retained_pre := by
  refine ⟨event.retained_pre_compact.diff (surgeryRetainedCollar_isOpen event width), ?_⟩
  intro x hx
  by_contra hnot
  have hfront : x ∈ frontier event.retained_pre := by
    rw [frontier, event.retained_pre_compact.isClosed.closure_eq]
    exact ⟨hx.1, hnot⟩
  exact hx.2 (surgeryRetained_frontier_subset_collar event hwidth hfront)

end PoincareConjecture.Proofs.M46
