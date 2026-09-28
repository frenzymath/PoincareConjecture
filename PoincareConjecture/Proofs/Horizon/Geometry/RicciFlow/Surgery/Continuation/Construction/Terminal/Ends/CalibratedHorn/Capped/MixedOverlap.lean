import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.CapFrontier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.Overlap.Quarter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.Overlap.ShiftedSlice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.SliceAlignment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.LowerCore
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.AlignedCores

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

private theorem mixed_overlap_of_shifted_slice (C D : CapCertificate g)
    (hC : C.epsilon ≤ 1 / 200) (hDC : D.epsilon = C.epsilon)
    (hmeet : (D.boundary_sphere ∩ C.carrier).Nonempty)
    (hmiss : ¬ D.boundary_sphere ⊆ C.carrier)
    {a : ℝ} (ha : a ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹)
    (hhigh : range (fun q : UnitTwoSphere => D.boundary_neck.coordinate_map (q, a)) ⊆
      C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) :
    C.carrier ⊆ D.carrier ∨
      (C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
        IsCompact (C.carrier ∪ D.carrier)) := by
  obtain ⟨e, f, heC, hfD, heB, hfB, hretain⟩ :=
    C.slice_alignment_of_epsilon_le D hC (hDC.trans_le hC) ha
      (fun q => (hhigh (mem_range_self q)).1)
  rcases C.closed_core_eq_or_compact_component_of_aligned_boundaries D e f
      heC hfD (heB.trans hfB.symm) with hequal | hclosed
  · left
    have hlower := C.lower_carrier_subset_transported_core_of_boundary_above_half
      e hretain (heB ▸ hhigh)
    obtain ⟨x, _, _, hxquarter, hxD⟩ := C.mixed_boundary_positive_end_contact D hmeet hmiss
    have hupper := C.end_neck.closure_positive_quarter_subset_of_central_sphere_contact_of_epsilon_le
      D.boundary_neck (C.end_neck_epsilon.trans_le hC)
      (D.boundary_neck_epsilon.trans (hDC.trans C.end_neck_epsilon.symm))
      ⟨x, by simpa only [C.end_neck_epsilon] using hxquarter, hxD⟩
    intro y hy
    by_cases hyupper : y ∈ C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹
    · apply D.boundary_neck_subset
      apply hupper
      simpa only [C.end_neck_epsilon] using subset_closure hyupper
    · have hycore := image_mono C.core_subset_closed_core (hlower ⟨hy, hyupper⟩)
      rw [hequal] at hycore
      rw [← hfD]
      exact image_mono D.closed_core_subset_carrier hycore
  · exact Or.inr hclosed

theorem mixed_overlap_containment_or_closing_of_epsilon_le (C D : CapCertificate g)
    (hC : C.epsilon ≤ 1 / 200) (hDC : D.epsilon = C.epsilon)
    (hmeet : (D.boundary_sphere ∩ C.carrier).Nonempty)
    (hmiss : ¬ D.boundary_sphere ⊆ C.carrier) :
    C.carrier ⊆ D.carrier ∨
      (C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
        IsCompact (C.carrier ∪ D.carrier)) := by
  obtain ⟨x, _, hxfront, hxquarter, hxD⟩ :=
    C.mixed_boundary_positive_end_contact D hmeet hmiss
  obtain ⟨a, _, ha, hhigh⟩ :=
    C.end_neck.shifted_slice_subset_positive_end_of_frontier_contact_of_epsilon_le
      D.boundary_neck (C.end_neck_epsilon.trans_le hC)
      (D.boundary_neck_epsilon.trans (hDC.trans C.end_neck_epsilon.symm))
      hxfront (by simpa only [C.end_neck_epsilon] using hxquarter) hxD
  apply C.mixed_overlap_of_shifted_slice D hC hDC hmeet hmiss ha
  simpa only [C.end_neck_epsilon] using hhigh

end PoincareConjecture.CapCertificate
