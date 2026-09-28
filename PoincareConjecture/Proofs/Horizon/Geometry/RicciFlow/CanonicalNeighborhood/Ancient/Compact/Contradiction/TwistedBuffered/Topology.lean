import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Topology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution 3 M}

theorem buffered_endNeck_subset_carrier (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    C.cover '' (univ ×ˢ Ioo (2 * L) (4 * L)) ⊆ interior (C.slabCore (4 * L)) := by
  intro x hx
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_interior_slabCore_iff]
  exact ((C.cover_mem_positiveSlab_iff (by positivity) p).mp hx).2

theorem buffered_boundaryNeck_subset_carrier (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    C.cover '' (univ ×ˢ Ioo L (3 * L)) ⊆ interior (C.slabCore (4 * L)) := by
  intro x hx
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_interior_slabCore_iff]
  have hp := ((C.cover_mem_positiveSlab_iff hL.le p).mp hx).2
  linarith

theorem buffered_core_eq_carrier_diff_endNeck (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    C.slabCore (2 * L) = interior (C.slabCore (4 * L)) \
      C.cover '' (univ ×ˢ Ioo (2 * L) (4 * L)) := by
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [mem_sdiff, C.cover_mem_slabCore_iff, C.cover_mem_interior_slabCore_iff,
    C.cover_mem_positiveSlab_iff (by positivity)]
  constructor
  · intro hp
    exact ⟨by linarith, fun h => (not_lt_of_ge hp) h.1⟩
  · rintro ⟨hp, hnot⟩
    by_contra h
    exact hnot ⟨lt_of_not_ge h, hp⟩

theorem buffered_carrier_inter_frontier_endNeck (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    interior (C.slabCore (4 * L)) ∩ frontier (C.cover '' (univ ×ˢ Ioo (2 * L) (4 * L))) =
      frontier (C.slabCore (2 * L)) := by
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [mem_inter_iff, C.cover_mem_interior_slabCore_iff,
    C.cover_mem_frontier_positiveSlab_iff (by positivity) (by linarith),
    C.cover_mem_frontier_slabCore_iff]
  constructor
  · rintro ⟨hp, h | h⟩
    · exact h
    · linarith
  · intro hp
    exact ⟨by linarith, Or.inl hp⟩

theorem buffered_frontier_subset_negativeEnd_closure
    (C : M27TwistedSphereLineFlowCertificate K) {L : ℝ} (hL : 0 < L) :
    frontier (C.slabCore (2 * L)) ⊆
      closure (C.cover '' (univ ×ˢ Ioo (2 * L) (5 * L / 2))) := by
  rw [C.frontier_slabCore (by positivity), C.closure_cover_image_Ioo (by linarith)]
  apply image_mono
  rintro p ⟨hp, hline⟩
  refine ⟨hp, ?_⟩
  rw [mem_singleton_iff] at hline
  rw [mem_Icc, hline]
  constructor <;> linarith

theorem isCompact_closure_interior_slabCore
    (C : M27TwistedSphereLineFlowCertificate K) (r : ℝ) :
    IsCompact (closure (interior (C.slabCore r))) :=
  (C.isCompact_slabCore r).of_isClosed_subset isClosed_closure
    (closure_minimal interior_subset (C.isCompact_slabCore r).isClosed)

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
