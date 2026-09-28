import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.CompactCapture

open _root_.AddCircle
open _root_.Poincare
open _root_.PoincareConjecture
open _root_.PoincareConjecture.CapCertificate

namespace M38Schoenflies

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_negative_end_compact_capture_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
          closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆
            C.boundary_neck.closedCollar ((0.75 : ℝ) * C.epsilon⁻¹) := by
  obtain ⟨ε₀, hε₀, hsmall, hcapture⟩ :=
    EpsilonNeck.exists_closure_positive_quarter_subset_closedCollar_of_central_sphere_contact.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε
  have hcontact : (closure (C.end_neck.reversed.region
      (C.end_neck.reversed.epsilon⁻¹ / 2) C.end_neck.reversed.epsilon⁻¹) ∩
        C.boundary_neck.central_sphere).Nonempty := by
    refine ⟨C.boundary_neck.center, ?_, C.boundary_neck.center_on_central_sphere⟩
    have hboundary : C.boundary_neck.center ∈ C.boundary_sphere :=
      C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
    simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
      C.end_neck_epsilon, neg_div] using C.boundary_subset_negative_end_closure hboundary
  have h := hcapture C.end_neck.reversed C.boundary_neck
    (by simpa only [EpsilonNeck.reversed_epsilon, C.end_neck_epsilon] using hε)
    (by rw [EpsilonNeck.reversed_epsilon, C.end_neck_epsilon, C.boundary_neck_epsilon]) hcontact
  simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
    C.end_neck_epsilon, C.boundary_neck_epsilon, neg_div] using h

theorem exists_compact_truncated_core_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ → ∀ a : ℝ, a < C.epsilon⁻¹ →
          IsCompact (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)) ∧
            C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a) ⊆ C.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, hcapture⟩ := exists_negative_end_compact_capture_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε a ha
  have hr : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hrad : (0.75 : ℝ) * C.epsilon⁻¹ < C.boundary_neck.epsilon⁻¹ := by
    rw [C.boundary_neck_epsilon]
    linarith
  have hnegative := hcapture C hε
  have hnegative_compact : IsCompact
      (closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2))) :=
    (C.boundary_neck.isCompact_closedCollar hrad).of_isClosed_subset isClosed_closure hnegative
  have hnegative_sub : closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆
      C.carrier := hnegative.trans
    ((C.boundary_neck.closedCollar_subset_carrier hrad).trans C.boundary_neck_subset)
  let b := max a (-C.epsilon⁻¹ / 2)
  let K := C.end_neck.coordinate_map '' (univ ×ˢ Icc (-C.epsilon⁻¹ / 2) b)
  have hlo : -C.end_neck.epsilon⁻¹ < -C.epsilon⁻¹ / 2 := by
    rw [C.end_neck_epsilon]
    linarith
  have hhi : b < C.end_neck.epsilon⁻¹ := by
    rw [C.end_neck_epsilon]
    exact max_lt ha (by linarith)
  have hK : IsCompact K := C.end_neck.isCompact_coordinate_slab hlo hhi
  have hKsub : K ⊆ C.carrier := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.end_neck_subset (C.end_neck.coordinate_map_mem
      ⟨mem_univ _, hlo.trans_le hz.2.1, hz.2.2.trans_lt hhi⟩)
  have hreg : C.end_neck.region (-C.epsilon⁻¹) a ⊆
      C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ∪ K := by
    intro x hx
    by_cases hax : (C.end_neck.coordinate_inverse x).2 < -C.epsilon⁻¹ / 2
    · exact Or.inl ⟨hx.1, hx.2.1, hax⟩
    · exact Or.inr ⟨C.end_neck.coordinate_inverse x,
        ⟨mem_univ _, le_of_not_gt hax, hx.2.2.le.trans (le_max_left _ _)⟩,
        C.end_neck.coordinate_map_coordinate_inverse hx.1⟩
  have hclosure : closure (C.end_neck.region (-C.epsilon⁻¹) a) ⊆
      closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ∪ K := by
    simpa only [closure_union, hK.isClosed.closure_eq] using closure_mono hreg
  refine ⟨C.closed_core_compact.union
    ((hnegative_compact.union hK).of_isClosed_subset isClosed_closure hclosure), ?_⟩
  exact union_subset C.closed_core_subset_carrier
    (hclosure.trans (union_subset hnegative_sub hKsub))

end PoincareConjecture.CapCertificate

end M38Schoenflies
