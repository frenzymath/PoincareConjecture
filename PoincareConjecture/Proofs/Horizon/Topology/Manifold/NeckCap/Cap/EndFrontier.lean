import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Ends
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SphereContact











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}


theorem frontier_carrier_subset_frontier_end (C : CapCertificate g) :
    frontier C.carrier ⊆ frontier C.end_neck.carrier := by
  intro x hx
  have hout : x ∉ C.carrier := (C.carrier_open.frontier_eq ▸ hx).2
  have hclosure : x ∈ C.closed_core ∪ closure C.end_neck.carrier := by
    have h := frontier_subset_closure hx
    rwa [C.carrier_eq_closed_core_union_end, closure_union,
      C.isClosed_closed_core.closure_eq] at h
  have hend : x ∈ closure C.end_neck.carrier := hclosure.resolve_left
    (fun hcore => hout (C.closed_core_subset_carrier hcore))
  rw [C.end_neck.carrier_open.frontier_eq]
  exact ⟨hend, fun hmem => hout (C.end_neck_subset hmem)⟩

private theorem frontier_carrier_subset_positive_of_negative_closure_subset
    (C : CapCertificate g)
    (hnegative : closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆
      C.carrier) :
    frontier C.carrier ⊆ closure (C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by
  have hinv : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  intro x hx
  have hends := C.end_neck.frontier_subset_closure_ends
    (a := -C.epsilon⁻¹ / 2) (b := C.epsilon⁻¹ / 2)
    (by rw [C.end_neck_epsilon]; linarith)
    (by rw [C.end_neck_epsilon]; linarith)
    (C.frontier_carrier_subset_frontier_end hx)
  rw [C.end_neck_epsilon] at hends
  exact hends.resolve_left (fun hneg =>
    (C.carrier_open.frontier_eq ▸ hx).2 (hnegative hneg))

omit [T2Space M] in
private theorem reversed_end_boundary_sphere_contact (C : CapCertificate g) :
    (closure (C.end_neck.reversed.region
      (C.end_neck.reversed.epsilon⁻¹ / 2) C.end_neck.reversed.epsilon⁻¹) ∩
        C.boundary_neck.central_sphere).Nonempty := by
  refine ⟨C.boundary_neck.center, ?_, C.boundary_neck.center_on_central_sphere⟩
  have hboundary : C.boundary_neck.center ∈ C.boundary_sphere :=
    C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
  simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
    C.end_neck_epsilon, neg_div] using C.boundary_subset_negative_end_closure hboundary



theorem exists_frontier_carrier_subset_closure_positive_end :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
          frontier C.carrier ⊆
            closure (C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by
  obtain ⟨ε₀, hε₀, hsmall, hcontact⟩ :=
    EpsilonNeck.exists_closure_positive_quarter_subset_of_central_sphere_contact.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε
  have hend : C.end_neck.reversed.epsilon ≤ ε₀ := by
    simpa only [EpsilonNeck.reversed_epsilon, C.end_neck_epsilon] using hε
  have heq : C.boundary_neck.epsilon = C.end_neck.reversed.epsilon := by
    rw [EpsilonNeck.reversed_epsilon, C.boundary_neck_epsilon, C.end_neck_epsilon]
  have hnegative := hcontact C.end_neck.reversed C.boundary_neck hend heq
    C.reversed_end_boundary_sphere_contact
  have hnegative' : closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆
      C.boundary_neck.carrier := by
    simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
      C.end_neck_epsilon, neg_div] using hnegative
  exact C.frontier_carrier_subset_positive_of_negative_closure_subset
    (hnegative'.trans C.boundary_neck_subset)

end PoincareConjecture.CapCertificate
