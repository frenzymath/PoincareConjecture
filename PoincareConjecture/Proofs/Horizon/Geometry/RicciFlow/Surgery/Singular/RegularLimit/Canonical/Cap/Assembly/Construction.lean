import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Assembly.Quantitative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Topology



set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]



theorem exists_cap_of_linked_necks
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {ε C : ℝ} (hε : ε ≤ 1 / 200) (hC : 0 < C)
    (kind : CapModelKind) (p : RealProjectiveThree) (U K core B : Set M)
    (endNeck boundaryNeck : EpsilonNeck g)
    (hendε : endNeck.epsilon = ε) (hboundaryε : boundaryNeck.epsilon = ε)
    (hendD : endNeck.connection = D) (hboundaryD : boundaryNeck.connection = D)
    (hboundarySubset : boundaryNeck.carrier ⊆ U)
    (hboundarySphere : B = boundaryNeck.central_sphere)
    (htopology : CapDomainTopology kind p U K core B endNeck.carrier
      (endNeck.region (-ε⁻¹) (-ε⁻¹ / 2)))
    (hquantitative : CapQuantitativeData g D C U core) :
    ∃ N : CapCertificate g,
      N.epsilon = ε ∧ N.cap_constant = C ∧ N.connection = D ∧
      N.carrier = U ∧ N.core = core ∧ N.closed_core = K ∧
      N.boundary_sphere = B ∧ N.model_kind = kind ∧
      N.end_neck = endNeck ∧ N.boundary_neck = boundaryNeck := by
  let N : CapCertificate g := {
    epsilon := ε
    epsilon_pos := hendε ▸ endNeck.epsilon_pos
    epsilon_le_threshold := hε
    cap_constant := C
    cap_constant_pos := hC
    carrier := U
    carrier_open := htopology.carrier_open
    closed_core := K
    closed_core_compact := htopology.closed_core_compact
    core := core
    core_nonempty := htopology.core_nonempty
    core_eq_interior_closed_core := htopology.core_eq_interior
    puncture := p
    model_kind := kind
    model_equivalence := htopology.model_equivalence
    connection := D
    end_neck := endNeck
    end_neck_epsilon := hendε
    end_neck_subset := htopology.end_subset
    end_neck_connection := hendD
    closed_core_eq_complement_end := htopology.closed_core_eq_complement_end
    boundary_sphere := B
    boundary_neck := boundaryNeck
    boundary_neck_epsilon := hboundaryε
    boundary_neck_subset := hboundarySubset
    boundary_neck_connection := hboundaryD
    boundary_eq_neck_sphere := hboundarySphere
    boundary_eq_end_frontier := htopology.boundary_eq_end_frontier
    boundary_subset_negative_end_closure := htopology.boundary_subset_negative_end_closure
    boundary_subset := htopology.boundary_subset
    core_frontier_eq_boundary := htopology.core_frontier_eq_boundary
    boundary_local_defining_function := htopology.boundary_local_defining_function
    scalar_pos := hquantitative.scalar_pos
    intrinsic_diameter_bound := hquantitative.intrinsic_diameter_bound
    scalar_ratio := hquantitative.scalar_ratio
    volume_bound := hquantitative.volume_bound
    core_radius := hquantitative.core_radius
    core_radius_pos := hquantitative.core_radius_pos
    core_radius_eq := hquantitative.core_radius_eq
    core_ball_subset := hquantitative.core_ball_subset
    core_ball_compact := hquantitative.core_ball_compact
    core_ball_volume_lower := hquantitative.core_ball_volume_lower
    gradient_bound := hquantitative.gradient_bound
    laplacian_bound := hquantitative.laplacian_bound }
  exact ⟨N, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.SingularRegularLimit
