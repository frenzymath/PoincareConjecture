import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Buffered.Fields











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive.SoulCapGeometry

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {delta D R epsilon C : ℝ}
  {G : SoulNeckRegion K S delta D R} (H : SoulCapGeometry G epsilon)
  (hsmall : epsilon ≤ 1 / 200) (hC : 0 < C) (B : BufferedRegionBounds H C)


noncomputable def capCertificate : CapCertificate (K.flow.metric 0) := by
  classical
  let radius : M → ℝ := B.core_ball_fields.choose
  let kappa : ℝ := B.core_ball_fields.choose_spec.choose
  have hballs := B.core_ball_fields.choose_spec.choose_spec
  letI : Nonempty RealProjectiveThree :=
    ⟨Quotient.mk' ⟨EuclideanSpace.basisFun (Fin 4) ℝ 0, by simp⟩⟩
  let p : RealProjectiveThree := Classical.choice inferInstance
  exact {
    epsilon := epsilon
    epsilon_pos := H.epsilon_pos
    epsilon_le_threshold := hsmall
    cap_constant := C
    cap_constant_pos := hC
    carrier := H.carrier
    carrier_open := H.carrier_open
    closed_core := closure G.inside
    closed_core_compact := G.compact_side
    core := G.inside
    core_nonempty := G.inside_connected.nonempty
    core_eq_interior_closed_core := G.interior_closure_inside.symm
    puncture := p
    model_kind := .euclidean
    model_equivalence := Classical.choice (H.nonempty_model p)
    connection := K.flow.connection 0
    end_neck := H.endNeck
    end_neck_epsilon := H.end_epsilon
    end_neck_subset := H.end_subset
    end_neck_connection := H.end_connection
    closed_core_eq_complement_end := H.closed_core_eq_complement_end
    boundary_sphere := H.source.central_sphere
    boundary_neck := H.boundary
    boundary_neck_epsilon := H.boundary_epsilon
    boundary_neck_subset := H.boundary_subset
    boundary_neck_connection := H.boundary_connection
    boundary_eq_neck_sphere := H.boundary_sphere.symm
    boundary_eq_end_frontier := H.boundary_eq_end_frontier
    boundary_subset_negative_end_closure := H.boundary_subset_negative_end_closure
    boundary_subset := H.boundary_sphere_subset
    core_frontier_eq_boundary := H.core_frontier_eq_boundary
    boundary_local_defining_function := fun _ hx => H.boundary_local_defining_function hx
    scalar_pos := B.scalar_pos
    intrinsic_diameter_bound := B.intrinsic_diameter_bound
    scalar_ratio := B.scalar_ratio
    volume_bound := B.volume_bound
    core_radius := radius
    core_radius_pos := fun x hx => (hballs.2 x hx).1
    core_radius_eq := fun x hx => (hballs.2 x hx).2.1
    core_ball_subset := fun x hx => (hballs.2 x hx).2.2.1
    core_ball_compact := fun x hx => (hballs.2 x hx).2.2.2.1
    core_ball_volume_lower := ⟨kappa, hballs.1, fun x hx => (hballs.2 x hx).2.2.2.2⟩
    gradient_bound := B.gradient_bound
    laplacian_bound := B.laplacian_bound }

@[simp] theorem capCertificate_epsilon : (H.capCertificate hsmall hC B).epsilon = epsilon := rfl

@[simp] theorem capCertificate_constant : (H.capCertificate hsmall hC B).cap_constant = C := rfl

@[simp] theorem capCertificate_carrier : (H.capCertificate hsmall hC B).carrier = H.carrier := rfl

@[simp] theorem capCertificate_core : (H.capCertificate hsmall hC B).core = G.inside := rfl

@[simp] theorem capCertificate_closed_core :
    (H.capCertificate hsmall hC B).closed_core = closure G.inside := rfl

@[simp] theorem capCertificate_connection :
    (H.capCertificate hsmall hC B).connection = K.flow.connection 0 := rfl

@[simp] theorem capCertificate_end_neck :
    (H.capCertificate hsmall hC B).end_neck = H.endNeck := rfl

@[simp] theorem capCertificate_boundary_neck :
    (H.capCertificate hsmall hC B).boundary_neck = H.boundary := rfl

@[simp] theorem capCertificate_boundary_sphere :
    (H.capCertificate hsmall hC B).boundary_sphere = H.source.central_sphere := rfl

@[simp] theorem capCertificate_model_kind :
    (H.capCertificate hsmall hC B).model_kind = .euclidean := rfl

end PoincareConjecture.NoncompactKappa.Positive.SoulCapGeometry
