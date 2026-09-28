import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardBoundary










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}




theorem exists_same_constant_outward_cap (N : CapCertificate g)
    {b epsilon : ℝ} (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 200)
    (E B : EpsilonNeck g) (hEe : E.epsilon = epsilon) (hBe : B.epsilon = epsilon)
    (hED : E.connection = N.connection) (hBD : B.connection = N.connection)
    (hEcarrier : E.carrier = N.end_neck.region b N.epsilon⁻¹)
    (hBcarrier : B.carrier ⊆ N.carrier)
    (hBsphere : B.central_sphere =
      N.end_neck.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)))
    (hnegative : B.central_sphere ⊆
      closure (E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)))
    (radius : M → ℝ) (bound : ℝ) (hbound : N.cap_constant⁻¹ < bound)
    (hballs : ∀ y ∈ N.recutCarrier b,
      0 < radius y ∧
      scalarCurvatureSupOn g N.connection (g.ball y (radius y)) = (radius y)⁻¹ ^ 2 ∧
      IsCompact (closure (g.ball y (radius y))) ∧
      closure (g.ball y (radius y)) ⊆ N.carrier ∧
      ENNReal.ofReal (bound * radius y ^ 3) ≤ calibratedMetricVolume g (g.ball y (radius y))) :
    ∃ H : CapCertificate g,
      H.epsilon = epsilon ∧ H.cap_constant = N.cap_constant ∧
      H.carrier = N.carrier ∧ H.connection = N.connection ∧
      H.closed_core = closure (N.recutCarrier b) ∧ H.core = N.recutCarrier b ∧
      N.core ⊆ H.core := by
  have hgeometry := cap_outward_core_geometry N hb hb'
  have hcore : N.core ⊆ N.recutCarrier b := by
    simpa only [cap_outward_core_interior N hb hb'] using hgeometry.2.2
  let H : CapCertificate g := {
    epsilon := epsilon
    epsilon_pos := hepsilon
    epsilon_le_threshold := hepsilon_le
    cap_constant := N.cap_constant
    cap_constant_pos := N.cap_constant_pos
    carrier := N.carrier
    carrier_open := N.carrier_open
    closed_core := closure (N.recutCarrier b)
    closed_core_compact := hgeometry.1
    core := N.recutCarrier b
    core_nonempty := N.core_nonempty.mono hcore
    core_eq_interior_closed_core := (cap_outward_core_interior N hb hb').symm
    puncture := N.puncture
    model_kind := N.model_kind
    model_equivalence := N.model_equivalence
    connection := N.connection
    end_neck := E
    end_neck_epsilon := hEe
    end_neck_subset := by
      rw [hEcarrier]
      exact fun _ hx => N.end_neck_subset hx.1
    end_neck_connection := hED
    closed_core_eq_complement_end := by
      rw [hEcarrier]
      exact cap_outward_core_eq_complement N hb hb'
    boundary_sphere := B.central_sphere
    boundary_neck := B
    boundary_neck_epsilon := hBe
    boundary_neck_subset := hBcarrier
    boundary_neck_connection := hBD
    boundary_eq_neck_sphere := rfl
    boundary_eq_end_frontier := by
      rw [hEcarrier, cap_outward_tail_relative_frontier N hb hb']
      exact hBsphere
    boundary_subset_negative_end_closure := hnegative
    boundary_subset := B.central_sphere_subset.trans hBcarrier
    core_frontier_eq_boundary :=
      (cap_outward_core_frontier N hb hb').trans hBsphere.symm
    boundary_local_defining_function := by
      intro x hx
      apply cap_outward_boundary_local_defining_function N hb hb'
      rwa [cap_outward_core_frontier N hb hb', ← hBsphere]
    scalar_pos := N.scalar_pos
    intrinsic_diameter_bound := N.intrinsic_diameter_bound
    scalar_ratio := N.scalar_ratio
    volume_bound := N.volume_bound
    core_radius := radius
    core_radius_pos := fun y hy => (hballs y hy).1
    core_radius_eq := fun y hy => (hballs y hy).2.1
    core_ball_subset := fun y hy => (hballs y hy).2.2.2.1
    core_ball_compact := fun y hy => (hballs y hy).2.2.1
    core_ball_volume_lower := ⟨bound, hbound, fun y hy => (hballs y hy).2.2.2.2⟩
    gradient_bound := N.gradient_bound
    laplacian_bound := N.laplacian_bound }
  exact ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, hcore⟩

end PoincareConjecture.Proofs.M47
