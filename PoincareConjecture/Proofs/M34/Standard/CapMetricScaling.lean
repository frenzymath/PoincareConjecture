import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

noncomputable def scaleMetric (N : CapCertificate g) (Q : ℝ) (hQ : 0 < Q) :
    CapCertificate (M13.scaleSmoothMetric g Q hQ) where
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_le_threshold := N.epsilon_le_threshold
  cap_constant := N.cap_constant
  cap_constant_pos := N.cap_constant_pos
  carrier := N.carrier
  carrier_open := N.carrier_open
  closed_core := N.closed_core
  closed_core_compact := N.closed_core_compact
  core := N.core
  core_nonempty := N.core_nonempty
  core_eq_interior_closed_core := N.core_eq_interior_closed_core
  puncture := N.puncture
  model_kind := N.model_kind
  model_equivalence := N.model_equivalence
  connection := M13.scaleLeviCivitaData N.connection Q hQ
  end_neck := N.end_neck.scaleMetric Q hQ
  end_neck_epsilon := N.end_neck_epsilon
  end_neck_subset := N.end_neck_subset
  end_neck_connection := congrArg (fun D => M13.scaleLeviCivitaData D Q hQ)
    N.end_neck_connection
  closed_core_eq_complement_end := N.closed_core_eq_complement_end
  boundary_sphere := N.boundary_sphere
  boundary_neck := N.boundary_neck.scaleMetric Q hQ
  boundary_neck_epsilon := N.boundary_neck_epsilon
  boundary_neck_subset := N.boundary_neck_subset
  boundary_neck_connection := congrArg (fun D => M13.scaleLeviCivitaData D Q hQ)
    N.boundary_neck_connection
  boundary_eq_neck_sphere := N.boundary_eq_neck_sphere
  boundary_eq_end_frontier := N.boundary_eq_end_frontier
  boundary_subset_negative_end_closure := N.boundary_subset_negative_end_closure
  boundary_subset := N.boundary_subset
  core_frontier_eq_boundary := N.core_frontier_eq_boundary
  boundary_local_defining_function := N.boundary_local_defining_function
  scalar_pos x hx := by
    rw [M13.scaleLeviCivitaData_scalarCurvature]
    exact div_pos (N.scalar_pos x hx) hQ
  intrinsic_diameter_bound := N.scaleMetric_intrinsic_diameter_bound Q hQ
  scalar_ratio := by
    obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
    refine ⟨b, hb, ?_⟩
    intro x hx y hy
    simp only [M13.scaleLeviCivitaData_scalarCurvature]
    calc
      _ ≤ (b * N.connection.scalarCurvature x) / Q :=
        div_le_div_of_nonneg_right (hratio x hx y hy) hQ.le
      _ = _ := by ring
  volume_bound := N.scaleMetric_volume_bound Q hQ
  core_radius y := Real.sqrt Q * N.core_radius y
  core_radius_pos y hy := mul_pos (Real.sqrt_pos.mpr hQ) (N.core_radius_pos y hy)
  core_radius_eq y hy := N.scaleMetric_core_radius_eq Q hQ hy
  core_ball_subset y hy := by
    rw [M13.scaleSmoothMetric_ball]
    exact N.core_ball_subset y hy
  core_ball_compact y hy := by
    rw [M13.scaleSmoothMetric_ball]
    exact N.core_ball_compact y hy
  core_ball_volume_lower := N.scaleMetric_core_ball_volume_lower Q hQ
  gradient_bound := N.scaleMetric_gradient_bound Q hQ
  laplacian_bound := N.scaleMetric_laplacian_bound Q hQ

end PoincareConjecture.CapCertificate
