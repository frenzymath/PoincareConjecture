import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareLib.Geometry.Riemannian.Measure.Calibrated

/-!
# Geometric cap certificates

Adapted from Mapher, `PoincareMT/Definitions/Ch09/NeckCapTopology.lean`, commit
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.
Declaration bodies are retained; only the required definition closure is imported.
The evolution bound includes the absolute value in Definition 9.72(8),
pp. 230--231, as in the corrected frozen source.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

structure CapCertificate (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_threshold : epsilon ≤ 1 / 200
  cap_constant : ℝ
  cap_constant_pos : 0 < cap_constant
  carrier : Set M
  carrier_open : IsOpen carrier
  closed_core : Set M
  closed_core_compact : IsCompact closed_core
  core : Set M
  core_nonempty : core.Nonempty
  core_eq_interior_closed_core : core = interior closed_core
  puncture : RealProjectiveThree
  model_kind : CapModelKind
  model_equivalence : CapModelEquivalence model_kind puncture carrier
  connection : LeviCivitaData g
  end_neck : EpsilonNeck g
  end_neck_epsilon : end_neck.epsilon = epsilon
  end_neck_subset : end_neck.carrier ⊆ carrier
  end_neck_connection : end_neck.connection = connection
  closed_core_eq_complement_end : closed_core = carrier \ end_neck.carrier
  boundary_sphere : Set M
  boundary_neck : EpsilonNeck g
  boundary_neck_epsilon : boundary_neck.epsilon = epsilon
  boundary_neck_subset : boundary_neck.carrier ⊆ carrier
  boundary_neck_connection : boundary_neck.connection = connection
  boundary_eq_neck_sphere : boundary_sphere = boundary_neck.central_sphere
  boundary_eq_end_frontier : boundary_sphere = carrier ∩ frontier end_neck.carrier
  boundary_subset_negative_end_closure : boundary_sphere ⊆
    closure (end_neck.region (-epsilon⁻¹) (-epsilon⁻¹ / 2))
  boundary_subset : boundary_sphere ⊆ carrier
  core_frontier_eq_boundary : frontier closed_core = boundary_sphere
  boundary_local_defining_function : ∀ x ∈ boundary_sphere, ∃ U : Set M, ∃ f : M → ℝ,
    IsOpen U ∧ x ∈ U ∧ U ⊆ carrier ∧
      (∀ y ∈ U, y ∈ closed_core ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
      ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧
        mvfderiv (𝓡 3) (fun y ↦ f y) x d ≠ 0
  scalar_pos : ∀ x ∈ carrier, 0 < connection.scalarCurvature x
  intrinsic_diameter_bound : intrinsicDiameter g carrier <
    ENNReal.ofReal (cap_constant * scalarCurvatureSupOn g connection
      carrier ^ (-1 / 2 : ℝ))
  scalar_ratio : ∃ bound : ℝ, bound < cap_constant ∧
    ∀ x ∈ carrier, ∀ y ∈ carrier,
      connection.scalarCurvature y ≤ bound * connection.scalarCurvature x
  volume_bound : calibratedMetricVolume g carrier <
    ENNReal.ofReal cap_constant *
      ENNReal.ofReal (scalarCurvatureSupOn g connection carrier ^ (-3 / 2 : ℝ))
  core_radius : M → ℝ
  core_radius_pos : ∀ y ∈ core, 0 < core_radius y
  core_radius_eq : ∀ y ∈ core,
    scalarCurvatureSupOn g connection (g.ball y (core_radius y)) =
      (core_radius y)⁻¹ ^ 2
  core_ball_subset : ∀ y ∈ core, closure (g.ball y (core_radius y)) ⊆ carrier
  core_ball_compact : ∀ y ∈ core,
    IsCompact (closure (g.ball y (core_radius y)))
  core_ball_volume_lower : ∃ bound : ℝ, cap_constant⁻¹ < bound ∧
    ∀ y ∈ core, ENNReal.ofReal (bound * core_radius y ^ 3) ≤
      calibratedMetricVolume g (g.ball y (core_radius y))
  gradient_bound : ∃ bound : ℝ, bound < cap_constant ∧ ∀ x ∈ carrier,
    scalarGradientNorm g connection x ≤ bound *
      (connection.scalarCurvature x) ^ (3 / 2 : ℝ)
  laplacian_bound : ∃ bound : ℝ, bound < cap_constant ∧ ∀ x ∈ carrier,
    |connection.laplacian connection.scalarCurvature x +
        2 * connection.ricciNormSq x| ≤ bound *
      (connection.scalarCurvature x) ^ 2

end PoincareMT
