import PoincareConjecture.Proofs.M47.CanonicalNeckPersistence
import PoincareConjecture.Proofs.M47.CanonicalCoreBallContainment
import PoincareConjecture.Proofs.M47.CanonicalNormalizedBallExistence
import PoincareConjecture.Proofs.M47.CanonicalCoreVolumeMargin
import PoincareConjecture.Proofs.M47.CanonicalAnalyticStability
import PoincareConjecture.Proofs.M47.CanonicalGeometricMargins










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [CompactSpace M] [SecondCountableTopology M]




theorem eventually_same_cap_certificate
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b)) (t : Icc a b)
    (N : CapCertificate (F.metric t.val)) (hconnection : N.connection = F.connection t.val) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∃ N' : CapCertificate (F.metric s.val),
      N'.epsilon = N.epsilon ∧ N'.cap_constant = N.cap_constant ∧
      N'.carrier = N.carrier ∧ N'.closed_core = N.closed_core ∧ N'.core = N.core ∧
      N'.boundary_sphere = N.boundary_sphere ∧ N'.connection = F.connection s.val := by
  classical
  obtain ⟨bR, hbR, hratio⟩ := cap_scalar_ratio_persists hC F t N hconnection
  obtain ⟨bG, hbG, hgradient⟩ := cap_gradient_bound_persists hC F t N hconnection
  obtain ⟨bE, hbE, hevolution⟩ := cap_evolution_bound_persists hC F t N hconnection
  obtain ⟨bV, hbV, hcorevolume⟩ := cap_core_ball_volume_bound_persists hC F t N hconnection
  have hend := eventually_same_epsilon_neck hC hab F t N.end_neck
    (N.end_neck_connection.trans hconnection) isCompact_univ (subset_univ _)
  have hboundary := eventually_same_epsilon_neck hC hab F t N.boundary_neck
    (N.boundary_neck_connection.trans hconnection) isCompact_univ (subset_univ _)
  filter_upwards [hratio, hgradient, hevolution, hcorevolume,
    cap_intrinsic_diameter_bound_persists hC F t N hconnection,
    cap_volume_bound_persists hC F t N hconnection, hend, hboundary]
    with s hratio hgradient hevolution hcorevolume hdiameter hvolume hend hboundary
  obtain ⟨E, hEe, _, hEcarrier, _, hEinverse, _, hEconnection, _⟩ := hend
  obtain ⟨B, hBe, _, hBcarrier, _, _, hBsphere, hBconnection, _⟩ := hboundary
  have hbounded : BddAbove (range (F.connection s.val).scalarCurvature) :=
    (isCompact_range (M34.contMDiff_scalarCurvature (F.connection s.val)).continuous).bddAbove
  have hballs (y : N.core) : ∃ r : ℝ, 0 < r ∧
      scalarCurvatureSupOn (F.metric s.val) (F.connection s.val)
        ((F.metric s.val).ball y.val r) = r⁻¹ ^ 2 ∧
      IsCompact (closure ((F.metric s.val).ball y.val r)) ∧
      closure ((F.metric s.val).ball y.val r) ⊆ N.carrier := by
    have hycarrier := N.core_subset_carrier' y.property
    have hyclosed : y.val ∈ N.closed_core := by
      have hsub : N.core ⊆ N.closed_core := by
        rw [N.core_eq_interior_closed_core]
        exact interior_subset
      exact hsub y.property
    obtain ⟨r, hr, _, hnorm, _⟩ := exists_scalar_normalized_ball_on_compact
      (F.metric s.val) (F.connection s.val) y.val (hratio.1 y.val hycarrier)
    have hbdd : BddAbove ((F.connection s.val).scalarCurvature ''
        (F.metric s.val).ball y.val r) := hbounded.mono (image_subset_range _ _)
    have hcapture := scalar_normalized_core_ball_captured N E (F.connection s.val)
      hEconnection hEcarrier hEinverse hyclosed hr hbdd hnorm
    exact ⟨r, hr, hnorm, hcapture⟩
  choose radius hradius hnormal hcompact hsubset using hballs
  let rho : M → ℝ := fun y => if hy : y ∈ N.core then radius ⟨y, hy⟩ else 1
  have hrho (y : M) (hy : y ∈ N.core) :
      0 < rho y ∧ scalarCurvatureSupOn (F.metric s.val) (F.connection s.val)
        ((F.metric s.val).ball y (rho y)) = (rho y)⁻¹ ^ 2 ∧
      IsCompact (closure ((F.metric s.val).ball y (rho y))) ∧
      closure ((F.metric s.val).ball y (rho y)) ⊆ N.carrier := by
    simp only [rho, dif_pos hy]
    exact ⟨hradius ⟨y, hy⟩, hnormal ⟨y, hy⟩, hcompact ⟨y, hy⟩, hsubset ⟨y, hy⟩⟩
  have hnegative : E.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) =
      N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) := by
    ext x
    simp only [EpsilonNeck.region, hEcarrier, hEinverse]
  let H : CapCertificate (F.metric s.val) := {
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
    connection := F.connection s.val
    end_neck := E
    end_neck_epsilon := hEe.trans N.end_neck_epsilon
    end_neck_subset := by rw [hEcarrier]; exact N.end_neck_subset
    end_neck_connection := hEconnection
    closed_core_eq_complement_end := by rw [hEcarrier]; exact N.closed_core_eq_complement_end
    boundary_sphere := N.boundary_sphere
    boundary_neck := B
    boundary_neck_epsilon := hBe.trans N.boundary_neck_epsilon
    boundary_neck_subset := by rw [hBcarrier]; exact N.boundary_neck_subset
    boundary_neck_connection := hBconnection
    boundary_eq_neck_sphere := N.boundary_eq_neck_sphere.trans hBsphere.symm
    boundary_eq_end_frontier := by rw [hEcarrier]; exact N.boundary_eq_end_frontier
    boundary_subset_negative_end_closure := by
      rw [hnegative]
      exact N.boundary_subset_negative_end_closure
    boundary_subset := N.boundary_subset
    core_frontier_eq_boundary := N.core_frontier_eq_boundary
    boundary_local_defining_function := N.boundary_local_defining_function
    scalar_pos := hratio.1
    intrinsic_diameter_bound := hdiameter
    scalar_ratio := ⟨bR, hbR, hratio.2⟩
    volume_bound := hvolume
    core_radius := rho
    core_radius_pos := fun y hy => (hrho y hy).1
    core_radius_eq := fun y hy => (hrho y hy).2.1
    core_ball_subset := fun y hy => (hrho y hy).2.2.2
    core_ball_compact := fun y hy => (hrho y hy).2.2.1
    core_ball_volume_lower := ⟨bV, hbV, fun y hy =>
      hcorevolume y hy (rho y) (hrho y hy).1 (hrho y hy).2.1⟩
    gradient_bound := ⟨bG, hbG, hgradient⟩
    laplacian_bound := ⟨bE, hbE, hevolution⟩ }
  exact ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.Proofs.M47
