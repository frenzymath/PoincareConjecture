import PoincareConjecture.Proofs.M35.CapGeometry.TransportedStaticNeck
import PoincareConjecture.Proofs.M35.CapGeometry.TransportedEndTopology
import PoincareConjecture.Proofs.M35.CapGeometry.BoundaryDefiningFunction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.CapCertificate

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}




theorem exists_transported_certificate (N : CapCertificate g)
    (h : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData h)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M StandardCapSpace ∞)
    (hClosure : closure N.carrier ⊆ phi.source)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hscalar : ∀ p ∈ phi '' N.carrier, 0 < D.scalarCurvature p)
    (hend : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.end_neck.center) * roundCylinderPullback h
        (phi ∘ N.end_neck.coordinate_map) z v w))
    (hboundary : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.boundary_neck.center) * roundCylinderPullback h
        (phi ∘ N.boundary_neck.coordinate_map) z v w))
    (hdiameter : intrinsicDiameter h (phi '' N.carrier) <
      ENNReal.ofReal (2 * N.cap_constant *
        scalarCurvatureSupOn h D (phi '' N.carrier) ^ (-1 / 2 : ℝ)))
    (hratio : ∃ B : ℝ, B < N.cap_constant ∧
      ∀ p ∈ phi '' N.carrier, ∀ q ∈ phi '' N.carrier,
        D.scalarCurvature q ≤ B * D.scalarCurvature p)
    (hvolume : calibratedMetricVolume h (phi '' N.carrier) <
      ENNReal.ofReal (8 * N.cap_constant *
        scalarCurvatureSupOn h D (phi '' N.carrier) ^ (-3 / 2 : ℝ)))
    (hradius : ∀ p ∈ phi '' N.core, ∃ r : ℝ, 0 < r ∧
      scalarCurvatureSupOn h D (h.ball p r) = r⁻¹ ^ 2 ∧
      closure (h.ball p r) ⊆ phi '' N.carrier ∧ IsCompact (closure (h.ball p r)))
    (hballvolume : ∀ p ∈ phi '' N.core, ∀ r : ℝ, 0 < r →
      scalarCurvatureSupOn h D (h.ball p r) = r⁻¹ ^ 2 →
      ENNReal.ofReal (kappa / 8 * r ^ 3) ≤ calibratedMetricVolume h (h.ball p r))
    (hgradient : ∀ p ∈ phi '' N.carrier,
      scalarGradientNorm h D p ≤ 8 * N.cap_constant * D.scalarCurvature p ^ (3 / 2 : ℝ))
    (hevolution : ∀ p ∈ phi '' N.carrier,
      |D.laplacian D.scalarCurvature p + 2 * D.ricciNormSq p| ≤
        8 * N.cap_constant * D.scalarCurvature p ^ 2) :
    ∃ C : CapCertificate h,
      C.epsilon = N.epsilon ∧ C.cap_constant = 8 * N.cap_constant + 16 / kappa ∧
      C.connection = D ∧ C.carrier = phi '' N.carrier ∧ C.core = phi '' N.core ∧
      C.closed_core = phi '' N.closed_core ∧ C.boundary_sphere = phi '' N.boundary_sphere ∧
      C.model_kind = N.model_kind := by
  classical
  have hU : N.carrier ⊆ phi.source := subset_closure.trans hClosure
  have heU : N.end_neck.carrier ⊆ phi.source := N.end_neck_subset.trans hU
  have hbU : N.boundary_neck.carrier ⊆ phi.source := N.boundary_neck_subset.trans hU
  have hepos : 0 < D.scalarCurvature (phi N.end_neck.center) := hscalar _
    ⟨_, N.end_neck_subset
      (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere), rfl⟩
  have hbpos : 0 < D.scalarCurvature (phi N.boundary_neck.center) := hscalar _
    ⟨_, N.boundary_neck_subset
      (N.boundary_neck.central_sphere_subset N.boundary_neck.center_on_central_sphere), rfl⟩
  have heclose : RoundCylinderClose N.end_neck.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.end_neck.center) * roundCylinderPullback h
        (phi ∘ N.end_neck.coordinate_map) z v w) := by
    simpa only [N.end_neck_epsilon] using hend
  have hbclose : RoundCylinderClose N.boundary_neck.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.boundary_neck.center) * roundCylinderPullback h
        (phi ∘ N.boundary_neck.coordinate_map) z v w) := by
    simpa only [N.boundary_neck_epsilon] using hboundary
  let ne := N.end_neck.transportedStatic h D phi heU hepos heclose
  let nb := N.boundary_neck.transportedStatic h D phi hbU hbpos hbclose
  have hecarrier : ne.carrier = phi '' N.end_neck.carrier :=
    N.end_neck.transportedStatic_carrier h D phi heU hepos heclose
  have hbcarrier : nb.carrier = phi '' N.boundary_neck.carrier :=
    N.boundary_neck.transportedStatic_carrier h D phi hbU hbpos hbclose
  obtain ⟨hopen, hcompact, hcore, hfrontier, hcomplement⟩ := N.transported_core_topology phi hU
  obtain ⟨hendfrontier, hendclosure⟩ := N.transported_end_attachment phi hClosure
  let c := 8 * N.cap_constant + 16 / kappa
  have hNpos := N.cap_constant_pos
  have hslack : 0 < 16 / kappa := div_pos (by norm_num) hkappa
  have hc : 0 < c := by dsimp [c]; positivity
  have h8c : 8 * N.cap_constant < c := by dsimp [c]; linarith
  have h2c : 2 * N.cap_constant ≤ c := by
    dsimp [c]
    linarith [N.cap_constant_pos]
  have hNc : N.cap_constant < c := by
    dsimp [c]
    linarith [N.cap_constant_pos]
  have hinverse : c⁻¹ < kappa / 8 := by
    apply (inv_lt_iff_one_lt_mul₀ hc).mpr
    have hcancel : (kappa / 8) * (16 / kappa) = 2 := by
      field_simp
      ring
    have hpositive : 0 < (kappa / 8) * (8 * N.cap_constant) := by
      positivity
    dsimp [c]
    rw [mul_add, hcancel]
    linarith
  let rho (p : StandardCapSpace) : ℝ :=
    if hp : p ∈ phi '' N.core then Classical.choose (hradius p hp) else 1
  have hrho (p : StandardCapSpace) (hp : p ∈ phi '' N.core) :
      0 < rho p ∧ scalarCurvatureSupOn h D (h.ball p (rho p)) = (rho p)⁻¹ ^ 2 ∧
        closure (h.ball p (rho p)) ⊆ phi '' N.carrier ∧
          IsCompact (closure (h.ball p (rho p))) := by
    simpa only [rho, dif_pos hp] using Classical.choose_spec (hradius p hp)
  let C : CapCertificate h := {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_le_threshold := N.epsilon_le_threshold
    cap_constant := c
    cap_constant_pos := hc
    carrier := phi '' N.carrier
    carrier_open := hopen
    closed_core := phi '' N.closed_core
    closed_core_compact := hcompact
    core := phi '' N.core
    core_nonempty := N.core_nonempty.image phi
    core_eq_interior_closed_core := hcore
    puncture := N.puncture
    model_kind := N.model_kind
    model_equivalence := N.model_equivalence.transported phi hU
    connection := D
    end_neck := ne
    end_neck_epsilon := N.end_neck_epsilon
    end_neck_subset := by rw [hecarrier]; exact image_mono N.end_neck_subset
    end_neck_connection := rfl
    closed_core_eq_complement_end := by rw [hecarrier]; exact hcomplement
    boundary_sphere := phi '' N.boundary_sphere
    boundary_neck := nb
    boundary_neck_epsilon := N.boundary_neck_epsilon
    boundary_neck_subset := by rw [hbcarrier]; exact image_mono N.boundary_neck_subset
    boundary_neck_connection := rfl
    boundary_eq_neck_sphere := by
      change phi '' N.boundary_sphere =
        (N.boundary_neck.transportedStatic h D phi hbU hbpos hbclose).central_sphere
      rw [N.boundary_neck.transportedStatic_central_sphere, N.boundary_eq_neck_sphere]
    boundary_eq_end_frontier := by rw [hecarrier]; exact hendfrontier
    boundary_subset_negative_end_closure := by
      change phi '' N.boundary_sphere ⊆ closure
        ((N.end_neck.transportedStatic h D phi heU hepos heclose).region
          (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2))
      rw [N.end_neck.transportedStatic_region]
      exact hendclosure
    boundary_subset := image_mono N.boundary_subset
    core_frontier_eq_boundary := hfrontier.symm
    boundary_local_defining_function := N.transported_boundary_local_defining_function phi hU
    scalar_pos := hscalar
    intrinsic_diameter_bound := by
      rw [ENNReal.ofReal_mul hc.le]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * N.cap_constant)] at hdiameter
      apply hdiameter.trans_le
      gcongr
    scalar_ratio := by
      obtain ⟨B, hB, hratioB⟩ := hratio
      exact ⟨B, hB.trans hNc, hratioB⟩
    volume_bound := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * N.cap_constant)] at hvolume
      apply hvolume.trans_le
      gcongr
    core_radius := rho
    core_radius_pos := fun p hp => (hrho p hp).1
    core_radius_eq := fun p hp => (hrho p hp).2.1
    core_ball_subset := fun p hp => (hrho p hp).2.2.1
    core_ball_compact := fun p hp => (hrho p hp).2.2.2
    core_ball_volume_lower := ⟨kappa / 8, hinverse,
      fun p hp => hballvolume p hp (rho p) (hrho p hp).1 (hrho p hp).2.1⟩
    gradient_bound := ⟨8 * N.cap_constant, h8c, hgradient⟩
    laplacian_bound := ⟨8 * N.cap_constant, h8c, hevolution⟩
  }
  exact ⟨C, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.CapCertificate
