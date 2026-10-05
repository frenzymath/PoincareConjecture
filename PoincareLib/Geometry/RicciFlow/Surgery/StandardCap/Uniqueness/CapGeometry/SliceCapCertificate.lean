import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.SliceStaticNeck
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.TransportedEndTopology
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.BoundaryDefiningFunction

/-!
# The exact quantitative cap on the Chapter 11 slice

Morgan-Tian Definition 9.72 and Theorem 12.28, pp. 323-324.
Every original cap field is transported through the actual slice
diffeomorphism. The numerical constant, epsilon, exact scalar radii,
strict witnesses, and designated image sets are preserved.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.CapCertificate

open M35.OrdinaryRealization

/-- Definition 9.72: the exact ordinary cap supplies a cap on the
genuine generalized-flow slice with every quantitative witness retained. -/
noncomputable def toOrdinarySlice (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (N : CapCertificate (F.metric t)) (hconnection : N.connection = F.connection t) :
    CapCertificate (metric F t) := by
  let e := sliceDiffeomorph ht
  let phi := e.symm.toPartialDiffeomorph
  have hU : N.carrier ⊆ phi.source := subset_univ _
  have hClosure : closure N.carrier ⊆ phi.source := subset_univ _
  have htop := N.transported_core_topology phi hU
  have hopen := htop.1
  have hcompact := htop.2.1
  have hcore := htop.2.2.1
  have hfrontier := htop.2.2.2.1
  have hcomplement := htop.2.2.2.2
  have hend := N.transported_end_attachment phi hClosure
  have hendfrontier := hend.1
  have hendclosure := hend.2
  let ne := N.end_neck.toOrdinarySlice P F ht (N.end_neck_connection.trans hconnection)
  let nb := N.boundary_neck.toOrdinarySlice P F ht
    (N.boundary_neck_connection.trans hconnection)
  have hscalar (x : StandardCapSpace) :
      (M35.OrdinaryRealization.connection F t).scalarCurvature (e.symm x) =
      N.connection.scalarCurvature x := by
    rw [hconnection]
    exact scalar_eq P F ht x
  have hsup (U : Set StandardCapSpace) :
      scalarCurvatureSupOn (metric F t) (M35.OrdinaryRealization.connection F t) (e.symm '' U) =
        scalarCurvatureSupOn (F.metric t) N.connection U := by
    rw [hconnection]
    exact slice_scalarSup_image P F ht U
  have hvolumeImage (U : Set StandardCapSpace) :
      calibratedMetricVolume (metric F t) (e.symm '' U) =
        calibratedMetricVolume (F.metric t) U := volume_image P F ht U
  refine {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_le_threshold := N.epsilon_le_threshold
    cap_constant := N.cap_constant
    cap_constant_pos := N.cap_constant_pos
    carrier := e.symm '' N.carrier
    carrier_open := hopen
    closed_core := e.symm '' N.closed_core
    closed_core_compact := hcompact
    core := e.symm '' N.core
    core_nonempty := N.core_nonempty.image e.symm
    core_eq_interior_closed_core := hcore
    puncture := N.puncture
    model_kind := N.model_kind
    model_equivalence := N.model_equivalence.transported phi hU
    connection := M35.OrdinaryRealization.connection F t
    end_neck := ne
    end_neck_epsilon := N.end_neck_epsilon
    end_neck_subset := image_mono N.end_neck_subset
    end_neck_connection := rfl
    closed_core_eq_complement_end := hcomplement
    boundary_sphere := e.symm '' N.boundary_sphere
    boundary_neck := nb
    boundary_neck_epsilon := N.boundary_neck_epsilon
    boundary_neck_subset := image_mono N.boundary_neck_subset
    boundary_neck_connection := rfl
    boundary_eq_neck_sphere := congrArg (image e.symm) N.boundary_eq_neck_sphere
    boundary_eq_end_frontier := hendfrontier
    boundary_subset_negative_end_closure := ?_
    boundary_subset := image_mono N.boundary_subset
    core_frontier_eq_boundary := hfrontier.symm
    boundary_local_defining_function := N.transported_boundary_local_defining_function phi hU
    scalar_pos := ?_
    intrinsic_diameter_bound := ?_
    scalar_ratio := ?_
    volume_bound := ?_
    core_radius := N.core_radius ∘ e
    core_radius_pos := ?_
    core_radius_eq := ?_
    core_ball_subset := ?_
    core_ball_compact := ?_
    core_ball_volume_lower := ?_
    gradient_bound := ?_
    laplacian_bound := ?_
  }
  · change e.symm '' N.boundary_sphere ⊆
      closure ((N.end_neck.toOrdinarySlice P F ht
        (N.end_neck_connection.trans hconnection)).region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2))
    rw [N.end_neck.toOrdinarySlice_region]
    exact hendclosure
  · rintro _ ⟨x, hx, rfl⟩
    rw [hscalar]
    exact N.scalar_pos x hx
  · rw [hsup]
    exact (slice_intrinsicDiameter_image_le F ht N.carrier_open).trans_lt
      N.intrinsic_diameter_bound
  · obtain ⟨B, hB, hratio⟩ := N.scalar_ratio
    refine ⟨B, hB, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hscalar, hscalar]
    exact hratio x hx y hy
  · rw [hsup, hvolumeImage]
    exact N.volume_bound
  · rintro _ ⟨x, hx, rfl⟩
    exact N.core_radius_pos x hx
  · rintro _ ⟨x, hx, rfl⟩
    change scalarCurvatureSupOn (metric F t) (M35.OrdinaryRealization.connection F t)
      ((metric F t).ball (e.symm x) (N.core_radius x)) = (N.core_radius x)⁻¹ ^ 2
    rw [← slice_ball_image P F ht, hsup]
    exact N.core_radius_eq x hx
  · rintro _ ⟨x, hx, rfl⟩
    change closure ((metric F t).ball (e.symm x) (N.core_radius x)) ⊆ e.symm '' N.carrier
    rw [← slice_closure_ball_image P F ht]
    exact image_mono (N.core_ball_subset x hx)
  · rintro _ ⟨x, hx, rfl⟩
    change IsCompact (closure ((metric F t).ball (e.symm x) (N.core_radius x)))
    rw [← slice_closure_ball_image P F ht]
    exact (N.core_ball_compact x hx).image e.symm.continuous
  · obtain ⟨B, hB, hvolume⟩ := N.core_ball_volume_lower
    refine ⟨B, hB, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change ENNReal.ofReal (B * N.core_radius x ^ 3) ≤
      calibratedMetricVolume (metric F t) ((metric F t).ball (e.symm x) (N.core_radius x))
    rw [← slice_ball_image P F ht]
    exact (hvolume x hx).trans_eq (hvolumeImage _).symm
  · obtain ⟨B, hB, hgradient⟩ := N.gradient_bound
    refine ⟨B, hB, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [slice_scalarGradientNorm_eq P F ht, hscalar, ← hconnection]
    exact hgradient x hx
  · obtain ⟨B, hB, hevolution⟩ := N.laplacian_bound
    refine ⟨B, hB, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [scalar_evolution_eq P F ht, hscalar, ← hconnection]
    exact hevolution x hx

/-- Theorem 12.28: an actual quantitative ordinary cap gives
the exact Chapter 11 canonical-control cap branch at its core points. -/
theorem generalized_canonical_control (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    {t epsilon C : ℝ} (ht : t ∈ Ico 0 F.base.lifetime)
    (N : CapCertificate (F.metric t)) (hepsilon : N.epsilon = epsilon)
    (hC : N.cap_constant ≤ C) (hconnection : N.connection = F.connection t)
    {x : StandardCapSpace} (hx : x ∈ N.core) :
    GeneralizedCanonicalControl (F := generalizedFlow F.base.flow) t
      ((sliceDiffeomorph ht).symm x) epsilon C := by
  exact .cap (N.toOrdinarySlice P F.base.flow ht hconnection) hepsilon hC rfl
    ⟨x, hx, rfl⟩

end PoincareMT.CapCertificate
