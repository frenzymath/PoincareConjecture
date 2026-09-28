import PoincareConjecture.Proofs.M34.Standard.CapIsometryGeometry
import PoincareConjecture.Proofs.M34.Standard.CapIsometryScalar
import PoincareConjecture.Proofs.M34.Standard.CapIsometryTopology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [MeasurableSpace X] [BorelSpace M] [BorelSpace X]
  [T3Space M] [T3Space X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}

theorem exists_isometric_image_cap_of_necks (N : CapCertificate g)
    (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1)
    (D : LeviCivitaData h) (Eend Eboundary : EpsilonNeck h)
    (hend_epsilon : Eend.epsilon = N.epsilon)
    (hboundary_epsilon : Eboundary.epsilon = N.epsilon)
    (hend_connection : Eend.connection = D)
    (hboundary_connection : Eboundary.connection = D)
    (hend_carrier : Eend.carrier = f '' N.end_neck.carrier)
    (hboundary_carrier : Eboundary.carrier = f '' N.boundary_neck.carrier)
    (hboundary_sphere : Eboundary.central_sphere = f '' N.boundary_sphere)
    (hend_negative : Eend.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) =
      f '' N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) :
    ∃ H : CapCertificate h, H.epsilon = N.epsilon ∧ H.cap_constant = N.cap_constant ∧
      H.connection = D ∧ H.core = f '' N.core ∧ H.carrier = f '' N.carrier := by
  classical
  let : T25Space X := T3Space.t25Space
  let : T2Space X := T25Space.t2Space
  have hscalar := M34.metricIsometry_scalar f hf N.connection D
  have hsup := M34.metricIsometry_scalarSup f hf N.connection D
  have hball := M34.metricIsometry_ball g h f hf
  have hvolume := M34.metricIsometry_volume g h f hf
  have himage_closure (U : Set M) : f '' closure U = closure (f '' U) :=
    f.toHomeomorph.image_closure U
  have himage_frontier (U : Set M) : f '' frontier U = frontier (f '' U) :=
    f.toHomeomorph.image_frontier U
  have hclosure (x : M) (r : ℝ) :
      closure (h.ball (f x) r) = f '' closure (g.ball x r) := by
    rw [← hball, himage_closure]
  obtain ⟨model⟩ := N.nonempty_diffeomorph_imageModel f
  let H : CapCertificate h := {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_le_threshold := N.epsilon_le_threshold
    cap_constant := N.cap_constant
    cap_constant_pos := N.cap_constant_pos
    carrier := f '' N.carrier
    carrier_open := f.toHomeomorph.isOpenMap _ N.carrier_open
    closed_core := f '' N.closed_core
    closed_core_compact := N.closed_core_compact.image f.continuous
    core := f '' N.core
    core_nonempty := N.core_nonempty.image f
    core_eq_interior_closed_core := by
      rw [N.core_eq_interior_closed_core]
      exact f.toHomeomorph.image_interior _
    puncture := N.puncture
    model_kind := N.model_kind
    model_equivalence := model
    connection := D
    end_neck := Eend
    end_neck_epsilon := hend_epsilon
    end_neck_subset := by rw [hend_carrier]; exact image_mono N.end_neck_subset
    end_neck_connection := hend_connection
    closed_core_eq_complement_end := by
      rw [hend_carrier, N.closed_core_eq_complement_end]
      exact Set.image_sdiff f.injective _ _
    boundary_sphere := f '' N.boundary_sphere
    boundary_neck := Eboundary
    boundary_neck_epsilon := hboundary_epsilon
    boundary_neck_subset := by rw [hboundary_carrier]; exact image_mono N.boundary_neck_subset
    boundary_neck_connection := hboundary_connection
    boundary_eq_neck_sphere := hboundary_sphere.symm
    boundary_eq_end_frontier := by
      rw [hend_carrier, N.boundary_eq_end_frontier, ← himage_frontier]
      exact Set.image_inter f.injective
    boundary_subset_negative_end_closure := by
      rw [hend_negative, ← himage_closure]
      exact image_mono N.boundary_subset_negative_end_closure
    boundary_subset := image_mono N.boundary_subset
    core_frontier_eq_boundary := by
      rw [← himage_frontier, N.core_frontier_eq_boundary]
    boundary_local_defining_function := N.diffeomorph_image_boundary_local_defining_function f
    scalar_pos := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hscalar]
      exact N.scalar_pos x hx
    intrinsic_diameter_bound := by
      rw [M34.metricIsometry_intrinsicDiameter g h f hf, hsup]
      exact N.intrinsic_diameter_bound
    scalar_ratio := by
      obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
      refine ⟨b, hb, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [hscalar, hscalar]
      exact hratio x hx y hy
    volume_bound := by
      rw [hvolume, hsup]
      exact N.volume_bound
    core_radius := N.core_radius ∘ f.symm
    core_radius_pos := by
      rintro _ ⟨y, hy, rfl⟩
      simpa only [Function.comp_apply, f.symm_apply_apply] using N.core_radius_pos y hy
    core_radius_eq := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, f.symm_apply_apply]
      rw [← hball, hsup]
      exact N.core_radius_eq y hy
    core_ball_subset := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, f.symm_apply_apply]
      rw [hclosure]
      exact image_mono (N.core_ball_subset y hy)
    core_ball_compact := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, f.symm_apply_apply]
      rw [hclosure]
      exact (N.core_ball_compact y hy).image f.continuous
    core_ball_volume_lower := by
      obtain ⟨b, hb, hbound⟩ := N.core_ball_volume_lower
      refine ⟨b, hb, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, f.symm_apply_apply]
      rw [← hball, hvolume]
      exact hbound y hy
    gradient_bound := by
      obtain ⟨b, hb, hbound⟩ := N.gradient_bound
      refine ⟨b, hb, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [M34.metricIsometry_scalarGradient f hf N.connection D, hscalar]
      exact hbound x hx
    laplacian_bound := by
      obtain ⟨b, hb, hbound⟩ := N.laplacian_bound
      refine ⟨b, hb, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [M34.metricIsometry_scalarEvolution f hf N.connection D, hscalar]
      exact hbound x hx
  }
  exact ⟨H, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.CapCertificate
