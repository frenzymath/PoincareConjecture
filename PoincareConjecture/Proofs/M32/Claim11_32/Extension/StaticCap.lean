import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StaticNeck
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StaticTopology













set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M32

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
  {e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞}



noncomputable def pullbackCapCertificate (K : CapCertificate h)
    (he : MetricHomothety g h e 1) (Hcal : MetricHomothetyCalculus g h e 1)
    (D : LeviCivitaData g) : CapCertificate g where
  epsilon := K.epsilon
  epsilon_pos := K.epsilon_pos
  epsilon_le_threshold := K.epsilon_le_threshold
  cap_constant := K.cap_constant
  cap_constant_pos := K.cap_constant_pos
  carrier := e ⁻¹' K.carrier
  carrier_open := K.carrier_open.preimage e.continuous
  closed_core := e ⁻¹' K.closed_core
  closed_core_compact := e.toHomeomorph.isCompact_preimage.mpr K.closed_core_compact
  core := e ⁻¹' K.core
  core_nonempty := by
    obtain ⟨x, hx⟩ := K.core_nonempty
    exact ⟨e.symm x, by simpa using hx⟩
  core_eq_interior_closed_core := by
    rw [K.core_eq_interior_closed_core]
    exact e.toHomeomorph.preimage_interior _
  puncture := K.puncture
  model_kind := K.model_kind
  model_equivalence := pullbackCapModelEquivalence e K.model_equivalence
  connection := D
  end_neck := pullbackEpsilonNeck K.end_neck he Hcal D
  end_neck_epsilon := K.end_neck_epsilon
  end_neck_subset := fun _ hx => K.end_neck_subset hx
  end_neck_connection := rfl
  closed_core_eq_complement_end := by
    change e ⁻¹' K.closed_core = e ⁻¹' K.carrier \ e ⁻¹' K.end_neck.carrier
    rw [K.closed_core_eq_complement_end, preimage_sdiff]
  boundary_sphere := e ⁻¹' K.boundary_sphere
  boundary_neck := pullbackEpsilonNeck K.boundary_neck he Hcal D
  boundary_neck_epsilon := K.boundary_neck_epsilon
  boundary_neck_subset := fun _ hx => K.boundary_neck_subset hx
  boundary_neck_connection := rfl
  boundary_eq_neck_sphere := congrArg (fun U => e ⁻¹' U) K.boundary_eq_neck_sphere
  boundary_eq_end_frontier := by
    change e ⁻¹' K.boundary_sphere = e ⁻¹' K.carrier ∩ frontier (e ⁻¹' K.end_neck.carrier)
    rw [K.boundary_eq_end_frontier, preimage_inter]
    erw [e.toHomeomorph.preimage_frontier]
    rfl
  boundary_subset_negative_end_closure := by
    rw [pullbackEpsilonNeck_region]
    erw [← e.toHomeomorph.preimage_closure]
    exact preimage_mono K.boundary_subset_negative_end_closure
  boundary_subset := fun _ hx => K.boundary_subset hx
  core_frontier_eq_boundary := by
    erw [← e.toHomeomorph.preimage_frontier]
    rw [K.core_frontier_eq_boundary]
    rfl
  boundary_local_defining_function := by
    intro x hx
    obtain ⟨U, φ, hU, hxU, hUK, hcore, hzero, hsmooth, d, hd, hderiv⟩ :=
      K.boundary_local_defining_function (e x) hx
    let L := e.mfderivToContinuousLinearEquiv (by simp) x
    refine ⟨e ⁻¹' U, φ ∘ e, hU.preimage e.continuous, hxU, fun _ hy => hUK hy,
      fun y hy => hcore (e y) hy, hzero,
      hsmooth.comp e.contMDiff.contMDiffOn (fun _ hy => hy), L.symm d, ?_, ?_⟩
    · intro hz
      apply hd
      have hi := congrArg L hz
      simpa only [L.apply_symm_apply, map_zero] using hi
    · have hi := mvfderiv_comp_apply x
        ((hsmooth.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiable (by simp) _) (L.symm d)
      change mvfderiv (𝓡 3) (φ ∘ e) x (L.symm d) =
        mvfderiv (𝓡 3) φ (e x) (L (L.symm d)) at hi
      rw [L.apply_symm_apply] at hi
      exact hi ▸ hderiv
  scalar_pos := by
    intro x hx
    rw [unitHomothety_scalar_eq Hcal D K.connection]
    exact K.scalar_pos (e x) hx
  intrinsic_diameter_bound := by
    rw [unitHomothety_intrinsicDiameter_eq Hcal, unitHomothety_scalarSup_eq Hcal D K.connection]
    exact K.intrinsic_diameter_bound
  scalar_ratio := by
    obtain ⟨b, hb, hbound⟩ := K.scalar_ratio
    refine ⟨b, hb, fun x hx y hy => ?_⟩
    rw [unitHomothety_scalar_eq Hcal D K.connection, unitHomothety_scalar_eq Hcal D K.connection]
    exact hbound (e x) hx (e y) hy
  volume_bound := by
    rw [unitHomothety_volume_eq Hcal, unitHomothety_scalarSup_eq Hcal D K.connection]
    exact K.volume_bound
  core_radius := K.core_radius ∘ e
  core_radius_pos := fun y hy => K.core_radius_pos (e y) hy
  core_radius_eq := by
    intro y hy
    change scalarCurvatureSupOn g D (g.ball y (K.core_radius (e y))) = _
    rw [unitHomothety_ball_eq Hcal, unitHomothety_scalarSup_eq Hcal D K.connection]
    exact K.core_radius_eq (e y) hy
  core_ball_subset := by
    intro y hy
    change closure (g.ball y (K.core_radius (e y))) ⊆ e ⁻¹' K.carrier
    rw [unitHomothety_ball_eq Hcal]
    erw [← e.toHomeomorph.preimage_closure]
    exact preimage_mono (K.core_ball_subset (e y) hy)
  core_ball_compact := by
    intro y hy
    change IsCompact (closure (g.ball y (K.core_radius (e y))))
    rw [unitHomothety_ball_eq Hcal]
    erw [← e.toHomeomorph.preimage_closure]
    exact e.toHomeomorph.isCompact_preimage.mpr (K.core_ball_compact (e y) hy)
  core_ball_volume_lower := by
    obtain ⟨b, hb, hbound⟩ := K.core_ball_volume_lower
    refine ⟨b, hb, fun y hy => ?_⟩
    change ENNReal.ofReal (b * K.core_radius (e y) ^ 3) ≤
      calibratedMetricVolume g (g.ball y (K.core_radius (e y)))
    rw [unitHomothety_ball_eq Hcal, unitHomothety_volume_eq Hcal]
    exact hbound (e y) hy
  gradient_bound := by
    obtain ⟨b, hb, hbound⟩ := K.gradient_bound
    refine ⟨b, hb, fun x hx => ?_⟩
    rw [unitHomothety_scalarGradient_eq Hcal he D K.connection,
      unitHomothety_scalar_eq Hcal D K.connection]
    exact hbound (e x) hx
  laplacian_bound := by
    obtain ⟨b, hb, hbound⟩ := K.laplacian_bound
    refine ⟨b, hb, fun x hx => ?_⟩
    rw [unitHomothety_scalarEvolution_eq Hcal he D K.connection,
      unitHomothety_scalar_eq Hcal D K.connection]
    exact hbound (e x) hx

end PoincareConjecture.M32
