import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.StandardGeometry.CapEndOrientation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.StandardGeometry.CapDefiningFunction
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.StandardGeometry.NeckReflection
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.StandardGeometry.CapUniformBounds
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Constants.ProducerEndpoints

/-!
# Standard caps in the common intrinsic certificate

Morgan--Tian Definition 9.72 and Remark 9.73, pp. 230-231, and Section
15.1.1, p. 354. The selected carrier, closed core, and connection are
unchanged. Exact end reversal fixes orientation; the added unit supplies
every uniform strict analytic bound.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.StandardCapNeighborhood

open M45

variable {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
  {F : MaximalStandardCapFlow g₀} {t epsilon C : ℝ} {x : StandardCapSpace}

/-- The closed-core frontier is the end frontier relative to the actual
open cap carrier. Definition 9.72(3), p. 230. -/
theorem core_frontier_eq_end (N : StandardCapNeighborhood atlas F t epsilon C x) :
    frontier N.closed_core = N.carrier ∩ frontier N.end_neck.patch.carrier := by
  rw [N.core_compact.isClosed.frontier_eq, N.closed_core_eq]
  simp only [sdiff_eq]
  rw [interior_inter, N.carrier_open.interior_eq, interior_compl,
    N.end_neck.patch.carrier_open.frontier_eq]
  ext y
  simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
  tauto

/-- The supplied Euclidean cap chart is the actual model equivalence.
Definition 9.72(1), p. 230. -/
noncomputable def euclideanModel (N : StandardCapNeighborhood atlas F t epsilon C x)
    (p : RealProjectiveThree) : CapModelEquivalence .euclidean p N.carrier where
  model := StandardCapSpace
  model_topology := inferInstance
  model_charted := inferInstance
  model_manifold := inferInstance
  standard_model := Homeomorph.ulift.symm
  standard_smooth := ⟨Diffeomorph.refl (𝓡 3) StandardCapSpace ∞⟩
  forward := N.ball_inverse
  inverse := N.ball_map
  inverse_mem := fun y => N.ball_map_range ▸ mem_range_self y
  left_inverse := N.ball_map_right_inverse
  right_inverse := N.ball_map_left_inverse
  forward_smooth := N.ball_inverse_smooth
  inverse_smooth := N.ball_map_smooth.contMDiffOn

/-- Refine the raw standard cap without changing its carrier, core, or
connection. Definition 9.72, pp. 230-231, and Section 15.1.1, p. 354. -/
theorem exists_refinement (N : StandardCapNeighborhood atlas F t epsilon C x)
    (hepsilon : epsilon ≤ 1 / 200) : Nonempty (M45StandardCapRefinement N) := by
  classical
  obtain ⟨E, hEepsilon, hEconnection, hEcarrier, hEboundary⟩ :
      ∃ E : EpsilonNeck (F.metric t), E.epsilon = epsilon ∧
        E.connection = F.connection t ∧ E.carrier = N.end_neck.patch.carrier ∧
        frontier N.closed_core ⊆ closure (E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
    rcases N.boundary_end_orientation with h | h
    · exact ⟨N.end_neck.toEpsilonNeck, rfl, rfl, rfl, h⟩
    · refine ⟨reverseNeck N.end_neck.toEpsilonNeck, rfl, rfl, rfl, ?_⟩
      rw [reverseNeck_region]
      simpa only [neg_neg, neg_div] using h
  obtain ⟨radius, hradius, hradiusEq, hball, hcompact, bound, hbound, hvolume⟩ :=
    N.exists_uniform_coreRadii
  let p : RealProjectiveThree := Quotient.mk'
    (Classical.choice (show Nonempty UnitThreeSphere from
      (NormedSpace.sphere_nonempty.mpr (by norm_num : 0 ≤ (1 : ℝ))).coe_sort))
  let cap : CapCertificate (F.metric t) :=
    { epsilon := epsilon
      epsilon_pos := N.epsilon_pos
      epsilon_le_threshold := hepsilon
      cap_constant := C + 1
      cap_constant_pos := by linarith [N.constant_pos]
      carrier := N.carrier
      carrier_open := N.carrier_open
      closed_core := N.closed_core
      closed_core_compact := N.core_compact
      core := interior N.closed_core
      core_nonempty := ⟨x, N.center_in_core⟩
      core_eq_interior_closed_core := rfl
      puncture := p
      model_kind := .euclidean
      model_equivalence := N.euclideanModel p
      connection := F.connection t
      end_neck := E
      end_neck_epsilon := hEepsilon
      end_neck_subset := hEcarrier ▸ N.end_subset
      end_neck_connection := hEconnection
      closed_core_eq_complement_end := by rw [hEcarrier]; exact N.closed_core_eq
      boundary_sphere := frontier N.closed_core
      boundary_neck := N.boundary_neck.toEpsilonNeck
      boundary_neck_epsilon := rfl
      boundary_neck_subset := N.boundary_neck_subset
      boundary_neck_connection := rfl
      boundary_eq_neck_sphere := N.boundary_sphere
      boundary_eq_end_frontier := by rw [hEcarrier]; exact N.core_frontier_eq_end
      boundary_subset_negative_end_closure := hEboundary
      boundary_subset := by
        intro y hy
        apply N.boundary_neck_subset
        apply N.boundary_neck.toEpsilonNeck.central_sphere_subset
        change y ∈ N.boundary_neck.patch.centralSphere
        rwa [← N.boundary_sphere]
      core_frontier_eq_boundary := rfl
      boundary_local_defining_function := fun y hy =>
        neck_boundary_defining_function N.boundary_neck.toEpsilonNeck
          N.core_compact.isClosed ⟨x, N.center_in_core⟩ N.core_ne_univ
          N.boundary_sphere N.boundary_neck_subset hy
      scalar_pos := N.scalar_pos
      intrinsic_diameter_bound := N.intrinsicDiameter_lt_add_one
      scalar_ratio := N.scalarRatio_uniform
      volume_bound := N.volume_lt_add_one
      core_radius := radius
      core_radius_pos := hradius
      core_radius_eq := hradiusEq
      core_ball_subset := hball
      core_ball_compact := hcompact
      core_ball_volume_lower := ⟨bound, hbound, hvolume⟩
      gradient_bound := N.gradient_uniform
      laplacian_bound := N.scalarEvolution_uniform }
  exact ⟨⟨cap, rfl, rfl, rfl, rfl, rfl, rfl, N.center_in_core⟩⟩

end PoincareMT.StandardCapNeighborhood

namespace PoincareMT.M45

/-- The literal cap-refinement producer used in the M45 calibration.
Definition 9.72 and Remark 9.73, pp. 230-231. -/
theorem capRefinementProducer : CapRefinementProducer := by
  intro atlas g₀ F t epsilon C x hepsilon N
  exact N.exists_refinement hepsilon

end PoincareMT.M45
