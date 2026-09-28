import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.Comparison
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.EpsilonNeck

open Proofs.M28.NeckAnalysis

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



noncomputable def restrictCoordinate (N : EpsilonNeck g) {eta : ℝ}
    (h : N.epsilon ≤ eta) :
    NeckDomain eta ≃ₜ N.region (-eta⁻¹) eta⁻¹ where
  toFun z := ⟨N.coordinate_map (z.1, z.2), by
    have hz := cylinderStrip_mono N.epsilon_pos h z.2.property
    refine ⟨N.coordinate_map_mem_of_axial (z.1, z.2) hz, ?_⟩
    simpa only [N.coordinate_inverse_coordinate_map_of_axial (z.1, z.2) hz, Set.mem_Ioo]
      using z.2.property⟩
  invFun x := ((N.coordinate_inverse x.1).1,
    ⟨(N.coordinate_inverse x.1).2, x.2.2⟩)
  left_inv z := by
    have hz := cylinderStrip_mono N.epsilon_pos h z.2.property
    have hi := N.coordinate_inverse_coordinate_map_of_axial (z.1, z.2) hz
    apply Prod.ext
    · exact congrArg (fun p : RoundCylinderSpace => p.1) hi
    · exact Subtype.ext (congrArg (fun p : RoundCylinderSpace => p.2) hi)
  right_inv x := Subtype.ext (N.coordinate_map_coordinate_inverse x.2.1)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply N.coordinate_map_smooth.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    intro z
    exact ⟨mem_univ _, cylinderStrip_mono N.epsilon_pos h z.2.property⟩
  continuous_invFun := by
    have hi : Continuous (fun x : N.region (-eta⁻¹) eta⁻¹ => N.coordinate_inverse x.1) :=
      N.coordinate_inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
        (fun x => x.2.1)
    exact hi.fst.prodMk (hi.snd.subtype_mk _)



noncomputable def restrict_m28 (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) : EpsilonNeck g where
  epsilon := eta
  epsilon_pos := N.epsilon_pos.trans_le h
  epsilon_lt_half := heta
  scale := N.scale
  scale_pos := N.scale_pos
  center := N.center
  connection := N.connection
  scalar_center_pos := N.scalar_center_pos
  scale_eq_scalar := N.scale_eq_scalar
  carrier := N.region (-eta⁻¹) eta⁻¹
  carrier_open := N.region_open _ _
  coordinate := N.restrictCoordinate h
  coordinate_map := N.coordinate_map
  coordinate_map_eq := fun _ => rfl
  coordinate_map_smooth := N.coordinate_map_smooth.mono
    (Set.prod_mono_right (cylinderStrip_mono N.epsilon_pos h))
  coordinate_inverse := N.coordinate_inverse
  coordinate_inverse_mem := fun _ hx => ⟨mem_univ _, hx.2⟩
  coordinate_inverse_left := fun z =>
    N.coordinate_inverse_coordinate_map_of_axial (z.1, z.2)
      (cylinderStrip_mono N.epsilon_pos h z.2.property)
  coordinate_inverse_right := fun x hx =>
    Subtype.ext (N.coordinate_map_coordinate_inverse hx.1)
  coordinate_inverse_smooth := N.coordinate_inverse_smooth.mono (fun _ hx => hx.1)
  central_sphere := N.central_sphere
  central_sphere_eq := N.central_sphere_eq
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := by
    rw [N.central_sphere_eq]
    rintro x ⟨z, hz, rfl⟩
    have heta_pos := N.epsilon_pos.trans_le h
    have hz0 : z.2 = 0 := hz.2
    have hzold : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hz0]
      exact ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
    refine ⟨N.coordinate_map_mem_of_axial z hzold, ?_⟩
    rw [N.coordinate_inverse_coordinate_map_of_axial z hzold, hz0]
    exact ⟨neg_neg_of_pos (inv_pos.mpr heta_pos), inv_pos.mpr heta_pos⟩
  metric_comparison := ⟨N.metric_comparison.close.mono_epsilon_m28 N.epsilon_pos h (by norm_num)⟩

@[simp] theorem restrict_epsilon (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) : (N.restrict_m28 eta h heta).epsilon = eta := rfl

@[simp] theorem restrict_center (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) :
    (N.restrict_m28 eta h heta).center = N.center := rfl

@[simp] theorem restrict_scale (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) :
    (N.restrict_m28 eta h heta).scale = N.scale := rfl

@[simp] theorem restrict_connection (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) :
    (N.restrict_m28 eta h heta).connection = N.connection := rfl

@[simp] theorem restrict_carrier (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) :
    (N.restrict_m28 eta h heta).carrier = N.region (-eta⁻¹) eta⁻¹ := rfl

@[simp] theorem restrict_central_sphere (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) :
    (N.restrict_m28 eta h heta).central_sphere = N.central_sphere := rfl

@[simp] theorem restrict_coordinate_map (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) :
    (N.restrict_m28 eta h heta).coordinate_map = N.coordinate_map := rfl

@[simp] theorem restrict_coordinate_inverse (N : EpsilonNeck g) (eta : ℝ)
    (h : N.epsilon ≤ eta) (heta : eta < 1 / 2) :
    (N.restrict_m28 eta h heta).coordinate_inverse = N.coordinate_inverse := rfl

end PoincareConjecture.EpsilonNeck
