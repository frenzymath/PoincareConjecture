import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Restriction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareConjecture

namespace StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon delta : ℝ}
  {E : GeneralizedFlowExtension F T}

noncomputable def restrictAccuracy (H : StrongHorn E epsilon)
    (hed : epsilon ≤ delta) : StrongHorn E delta where
  carrier := H.carrier
  coordinate := H.coordinate
  parameterization := H.parameterization
  coordinate_eq := H.coordinate_eq
  collar := H.collar
  collar_pos := H.collar_pos
  parameterization_smooth := H.parameterization_smooth
  parameterization_regular := H.parameterization_regular
  proper := H.proper
  boundary_sphere := H.boundary_sphere
  boundary_sphere_eq := H.boundary_sphere_eq
  boundary_neck := by
    obtain ⟨N, hN⟩ := H.boundary_neck
    exact ⟨N.restrictAccuracy hed, hN⟩
  every_point_neck := by
    intro x hx
    obtain ⟨N, hN⟩ := H.every_point_neck x hx
    exact ⟨N.restrictAccuracy hed, hN⟩

@[simp] theorem restrictAccuracy_carrier (H : StrongHorn E epsilon)
    (hed : epsilon ≤ delta) : (H.restrictAccuracy hed).carrier = H.carrier := rfl

@[simp] theorem restrictAccuracy_boundary_sphere (H : StrongHorn E epsilon)
    (hed : epsilon ≤ delta) :
    (H.restrictAccuracy hed).boundary_sphere = H.boundary_sphere := rfl

@[simp] theorem restrictAccuracy_parameterization (H : StrongHorn E epsilon)
    (hed : epsilon ≤ delta) :
    (H.restrictAccuracy hed).parameterization = H.parameterization := rfl

end StrongHorn

namespace StrongDoubleHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon delta : ℝ}
  {E : GeneralizedFlowExtension F T}

noncomputable def restrictAccuracy (H : StrongDoubleHorn E epsilon)
    (hed : epsilon ≤ delta) : StrongDoubleHorn E delta where
  basepoint := H.basepoint
  carrier := H.carrier
  component_eq := H.component_eq
  coordinate := H.coordinate
  parameterization := H.parameterization
  coordinate_eq := H.coordinate_eq
  parameterization_smooth := H.parameterization_smooth
  parameterization_regular := H.parameterization_regular
  every_point_neck := by
    intro x hx
    obtain ⟨N, hN⟩ := H.every_point_neck x hx
    exact ⟨N.restrictAccuracy hed, hN⟩

@[simp] theorem restrictAccuracy_basepoint (H : StrongDoubleHorn E epsilon)
    (hed : epsilon ≤ delta) : (H.restrictAccuracy hed).basepoint = H.basepoint := rfl

@[simp] theorem restrictAccuracy_carrier (H : StrongDoubleHorn E epsilon)
    (hed : epsilon ≤ delta) : (H.restrictAccuracy hed).carrier = H.carrier := rfl

@[simp] theorem restrictAccuracy_parameterization (H : StrongDoubleHorn E epsilon)
    (hed : epsilon ≤ delta) :
    (H.restrictAccuracy hed).parameterization = H.parameterization := rfl

end StrongDoubleHorn

namespace SingularRoundComponent

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon delta : ℝ}

noncomputable def restrictAccuracy (N : SingularRoundComponent g epsilon)
    (hed : epsilon ≤ delta) : SingularRoundComponent g delta where
  epsilon_pos := N.epsilon_pos.trans_le hed
  basepoint := N.basepoint
  carrier := N.carrier
  component_eq := N.component_eq
  compact := N.compact
  model := N.model
  model_compact := N.model_compact
  model_connected := N.model_connected
  model_metric := N.model_metric
  model_connection := N.model_connection
  model_curvature_one := N.model_curvature_one
  forward := N.forward
  inverse := N.inverse
  forward_image := N.forward_image
  forward_openEmbedding := N.forward_openEmbedding
  forward_smooth := N.forward_smooth
  inverse_smooth := N.inverse_smooth
  left_inverse := N.left_inverse
  right_inverse := N.right_inverse
  scale := N.scale
  scale_pos := N.scale_pos
  metric_comparison := by
    obtain ⟨b, hb, hbound⟩ := N.metric_comparison
    refine ⟨b, hb.trans_le (pow_le_pow_left₀ N.epsilon_pos.le hed 2), ?_⟩
    intro x
    have horder : ⌊delta⁻¹⌋₊ ≤ ⌊epsilon⁻¹⌋₊ :=
      Nat.floor_mono ((inv_le_inv₀ (N.epsilon_pos.trans_le hed) N.epsilon_pos).2 hed)
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.add_le_add_right horder 1))
      (fun _ _ _ => sq_nonneg _))
    exact hbound x

@[simp] theorem restrictAccuracy_basepoint (N : SingularRoundComponent g epsilon)
    (hed : epsilon ≤ delta) : (N.restrictAccuracy hed).basepoint = N.basepoint := rfl

@[simp] theorem restrictAccuracy_carrier (N : SingularRoundComponent g epsilon)
    (hed : epsilon ≤ delta) : (N.restrictAccuracy hed).carrier = N.carrier := rfl

@[simp] theorem restrictAccuracy_scale (N : SingularRoundComponent g epsilon)
    (hed : epsilon ≤ delta) : (N.restrictAccuracy hed).scale = N.scale := rfl

end SingularRoundComponent

end PoincareConjecture
