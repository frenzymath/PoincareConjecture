import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Proofs.M28.Generalized.CylinderComparisonCongruence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28



theorem slice_pullback_eq_of_identity (F : GeneralizedRicciFlowData.{u})
    {t t' : ℝ} (ht : t' = t)
    {U : Set (F.slice t).carrier} (hU : IsOpen U)
    (f : (F.slice t).carrier → (F.slice t').carrier)
    (hf : ∀ x ∈ U, (⟨t', f x⟩ : F.point) = ⟨t, x⟩)
    {x : (F.slice t).carrier} (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    (F.metric t').inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
      (mfderiv (𝓡 3) (𝓡 3) f x w) = (F.metric t).inner x v w := by
  subst t'
  have hid : EqOn f id U := fun y hy => eq_of_heq (Sigma.mk.inj_iff.mp (hf y hy)).2
  have heq : f =ᶠ[𝓝 x] id := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hid
  rw [heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)]
  simp only [mfderiv_id]
  change (F.metric t).inner (f x) v w = (F.metric t).inner x v w
  exact congrArg (fun y => (F.metric t).inner y v w) (hid hx)




theorem strongNeck_top_tensor_eq {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    generalizedCylinderPullback N.time_cylinder N.coordinate_map 0 z v w =
      N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric t) N.coordinate_map z v w := by
  have hzero : 0 ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hzN : N.coordinate_map z ∈ N.carrier := by
    have heq := N.coordinate_map_eq (z.1, ⟨z.2, hz⟩)
    exact heq ▸ (N.coordinate (z.1, ⟨z.2, hz⟩)).property
  simp only [generalizedCylinderPullback, dif_pos hzero,
    GeneralizedFlowCylinder.pullbackInner, roundCylinderPullback]
  congr 1
  exact slice_pullback_eq_of_identity F (by simp) N.carrier_open
    (N.time_cylinder.forward 0 hzero) (N.cylinder_identity hzero) hzN _ _



theorem strongNeck_top_comparison {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    NeckMetricJetComparison (F.metric t) epsilon N.scale N.coordinate_map := by
  have hzero : 0 ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := N.metric_comparison
  refine ⟨cylinderClose_of_eqOn_strip ⟨hsmooth 0 hzero, bound, hbound,
    hjet 0 hzero⟩ (strongNeck_top_tensor_eq N)⟩




noncomputable def strongNeck_top {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) (hepsilon : epsilon < 1 / 2) :
    EpsilonNeck (F.metric t) where
  epsilon := epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := hepsilon
  scale := N.scale
  scale_pos := N.scale_pos
  center := N.center
  connection := F.connection t
  scalar_center_pos := N.scalar_center_pos
  scale_eq_scalar := N.scale_scalar
  carrier := N.carrier
  carrier_open := N.carrier_open
  coordinate := N.coordinate
  coordinate_map := N.coordinate_map
  coordinate_map_eq := N.coordinate_map_eq
  coordinate_map_smooth := N.coordinate_map_smooth
  coordinate_inverse := N.coordinate_inverse
  coordinate_inverse_mem := fun x hx => ⟨mem_univ _, N.coordinate_inverse_mem x hx⟩
  coordinate_inverse_left := N.coordinate_inverse_left
  coordinate_inverse_right := by
    intro x hx
    apply Subtype.ext
    exact (N.coordinate_map_eq _).trans (N.coordinate_inverse_right x hx)
  coordinate_inverse_smooth := N.coordinate_inverse_smooth
  central_sphere := N.central_sphere
  central_sphere_eq := N.central_sphere_eq
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := N.central_sphere_subset
  metric_comparison := strongNeck_top_comparison N

end PoincareConjecture.M28
