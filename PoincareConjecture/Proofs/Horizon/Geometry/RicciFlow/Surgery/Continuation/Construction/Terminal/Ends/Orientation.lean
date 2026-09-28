import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.RoundCylinderCongruence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace RoundCylinderReflection

theorem familyClose_pullback {epsilon : ℝ} {J : Set ℝ}
    (B : ℝ → RoundCylinderTwoTensor)
    (hB : ∀ s ∈ J, ∀ (z : RoundCylinderSpace) (a b : ℝ) (v w : RoundCylinderTangent z),
      B s z (a • v) (b • w) = a * b * B s z v w)
    (h : RoundCylinderFamilyClose epsilon J B) :
    RoundCylinderFamilyClose epsilon J (fun s => pullback (B s)) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := h
  refine ⟨fun s hs => smoothOn_pullback (B s) (hB s hs) (hsmooth s hs), bound, hbound, ?_⟩
  intro s hs z hz
  rw [jetErrorSquared_pullback (B s) (hB s hs)]
  exact hjet s hs (space z) (neg_mem_interval hz)

end RoundCylinderReflection

namespace GeneralizedStrongNeck

open RoundCylinderReflection

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (N : GeneralizedStrongNeck F t epsilon)

theorem reversed_metric_comparison :
    RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback N.time_cylinder (N.coordinate_map ∘ space)) := by
  let B := generalizedCylinderPullback N.time_cylinder N.coordinate_map
  have hB : ∀ s ∈ Ioc (-1 : ℝ) 0,
      ∀ (z : RoundCylinderSpace) (a b : ℝ) (v w : RoundCylinderTangent z),
        B s z (a • v) (b • w) = a * b * B s z v w := by
    intro s hs z a b v w
    simp only [B, generalizedCylinderPullback, dif_pos hs,
      GeneralizedFlowCylinder.pullbackInner, map_smul, smul_apply, smul_eq_mul]
    ring
  apply RoundCylinderFamilyClose.congr
    (B' := fun s => pullback (B s)) ?_ (familyClose_pullback B hB N.metric_comparison)
  intro s hs z hz v w
  have hcoord : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      N.coordinate_map (space z) :=
    (N.coordinate_map_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ _, neg_mem_interval hz⟩)).mdifferentiableAt (by simp)
  have hreflect := contMDiff_space.mdifferentiable (by simp) z
  simp only [B, generalizedCylinderPullback, dif_pos hs, pullback, Function.comp_apply,
    mfderiv_comp z hcoord hreflect, ContinuousLinearMap.comp_apply, mfderiv_space_apply]

def reversed : GeneralizedStrongNeck F t epsilon :=
  { N with
    coordinate := (domain epsilon).trans N.coordinate
    coordinate_map := N.coordinate_map ∘ space
    coordinate_map_eq := fun z => N.coordinate_map_eq (domain epsilon z)
    coordinate_map_smooth := by
      apply N.coordinate_map_smooth.comp contMDiff_space.contMDiffOn
      intro z hz
      exact ⟨mem_univ _, neg_mem_interval hz.2⟩
    coordinate_inverse := space ∘ N.coordinate_inverse
    coordinate_inverse_mem := fun x hx => neg_mem_interval (N.coordinate_inverse_mem x hx)
    coordinate_inverse_left := by
      intro z
      change space (N.coordinate_inverse (N.coordinate (domain epsilon z))) = _
      rw [N.coordinate_inverse_left]
      simp [space, domain]
    coordinate_inverse_right := by
      intro x hx
      change N.coordinate_map (space (space (N.coordinate_inverse x))) = x
      rw [space_involutive]
      exact N.coordinate_inverse_right x hx
    coordinate_inverse_smooth := contMDiff_space.comp_contMDiffOn N.coordinate_inverse_smooth
    central_sphere_eq := by
      apply N.central_sphere_eq.trans
      apply image_congr
      rintro ⟨q, z⟩ ⟨_, hz⟩
      have hz' : z = 0 := hz
      subst z
      simp [space]
    metric_comparison := N.reversed_metric_comparison }

@[simp] theorem reversed_center : N.reversed.center = N.center := rfl

@[simp] theorem reversed_scale : N.reversed.scale = N.scale := rfl

@[simp] theorem reversed_carrier : N.reversed.carrier = N.carrier := rfl

@[simp] theorem reversed_central_sphere : N.reversed.central_sphere = N.central_sphere := rfl

@[simp] theorem reversed_time_cylinder : N.reversed.time_cylinder = N.time_cylinder := rfl

@[simp] theorem reversed_coordinate_map (z : RoundCylinderSpace) :
    N.reversed.coordinate_map z = N.coordinate_map (z.1, -z.2) := rfl

@[simp] theorem reversed_coordinate_inverse (x : (F.slice t).carrier) :
    N.reversed.coordinate_inverse x = ((N.coordinate_inverse x).1, -(N.coordinate_inverse x).2) := rfl

@[simp] theorem reversed_spatialNeck (hepsilon : epsilon < 1 / 2) :
    N.reversed.spatialNeck hepsilon = (N.spatialNeck hepsilon).reversed := rfl

@[simp] theorem reversed_spatial_region (hepsilon : epsilon < 1 / 2) (a b : ℝ) :
    (N.reversed.spatialNeck hepsilon).region a b = (N.spatialNeck hepsilon).region (-b) (-a) := by
  rw [N.reversed_spatialNeck, EpsilonNeck.reversed_region]

theorem reversed_spatial_negative (hepsilon : epsilon < 1 / 2) :
    (N.reversed.spatialNeck hepsilon).region (-epsilon⁻¹) 0 =
      (N.spatialNeck hepsilon).region 0 epsilon⁻¹ := by
  simp only [N.reversed_spatial_region, neg_zero, neg_neg]

theorem reversed_spatial_positive (hepsilon : epsilon < 1 / 2) :
    (N.reversed.spatialNeck hepsilon).region 0 epsilon⁻¹ =
      (N.spatialNeck hepsilon).region (-epsilon⁻¹) 0 := by
  simp only [N.reversed_spatial_region, neg_zero]

end GeneralizedStrongNeck

namespace HornEndCut

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon delta rho : ℝ}
  {E : GeneralizedFlowExtension F T} {H : StrongHorn E epsilon}
  {N : TerminalStrongNeck E delta} (C : HornEndCut H N rho)

def reversed : HornEndCut H N.reversed rho where
  point := C.point
  point_mem := C.point_mem
  carrier := C.carrier
  component_eq := C.component_eq
  tail_level := C.tail_level
  tail_level_nonneg := C.tail_level_nonneg
  tail_level_lt_one := C.tail_level_lt_one
  contains_tail := C.contains_tail
  escapes_compact := C.escapes_compact
  disjoint_low_curvature := C.disjoint_low_curvature

@[simp] theorem reversed_point : C.reversed.point = C.point := rfl

@[simp] theorem reversed_carrier : C.reversed.carrier = C.carrier := rfl

@[simp] theorem reversed_tail_level : C.reversed.tail_level = C.tail_level := rfl

end HornEndCut

end PoincareConjecture
