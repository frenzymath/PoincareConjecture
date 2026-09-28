import PoincareConjecture.Proofs.M32.Claim11_32.Extension.Cylinders
import PoincareConjecture.Proofs.M32.Neck.Spatial

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

theorem roundCylinderFamilyClose_congr_axial {epsilon : ℝ} {J : Set ℝ}
    {B B' : ℝ → RoundCylinderTwoTensor}
    (hB : ∀ s ∈ J, ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B s z v w = B' s z v w)
    (h : RoundCylinderFamilyClose epsilon J B') : RoundCylinderFamilyClose epsilon J B := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := h
  refine ⟨?_, bound, hbound, ?_⟩
  · intro s hs q a b
    apply (hsmooth s hs q a b).congr
    intro p hp
    exact hB s hs _ hp.2 _ _
  · intro s hs z hz
    rw [roundCylinderJetErrorSquared_congr_axial isOpen_Ioo (hB s hs) s _ z hz]
    exact hjet s hs z hz

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ} (E : GeneralizedFlowExtension F T)

noncomputable def extension_strongNeck (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) : GeneralizedStrongNeck E.extended t epsilon := by
  let f := extension_oldSliceDiffeomorph E t ht
  let V := f.symm ⁻¹' N.carrier
  let coordinate : RoundCylinderSpace → (E.extended.slice t).carrier :=
    f ∘ N.coordinate_map
  let inverse := N.coordinate_inverse ∘ f.symm
  let fV : V ≃ₜ N.carrier := f.symm.toHomeomorph.sets rfl
  let d := extension_pushCylinder E N.time_cylinder ⟨N.center⟩
  let c := rebaseCylinderSource d f.symm
  have hcoord (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
      N.coordinate_map z ∈ N.carrier := by
    have h := N.coordinate_map_eq (z.1, ⟨z.2, hz⟩)
    exact h ▸ (N.coordinate (z.1, ⟨z.2, hz⟩)).property
  have hcoord' : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    f.contMDiff.comp_contMDiffOn N.coordinate_map_smooth
  have hscalar : (E.extended.connection t).scalarCurvature (f N.center) =
      (F.connection t).scalarCurvature N.center := E.scalar_pullback t ht N.center
  have hzero : ∀ h x, x ∈ V → c.pointMap 0 h x = (⟨t, x⟩ : E.extended.point) := by
    intro h x hx
    calc
      c.pointMap 0 h x = d.pointMap 0 h (f.symm x) := rfl
      _ = E.spacetime_forward (N.time_cylinder.pointMap 0 h (f.symm x)) :=
        extension_pushCylinder_pointMap E N.time_cylinder ⟨N.center⟩ 0 h (f.symm x)
      _ = E.spacetime_forward (⟨t, f.symm x⟩ : F.point) := by
        rw [N.cylinder_identity h (f.symm x) hx]
      _ = (⟨t, E.forward t ht (f.symm x)⟩ : E.extended.point) := E.spacetime_slices t ht _
      _ = (⟨t, x⟩ : E.extended.point) := by
        change (⟨t, f (f.symm x)⟩ : E.extended.point) = _
        rw [f.apply_symm_apply]
  have hcomparison : RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback c coordinate) := by
    apply roundCylinderFamilyClose_congr_axial
      (B' := generalizedCylinderPullback N.time_cylinder N.coordinate_map) ?_
      N.metric_comparison
    intro s hs z hz v w
    have hmem : f.symm (coordinate z) ∈ N.carrier := by
      simpa only [coordinate, Function.comp_apply, f.symm_apply_apply] using hcoord z hz
    have hdiff := (hcoord'.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
    have hcomp : f.symm ∘ coordinate = N.coordinate_map := by
      funext z
      exact f.symm_apply_apply _
    have hderiv : (mfderiv (𝓡 3) (𝓡 3) f.symm (coordinate z)).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z := by
      rw [← mfderiv_comp z (f.symm.contMDiff.mdifferentiable (by simp) _) hdiff, hcomp]
    have hv (v : RoundCylinderTangent z) :
        mfderiv (𝓡 3) (𝓡 3) f.symm (coordinate z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v :=
      congrArg (fun A => A v) hderiv
    simp only [generalizedCylinderPullback, dif_pos hs]
    rw [rebaseCylinderSource_pullbackInner d f.symm N.carrier_open s hs (coordinate z) hmem,
      hv v, hv w]
    change d.pullbackInner s hs (f.symm (f (N.coordinate_map z))) _ _ = _
    rw [f.symm_apply_apply]
    exact extension_pushCylinder_pullbackInner E N.time_cylinder ⟨N.center⟩ N.carrier_open
      s hs (N.coordinate_map z) (hcoord z hz) _ _
  exact {
    epsilon_pos := N.epsilon_pos
    center := f N.center
    scalar_center_pos := hscalar.symm ▸ N.scalar_center_pos
    scale := N.scale
    scale_pos := N.scale_pos
    scale_scalar := by rw [hscalar]; exact N.scale_scalar
    carrier := V
    carrier_open := N.carrier_open.preimage f.symm.continuous
    coordinate := N.coordinate.trans fV.symm
    coordinate_map := coordinate
    coordinate_map_eq := by
      intro z
      change f (N.coordinate z) = f (N.coordinate_map (z.1, (z.2 : ℝ)))
      rw [N.coordinate_map_eq]
    coordinate_map_smooth := hcoord'
    coordinate_inverse := inverse
    coordinate_inverse_mem := fun x hx => N.coordinate_inverse_mem (f.symm x) hx
    coordinate_inverse_left := by
      intro z
      change N.coordinate_inverse (f.symm (f (N.coordinate z))) = _
      rw [f.symm_apply_apply]
      exact N.coordinate_inverse_left z
    coordinate_inverse_right := by
      intro x hx
      change f (N.coordinate_map (N.coordinate_inverse (f.symm x))) = x
      rw [N.coordinate_inverse_right (f.symm x) hx, f.apply_symm_apply]
    coordinate_inverse_smooth := N.coordinate_inverse_smooth.comp
      f.symm.contMDiff.contMDiffOn (fun _ hx => hx)
    central_sphere := f.symm ⁻¹' N.central_sphere
    central_sphere_eq := by
      ext x
      change (f.symm x ∈ N.central_sphere) ↔ x ∈ coordinate '' (univ ×ˢ {0})
      rw [N.central_sphere_eq]
      constructor
      · rintro ⟨z, hz, hzx⟩
        refine ⟨z, hz, ?_⟩
        dsimp only [coordinate, Function.comp_apply]
        rw [hzx, f.apply_symm_apply]
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, (f.symm_apply_apply _).symm⟩
    center_on_central_sphere := by
      change f.symm (f N.center) ∈ N.central_sphere
      rw [f.symm_apply_apply]
      exact N.center_on_central_sphere
    central_sphere_subset := fun _ hx => N.central_sphere_subset hx
    time_cylinder := c
    cylinder_identity := hzero
    metric_comparison := hcomparison }

@[simp] theorem extension_strongNeck_center (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    (extension_strongNeck E t ht N).center = E.forward t ht N.center := rfl

@[simp] theorem extension_strongNeck_scale (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    (extension_strongNeck E t ht N).scale = N.scale := rfl

theorem extension_strongNeck_carrier (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    (extension_strongNeck E t ht N).carrier = E.forward t ht '' N.carrier := by
  ext x
  change (E.inverse t ht x ∈ N.carrier) ↔ x ∈ E.forward t ht '' N.carrier
  constructor
  · intro hx
    exact ⟨E.inverse t ht x, hx, E.right_inverse t ht x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [E.left_inverse t ht y] using hy

theorem extension_strongNeck_central_sphere (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    (extension_strongNeck E t ht N).central_sphere = E.forward t ht '' N.central_sphere := by
  ext x
  change (E.inverse t ht x ∈ N.central_sphere) ↔ x ∈ E.forward t ht '' N.central_sphere
  constructor
  · intro hx
    exact ⟨E.inverse t ht x, hx, E.right_inverse t ht x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [E.left_inverse t ht y] using hy

theorem extension_strongNeck_pointMap (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (x : (E.extended.slice t).carrier) :
    (extension_strongNeck E t ht N).time_cylinder.pointMap s hs x =
      E.spacetime_forward (N.time_cylinder.pointMap s hs (E.inverse t ht x)) :=
  extension_pushCylinder_pointMap E N.time_cylinder ⟨N.center⟩ s hs (E.inverse t ht x)

end PoincareConjecture.M32
