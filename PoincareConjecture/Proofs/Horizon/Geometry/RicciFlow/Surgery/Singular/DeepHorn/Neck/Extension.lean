import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Cylinders.CylinderSource
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.RoundCylinderCongruence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem GeneralizedFlowCylinder.time_mem_of_nonempty_source
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}
    (d : GeneralizedFlowCylinder F C a q J U) (hC : Nonempty C.carrier)
    (s : ℝ) (hs : s ∈ J) : a + s / q ∈ F.interval :=
  (F.slice_nonempty_iff _).mp (hC.map (d.forward s hs))

namespace GeneralizedFlowExtension

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ} (E : GeneralizedFlowExtension F T)


noncomputable def oldSliceDiffeomorph (t : ℝ) (ht : t ∈ F.interval) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t).carrier (E.extended.slice t).carrier ∞ where
  toFun := E.forward t ht
  invFun := E.inverse t ht
  left_inv := E.left_inverse t ht
  right_inv := E.right_inverse t ht
  contMDiff_toFun := E.forward_smooth t ht
  contMDiff_invFun := E.inverse_smooth t ht

variable {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}


noncomputable def pushCylinder (d : GeneralizedFlowCylinder F C a q J U)
    (hC : Nonempty C.carrier) : GeneralizedFlowCylinder E.extended C a q J U := by
  let f (s : ℝ) (hs : s ∈ J) := E.oldSliceDiffeomorph (a + s / q) (d.time_mem_of_nonempty_source hC s hs)
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => f s hs ∘ d.forward s hs
    inverse := fun s hs => d.inverse s hs ∘ (f s hs).symm
    forward_smooth := fun s hs => (f s hs).contMDiff.comp_contMDiffOn (d.forward_smooth s hs)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := ?_
    vertical_compatibility := ?_ }
  · intro s hs
    apply (d.inverse_smooth s hs).comp (f s hs).symm.contMDiff.contMDiffOn
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · intro s hs x hx
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using d.left_inverse s hs hx
  · intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [Diffeomorph.symm_apply_apply, d.left_inverse s hs hx]
  · have heq : (fun p : J × U =>
        (⟨a + p.1.1 / q, f p.1.1 p.1.2 (d.forward p.1.1 p.1.2 p.2.1)⟩ : E.extended.point)) =
        E.spacetime_forward ∘ (fun p : J × U =>
          (⟨a + p.1.1 / q, d.forward p.1.1 p.1.2 p.2.1⟩ : F.point)) := by
      funext p
      exact (E.spacetime_slices _ (d.time_mem_of_nonempty_source hC p.1.1 p.1.2) _).symm
    change Topology.IsEmbedding (fun p : J × U =>
      (⟨a + p.1.1 / q, f p.1.1 p.1.2 (d.forward p.1.1 p.1.2 p.2.1)⟩ : E.extended.point))
    rw [heq]
    exact E.spacetime_openEmbedding.isEmbedding.comp d.embedding
  · intro s hs x hx
    obtain ⟨b, y, r, hr, hworld⟩ := d.vertical_compatibility s hs x hx
    obtain ⟨hb, hby⟩ := hworld s hs (by simpa using hr)
    obtain ⟨c, z, r', hr', hworld'⟩ := E.vertical_compatibility b (a + s / q) hb y
    refine ⟨c, z, min r (r' * q), lt_min hr (mul_pos hr' d.scale_pos), ?_⟩
    intro s' hs' hdist
    obtain ⟨hb', hby'⟩ := hworld s' hs' (hdist.trans_le (min_le_left _ _))
    have hphysical : |(a + s' / q) - (a + s / q)| < r' := by
      rw [show (a + s' / q) - (a + s / q) = (s' - s) / q by ring,
        abs_div, abs_of_pos d.scale_pos]
      exact (div_lt_iff₀ d.scale_pos).mpr (hdist.trans_le (min_le_right _ _))
    obtain ⟨hc, hcz⟩ := hworld' (a + s' / q) hb' hphysical
    refine ⟨hc, ?_⟩
    rw [E.spacetime_slices _ (d.time_mem_of_nonempty_source hC s' hs') _] at hcz
    change E.forward (a + s' / q) _ (d.forward s' hs' x) = _
    rw [hby']
    exact eq_of_heq (Sigma.mk.inj hcz).2

theorem pushCylinder_pointMap (d : GeneralizedFlowCylinder F C a q J U)
    (hC : Nonempty C.carrier) (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (E.pushCylinder d hC).pointMap s hs x = E.spacetime_forward (d.pointMap s hs x) :=
  (E.spacetime_slices _ (d.time_mem_of_nonempty_source hC s hs) _).symm

theorem pushCylinder_pullbackInner (d : GeneralizedFlowCylinder F C a q J U)
    (hC : Nonempty C.carrier) (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (E.pushCylinder d hC).pullbackInner s hs x v w = d.pullbackInner s hs x v w := by
  let f := E.oldSliceDiffeomorph (a + s / q) (d.time_mem_of_nonempty_source hC s hs)
  have hd := ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hf := f.contMDiff.mdifferentiable (by simp) (d.forward s hs x)
  change q * (E.extended.metric (a + s / q)).inner (f (d.forward s hs x))
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ d.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ d.forward s hs) x w) = _
  rw [mfderiv_comp x hf hd]
  change q * (E.extended.metric (a + s / q)).inner (E.forward _ _ (d.forward s hs x))
      (mfderiv (𝓡 3) (𝓡 3) (E.forward _ _) (d.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x v))
      (mfderiv (𝓡 3) (𝓡 3) (E.forward _ _) (d.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x w)) = _
  rw [E.metric_pullback]
  rfl


noncomputable def strongNeck (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) : GeneralizedStrongNeck E.extended t epsilon := by
  let f := E.oldSliceDiffeomorph t ht
  let V := f.symm ⁻¹' N.carrier
  let coordinate : RoundCylinderSpace → (E.extended.slice t).carrier :=
    f ∘ N.coordinate_map
  let inverse := N.coordinate_inverse ∘ f.symm
  let fV : V ≃ₜ N.carrier := f.symm.toHomeomorph.sets rfl
  let d := E.pushCylinder N.time_cylinder ⟨N.center⟩
  let c := d.rebaseSource f.symm
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
        E.pushCylinder_pointMap N.time_cylinder ⟨N.center⟩ 0 h (f.symm x)
      _ = E.spacetime_forward (⟨t, f.symm x⟩ : F.point) := by
        rw [N.cylinder_identity h (f.symm x) hx]
      _ = (⟨t, E.forward t ht (f.symm x)⟩ : E.extended.point) := E.spacetime_slices t ht _
      _ = (⟨t, x⟩ : E.extended.point) := by
        change (⟨t, f (f.symm x)⟩ : E.extended.point) = _
        rw [f.apply_symm_apply]
  have hcomparison : RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback c coordinate) := by
    apply RoundCylinderFamilyClose.congr
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
    rw [d.rebaseSource_pullbackInner f.symm N.carrier_open s hs (coordinate z) hmem,
      hv v, hv w]
    change d.pullbackInner s hs (f.symm (f (N.coordinate_map z))) _ _ = _
    rw [f.symm_apply_apply]
    exact E.pushCylinder_pullbackInner N.time_cylinder ⟨N.center⟩ N.carrier_open
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
        exact ⟨z, hz, by dsimp only [coordinate, Function.comp_apply]; rw [hzx, f.apply_symm_apply]⟩
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

@[simp] theorem strongNeck_center (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    (E.strongNeck t ht N).center = E.forward t ht N.center := rfl

@[simp] theorem strongNeck_scale (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) : (E.strongNeck t ht N).scale = N.scale := rfl

theorem strongNeck_carrier (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    (E.strongNeck t ht N).carrier = E.forward t ht '' N.carrier := by
  ext x
  change (E.inverse t ht x ∈ N.carrier) ↔ x ∈ E.forward t ht '' N.carrier
  constructor
  · intro hx
    exact ⟨E.inverse t ht x, hx, E.right_inverse t ht x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [E.left_inverse t ht y] using hy

theorem strongNeck_central_sphere (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) :
    (E.strongNeck t ht N).central_sphere = E.forward t ht '' N.central_sphere := by
  ext x
  change (E.inverse t ht x ∈ N.central_sphere) ↔ x ∈ E.forward t ht '' N.central_sphere
  constructor
  · intro hx
    exact ⟨E.inverse t ht x, hx, E.right_inverse t ht x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [E.left_inverse t ht y] using hy

theorem strongNeck_pointMap (t : ℝ) (ht : t ∈ F.interval) {epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (x : (E.extended.slice t).carrier) :
    (E.strongNeck t ht N).time_cylinder.pointMap s hs x =
      E.spacetime_forward (N.time_cylinder.pointMap s hs (E.inverse t ht x)) :=
  E.pushCylinder_pointMap N.time_cylinder ⟨N.center⟩ s hs (E.inverse t ht x)

end GeneralizedFlowExtension

end PoincareConjecture
