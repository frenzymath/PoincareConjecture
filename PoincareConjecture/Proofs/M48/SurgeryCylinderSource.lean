import PoincareConjecture.Definitions.Ch15.SurgeryFlow










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryFlowCylinder

variable {F : SurgeryFlowData.{u}} {C C' : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (d : SurgeryFlowCylinder F C a q J U)
  (f : Diffeomorph (𝓡 3) (𝓡 3) C'.carrier C.carrier ∞)

noncomputable def rebaseSource : SurgeryFlowCylinder F C' a q J (f ⁻¹' U) := by
  have hmaps : MapsTo f (f ⁻¹' U) U := fun _ hx => hx
  have himage (s : ℝ) (hs : s ∈ J) :
      (d.forward s hs ∘ f) '' (f ⁻¹' U) ⊆ d.forward s hs '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, hx, rfl⟩
  refine {
    scale_pos := d.scale_pos
    interval_connected := d.interval_connected
    time_subset := d.time_subset
    forward := fun s hs => d.forward s hs ∘ f
    inverse := fun s hs => f.symm ∘ d.inverse s hs
    forward_smooth := fun s hs => (d.forward_smooth s hs).comp f.contMDiff.contMDiffOn hmaps
    inverse_smooth := fun s hs =>
      f.symm.contMDiff.comp_contMDiffOn ((d.inverse_smooth s hs).mono (himage s hs))
    left_inverse := ?_
    right_inverse := ?_
    slab_compatibility := ?_
    retained_at_surgery := ?_
    pre_retained_at_surgery := ?_
    surgery_compatibility := ?_ }
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, f.symm_apply_apply]
  · intro s hs y hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, f.apply_symm_apply]
  · intro l r hlr hJ hfree s hs t ht hs' ht' x hx
    exact d.slab_compatibility l r hlr hJ hfree s hs t ht hs' ht' (f x) hx
  · intro s hs hT _ hearlier
    exact (himage s hs).trans (d.retained_at_surgery s hs hT hearlier)
  · intro s hs hT _ t ht ht' x hx
    exact d.pre_retained_at_surgery s hs hT t ht ht' (f x) hx
  · intro s hs hT _ t ht ht' x hx
    exact d.surgery_compatibility s hs hT t ht ht' (f x) hx

theorem rebaseSource_forward (s : ℝ) (hs : s ∈ J) (x : C'.carrier) :
    (d.rebaseSource f).forward s hs x = d.forward s hs (f x) := rfl

theorem rebaseSource_pullbackInner (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C'.carrier) (hx : f x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (d.rebaseSource f).pullbackInner s hs x v w =
      d.pullbackInner s hs (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  have hd := ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hf := f.contMDiff.mdifferentiable (by simp) x
  dsimp only [pullbackInner, rebaseSource]
  rw [mfderiv_comp x hd hf]
  rfl

end PoincareConjecture.SurgeryFlowCylinder

namespace PoincareConjecture.SurgeryFlowCylinder

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : Set ℝ} {U V : Set C.carrier}


noncomputable def restrictSource (d : SurgeryFlowCylinder F C a q J U) (hVU : V ⊆ U) :
    SurgeryFlowCylinder F C a q J V where
  scale_pos := d.scale_pos
  interval_connected := d.interval_connected
  time_subset := d.time_subset
  forward := d.forward
  inverse := d.inverse
  forward_smooth := fun s hs => (d.forward_smooth s hs).mono hVU
  inverse_smooth := fun s hs => (d.inverse_smooth s hs).mono (image_mono hVU)
  left_inverse := fun s hs => (d.left_inverse s hs).mono hVU
  right_inverse := fun s hs => (d.right_inverse s hs).mono (image_mono hVU)
  slab_compatibility := fun l r hlr hJ hfree s hs t ht hs' ht' x hx =>
    d.slab_compatibility l r hlr hJ hfree s hs t ht hs' ht' x (hVU hx)
  retained_at_surgery := fun s hs hT _ hearlier =>
    (image_mono hVU).trans (d.retained_at_surgery s hs hT hearlier)
  pre_retained_at_surgery := fun s hs hT _ t ht ht' x hx =>
    d.pre_retained_at_surgery s hs hT t ht ht' x (hVU hx)
  surgery_compatibility := fun s hs hT _ t ht ht' x hx =>
    d.surgery_compatibility s hs hT t ht ht' x (hVU hx)

theorem restrictSource_forward (d : SurgeryFlowCylinder F C a q J U) (hVU : V ⊆ U)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (d.restrictSource hVU).forward s hs x = d.forward s hs x := rfl

theorem restrictSource_pullbackInner (d : SurgeryFlowCylinder F C a q J U) (hVU : V ⊆ U)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) (v w : TangentSpace (𝓡 3) x) :
    (d.restrictSource hVU).pullbackInner s hs x v w = d.pullbackInner s hs x v w := rfl

end PoincareConjecture.SurgeryFlowCylinder
