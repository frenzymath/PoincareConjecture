import PoincareConjecture.Definitions.M33RegularHistory

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryFlowCylinder

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J J' : Set ℝ} {U U' : Set C.carrier}
  (e : SurgeryFlowCylinder F C a q J U)
  (hJ : J' ⊆ J) (hconnected : J'.OrdConnected) (hU : U' ⊆ U)

noncomputable def restrict : SurgeryFlowCylinder F C a q J' U' where
  scale_pos := e.scale_pos
  interval_connected := hconnected
  time_subset := (image_mono hJ).trans e.time_subset
  forward := fun s hs => e.forward s (hJ hs)
  inverse := fun s hs => e.inverse s (hJ hs)
  forward_smooth := fun s hs => (e.forward_smooth s (hJ hs)).mono hU
  inverse_smooth := fun s hs => (e.inverse_smooth s (hJ hs)).mono (image_mono hU)
  left_inverse := fun s hs x hx => e.left_inverse s (hJ hs) (hU hx)
  right_inverse := fun s hs x hx => e.right_inverse s (hJ hs) (image_mono hU hx)
  slab_compatibility := fun a b hab ht hs s hsm t htm hs' ht' x hx =>
    e.slab_compatibility a b hab ht hs s (hJ hsm) t (hJ htm) hs' ht' x (hU hx)
  retained_at_surgery := by
    intro s hs hT _ hearlier
    apply (image_mono hU).trans
    apply e.retained_at_surgery s (hJ hs) hT
    obtain ⟨s', hs', hlt⟩ := hearlier
    exact ⟨s', hJ hs', hlt⟩
  pre_retained_at_surgery := fun s hs hT _ t ht ht' x hx =>
    e.pre_retained_at_surgery s (hJ hs) hT t (hJ ht) ht' x (hU hx)
  surgery_compatibility := fun s hs hT _ t ht ht' x hx =>
    e.surgery_compatibility s (hJ hs) hT t (hJ ht) ht' x (hU hx)

theorem restrict_forward (s : ℝ) (hs : s ∈ J') (x : C.carrier) :
    (e.restrict hJ hconnected hU).forward s hs x = e.forward s (hJ hs) x := rfl

end PoincareConjecture.SurgeryFlowCylinder
