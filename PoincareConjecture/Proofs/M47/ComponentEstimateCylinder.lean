import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem component_cylinder_image_eq
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (hopen : IsOpen U) (hcompact : IsCompact U) (hconnected : IsConnected U)
    (s : ℝ) (hs : s ∈ I) {x : C.carrier} (hx : x ∈ U) :
    e.forward s hs '' U = connectedComponent (e.forward s hs x) := by
  have hopenImage := (M44.cylinderSliceChart e hopen s hs).open_target
  have hcontinuous := (e.forward_smooth s hs).continuousOn
  have hcompactImage := hcompact.image_of_continuousOn hcontinuous
  have hconnectedImage := hconnected.image (e.forward s hs) hcontinuous
  have hpoint := mem_image_of_mem (e.forward s hs) hx
  exact Subset.antisymm (hconnectedImage.subset_connectedComponent hpoint)
    ((show IsClopen _ from ⟨hcompactImage.isClosed, hopenImage⟩).connectedComponent_subset hpoint)

theorem exists_component_singleton_cylinder
    (F : SurgeryFlowData.{u}) (origin : ℝ) (htime : origin ∈ F.time_domain)
    (U : Set (F.slice origin).carrier) :
    ∃ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc 0 0) U,
      ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x := by
  have hzero (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 0) : s = 0 := le_antisymm hs.2 hs.1
  let chart (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 0) :
      Diffeomorph (𝓡 3) (𝓡 3) (F.slice origin).carrier
        (F.slice (origin + s / 1)).carrier ∞ :=
    Eq.ndrec (motive := fun r => Diffeomorph (𝓡 3) (𝓡 3)
      (F.slice origin).carrier (F.slice r).carrier ∞)
      (Diffeomorph.refl (𝓡 3) (F.slice origin).carrier ∞)
      (by rw [hzero s hs, zero_div, add_zero])
  let e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc 0 0) U := {
    scale_pos := zero_lt_one
    interval_connected := ordConnected_Icc
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      simpa only [hzero s hs, zero_div, add_zero] using htime
    forward := fun s hs => chart s hs
    inverse := fun s hs => (chart s hs).symm
    forward_smooth := fun s hs => (chart s hs).contMDiff.contMDiffOn
    inverse_smooth := fun s hs => (chart s hs).symm.contMDiff.contMDiffOn
    left_inverse := fun s hs x _ => (chart s hs).symm_apply_apply x
    right_inverse := fun s hs x _ => (chart s hs).apply_symm_apply x
    slab_compatibility := by
      intro a b hab hJ hfree s hs t ht hs' ht' x _hx
      have hs0 := hzero s hs
      have ht0 := hzero t ht
      subst s
      subst t
      exact SurgeryRegularSlab.transport_self _ _ _
    retained_at_surgery := by
      intro s hs _hT _ hearlier
      obtain ⟨t, ht, hts⟩ := hearlier
      have hs0 := hzero s hs
      have ht0 := hzero t ht
      exact (by linarith : False).elim
    pre_retained_at_surgery := by
      intro s hs _hT _ t ht ht' _x _hx
      have hs0 := hzero s hs
      have ht0 := hzero t ht
      have hlt := ht'.2
      simp only [hs0, ht0] at hlt
      exact (lt_irrefl _ hlt).elim
    surgery_compatibility := by
      intro s hs _hT _ t ht ht' _x _hx
      have hs0 := hzero s hs
      have ht0 := hzero t ht
      have hlt := ht'.2
      simp only [hs0, ht0] at hlt
      exact (lt_irrefl _ hlt).elim
  }
  refine ⟨e, ?_⟩
  intro hs x _hx
  have hid (b : ℝ) (hb : origin = b) :
      HEq ((Eq.ndrec (motive := fun r => Diffeomorph (𝓡 3) (𝓡 3)
        (F.slice origin).carrier (F.slice r).carrier ∞)
        (Diffeomorph.refl (𝓡 3) (F.slice origin).carrier ∞) hb) x) x := by
    cases hb
    rfl
  exact hid (origin + 0 / 1) _

end PoincareConjecture.M47
