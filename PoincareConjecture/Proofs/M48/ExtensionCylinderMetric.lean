import PoincareConjecture.Proofs.M48.ExtensionCylinder
import PoincareConjecture.Proofs.M48.SurgeryCylinderSource









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryFlowExtension

variable {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}

theorem pushCylinder_pullbackInner (d : SurgeryFlowCylinder F C a q J U)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (E.pushCylinder d).pullbackInner s hs x v w = d.pullbackInner s hs x v w := by
  let f := E.identify (a + s / q) (d.time_subset ⟨s, hs, rfl⟩)
  have hd := ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hf := f.contMDiff.mdifferentiable (by simp) (d.forward s hs x)
  change q * (E.extended.metric (a + s / q)).inner (f (d.forward s hs x))
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ d.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ d.forward s hs) x w) = _
  rw [mfderiv_comp x hf hd]
  change q * (E.extended.metric (a + s / q)).inner (f (d.forward s hs x))
      (mfderiv (𝓡 3) (𝓡 3) f (d.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x v))
      (mfderiv (𝓡 3) (𝓡 3) f (d.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x w)) = _
  rw [E.metric_pullback]
  rfl

theorem pullCylinder_pullbackInner
    (d : SurgeryFlowCylinder E.extended C a q J U)
    (htime : ∀ s ∈ J, a + s / q ∈ F.time_domain)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (E.pullCylinder d htime).pullbackInner s hs x v w = d.pullbackInner s hs x v w := by
  have h := E.pushCylinder_pullbackInner (E.pullCylinder d htime) hU s hs x hx v w
  have hmap : (E.pushCylinder (E.pullCylinder d htime)).forward s hs = d.forward s hs := by
    funext y
    simp only [pushCylinder_forward, pullCylinder_forward, Diffeomorph.apply_symm_apply]
  unfold SurgeryFlowCylinder.pullbackInner at h ⊢
  rw [hmap] at h
  exact h.symm

end PoincareConjecture.SurgeryFlowExtension
