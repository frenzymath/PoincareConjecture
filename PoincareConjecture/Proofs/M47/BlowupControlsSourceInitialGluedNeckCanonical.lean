import PoincareConjecture.Definitions.M45NeckGluing
import PoincareConjecture.Definitions.Ch15.SurgeryFlow










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

theorem roundCylinderFamilyClose_congr {epsilon : ℝ} {I : Set ℝ}
    {B B' : ℝ → RoundCylinderTwoTensor} (h : RoundCylinderFamilyClose epsilon I B)
    (heq : ∀ u ∈ I, B' u = B u) : RoundCylinderFamilyClose epsilon I B' := by
  obtain ⟨hsmooth, bound, hbound, herror⟩ := h
  refine ⟨fun u hu => ?_, bound, hbound, fun u hu z hz => ?_⟩
  · rw [heq u hu]
    exact hsmooth u hu
  · rw [heq u hu]
    exact herror u hu z hz



theorem surgeryCanonicalControl_of_close_pullback {F : SurgeryFlowData.{u}}
    {t epsilon C : ℝ} (neck : EpsilonNeck (F.metric t)) (heps : neck.epsilon = epsilon)
    (hconn : neck.connection = F.connection t)
    (cyl : SurgeryFlowCylinder F (F.slice t) t (neck.scale⁻¹ ^ 2)
      (Ioc (-1 : ℝ) 0) neck.carrier)
    (hterm : ∀ h x, x ∈ neck.carrier → HEq (cyl.forward 0 h x) x)
    (T : ℝ → RoundCylinderTwoTensor)
    (hT : RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0) T)
    (hpull : ∀ u ∈ Ioc (-1 : ℝ) 0,
      surgeryCylinderPullback cyl neck.coordinate_map u = T u) :
    SurgeryCanonicalControl F t neck.center epsilon C :=
  SurgeryCanonicalControl.neck
    ⟨neck, heps, hconn, cyl, hterm, roundCylinderFamilyClose_congr hT hpull⟩ rfl




theorem surgeryCanonicalControl_of_neck_gluing {epsilon beta : ℝ}
    (hglue : M45NeckGluingProperty.{u} epsilon beta)
    (I : M45NeckGluingInput.{u} epsilon beta)
    {F : SurgeryFlowData.{u}} {t C : ℝ}
    (neck : EpsilonNeck (F.metric t)) (heps : neck.epsilon = epsilon)
    (hconn : neck.connection = F.connection t)
    (cyl : SurgeryFlowCylinder F (F.slice t) t (neck.scale⁻¹ ^ 2)
      (Ioc (-1 : ℝ) 0) neck.carrier)
    (hterm : ∀ h x, x ∈ neck.carrier → HEq (cyl.forward 0 h x) x)
    (hpull : ∀ u ∈ Ioc (-1 : ℝ) 0,
      surgeryCylinderPullback cyl neck.coordinate_map u =
        I.piecewiseTensor I.recent_patch.coordinate u) :
    SurgeryCanonicalControl F t neck.center epsilon C := by
  obtain ⟨G⟩ := hglue I
  have hclose := G.comparison
  rw [G.coordinate_eq] at hclose
  exact surgeryCanonicalControl_of_close_pullback neck heps hconn cyl hterm
    _ hclose hpull

end PoincareConjecture.M47
