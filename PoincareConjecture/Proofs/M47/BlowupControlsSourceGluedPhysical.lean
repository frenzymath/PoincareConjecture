import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalAssembly
import PoincareConjecture.Definitions.M45NeckGluing

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

open PoincareConjecture.Proofs.M47

theorem neckGluing_family_close {epsilon beta : ℝ}
    (hglue : M45NeckGluingProperty.{u} epsilon beta)
    (I : M45NeckGluingInput.{u} epsilon beta)
    {B : ℝ → RoundCylinderTwoTensor}
    (hpull : ∀ s ∈ Ioc (-1 : ℝ) 0,
      B s = I.piecewiseTensor I.recent_patch.coordinate s) :
    RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0) B := by
  obtain ⟨G⟩ := hglue I
  have hclose := G.comparison
  rw [G.coordinate_eq] at hclose
  obtain ⟨hsmooth, bound, hbound, herror⟩ := hclose
  refine ⟨fun s hs => ?_, bound, hbound, fun s hs z hz => ?_⟩
  · rw [hpull s hs]
    exact hsmooth s hs
  · rw [hpull s hs]
    exact herror s hs z hz

theorem surgeryCanonicalControl_of_neck_gluing_family {epsilon beta : ℝ}
    (hglue : M45NeckGluingProperty.{u} epsilon beta)
    (I : M45NeckGluingInput.{u} epsilon beta)
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Cc : ℝ} {g : RiemannianMetric 3 C.carrier}
    (N : EpsilonNeck g) (hNeps : N.epsilon = epsilon)
    (e : SurgeryFlowCylinder F C origin (N.scale⁻¹ ^ 2)
      (Ioc (-1 : ℝ) 0) N.carrier)
    (hscalar : (F.connection (origin + 0 / (N.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) N.center) =
        N.connection.scalarCurvature N.center)
    (hpull : ∀ s ∈ Ioc (-1 : ℝ) 0,
      surgeryCylinderPullback e N.coordinate_map s =
        I.piecewiseTensor I.recent_patch.coordinate s) :
    SurgeryCanonicalControl F (origin + 0 / (N.scale⁻¹ ^ 2))
      (e.forward 0 (by constructor <;> norm_num) N.center) epsilon Cc := by
  have hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e N.coordinate_map) := by
    rw [hNeps]
    exact neckGluing_family_close hglue I hpull
  obtain ⟨S, hS⟩ := exists_physical_strong_neck_of_family N e hscalar hfamily
  rw [← hNeps]
  exact SurgeryCanonicalControl.neck S hS

end PoincareConjecture.M47
