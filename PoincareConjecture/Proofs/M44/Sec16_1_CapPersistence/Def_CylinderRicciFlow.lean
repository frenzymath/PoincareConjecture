import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedCylinderFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_TargetMetricTransport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}




structure CylinderRicciFlow
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) where

  flow : RicciFlow 3 (⟨f.target, f.open_target⟩ : Opens C.carrier) I

  metric_link : ∀ (s : ℝ) (hs : s ∈ I)
    (y : (⟨f.target, f.open_target⟩ : Opens C.carrier)) (v w : TangentSpace (𝓡 3) y),
    (flow.metric s).inner y v w = scale * (F.metric (origin + s / scale)).inner
      (cylinderTargetTransport e f s hs y)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y v)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y w)





theorem exists_cylinderRicciFlow
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    {B : ℝ} (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U)
    (hU : IsOpen U) (hB : 0 < B)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U) :
    Nonempty (CylinderRicciFlow e f) := by
  obtain ⟨G, hcoeff⟩ := exists_normalized_cylinder_physical_flow P hpinch e hU hB f hmap
  exact ⟨⟨G, fun s hs => cylinderTargetTransport_metric e hU f hmap s hs (G.metric s)
    (fun p => hcoeff p s hs)⟩⟩




theorem CylinderRicciFlow.physical_metric_link
    {e : SurgeryFlowCylinder F C origin scale I U}
    {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}
    (G : CylinderRicciFlow e f) (s : ℝ) (hs : s ∈ I)
    (y : (⟨f.target, f.open_target⟩ : Opens C.carrier)) (v w : TangentSpace (𝓡 3) y) :
    (F.metric (origin + s / scale)).inner (cylinderTargetTransport e f s hs y)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y v)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y w) =
        scale⁻¹ * (G.flow.metric s).inner y v w := by
  rw [G.metric_link s hs y v w, ← mul_assoc, inv_mul_cancel₀ e.scale_pos.ne', one_mul]

end PoincareConjecture.M44
