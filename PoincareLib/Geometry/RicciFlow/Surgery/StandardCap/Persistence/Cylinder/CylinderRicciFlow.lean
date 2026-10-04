import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Cylinder.NormalizedCylinderFlow
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.TargetMetricTransport

/-!
# The ordinary flow and its actual cylinder metric identity

This local record retains the constructed Ricci flow on the
literal physical birth-chart target together with its actual
metric identity. Morgan--Tian, Lemma 16.8, pp. 372-373;
see M44 derivations 62-63.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- The actual normalized ordinary flow carried by a physical
birth-chart target of the surviving cylinder. Source: Lemma 16.8,
pp. 372-373; M44 derivations 62-63. -/
structure CylinderRicciFlow
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) where
  /-- The ordinary flow remains on the physical Type-u carrier. -/
  flow : RicciFlow 3 (⟨f.target, f.open_target⟩ : Opens C.carrier) I
  /-- Both actual tangent slots use the physical cylinder transport. -/
  metric_link : ∀ (s : ℝ) (hs : s ∈ I)
    (y : (⟨f.target, f.open_target⟩ : Opens C.carrier)) (v w : TangentSpace (𝓡 3) y),
    (flow.metric s).inner y v w = scale * (F.metric (origin + s / scale)).inner
      (cylinderTargetTransport e f s hs y)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y v)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y w)

/-- The actual maximal-survival cylinder supplies this ordinary
flow and its physical metric link without an additional analytic
hypothesis. Source: Lemma 16.8 and Proposition 16.5;
M44 derivations 62-63. -/
theorem exists_cylinderRicciFlow
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    {B : ℝ} (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U)
    (hU : IsOpen U) (hB : 0 < B)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U) :
    Nonempty (CylinderRicciFlow e f) := by
  obtain ⟨G, hcoeff⟩ := exists_normalized_cylinder_physical_flow P hpinch e hU hB f hmap
  exact ⟨⟨G, fun s hs => cylinderTargetTransport_metric e hU f hmap s hs (G.metric s)
    (fun p => hcoeff p s hs)⟩⟩

/-- The same physical metric identity with the target metric
on the left has the reciprocal normalization factor. Source:
Lemma 16.8; M44 derivation 63. -/
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

end PoincareMT.M44
