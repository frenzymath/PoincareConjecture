import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_CylinderFirstExit
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Function

universe u v

namespace PoincareConjecture.M47

open Proofs.M12 Proofs.M46

theorem seedM15_compactCylinder_capture
    {F : GeneralizedRicciFlowData.{u}}
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hJ : IsCompact J.domain) (hU : IsCompact (U : Set C.carrier))
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    {A : Type v} [TopologicalSpace A] [PreconnectedSpace A]
    (gamma : A → R.spacetime.Point) (hgamma : Continuous gamma)
    (hclock : ∀ t, R.spacetime.timeFunction (gamma t) ∈
      (cylinderPhysicalInterval origin scale e.scale_pos J).domain)
    (hcaptured : ∃ t, gamma t ∈ range (rawCylinderMap R e)) :
    ∀ t, gamma t ∈ range (rawCylinderMap R e) := by
  let : CompactSpace J.domain := isCompact_iff_compactSpace.mp hJ
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let clock := cylinderClockHomeomorph origin scale e.scale_pos J
  let : CompactSpace (cylinderPhysicalInterval origin scale e.scale_pos J).domain :=
    clock.symm.surjective.compactSpace clock.symm.continuous
  have hclosed : IsClosed (range (rawCylinderMap R e)) :=
    (isCompact_range (rawCylinderMap_embedding R e).continuous).isClosed
  have hopen := rawCylinder_preimage_isOpen R e hI gamma hgamma hclock
  have hall : gamma ⁻¹' range (rawCylinderMap R e) = univ :=
    (show IsClopen (gamma ⁻¹' range (rawCylinderMap R e)) from
      ⟨hclosed.preimage hgamma, hopen⟩).eq_univ hcaptured
  intro t
  change t ∈ gamma ⁻¹' range (rawCylinderMap R e)
  rw [hall]
  exact mem_univ t

end PoincareConjecture.M47
