import PoincareConjecture.Proofs.M12.GeneralizedCylinders
import PoincareConjecture.Definitions.M13TimeRescaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

noncomputable def cylinderPhysicalInterval (a q : ℝ) (hq : 0 < q)
    (J : SpacetimeInterval) : SpacetimeInterval where
  domain := parabolicTimeInv q a '' J.domain
  ordConnected := by
    let : J.domain.OrdConnected := J.ordConnected
    exact Set.ordConnected_image (parabolicTimeOrderIso q hq a).symm
  nontrivial := J.nontrivial.image (parabolicTimeOrderIso q hq a).symm.injective

theorem cylinderClock_mem (a q : ℝ) (hq : 0 < q) (J : SpacetimeInterval)
    (t : (cylinderPhysicalInterval a q hq J).domain) :
    parabolicTime q a t.val ∈ J.domain := by
  obtain ⟨s, hs, ht⟩ := t.property
  rw [← ht, parabolicTime_parabolicTimeInv q hq]
  exact hs

noncomputable def cylinderClockHomeomorph (a q : ℝ) (hq : 0 < q) (J : SpacetimeInterval) :
    (cylinderPhysicalInterval a q hq J).domain ≃ₜ J.domain where
  toFun t := ⟨parabolicTime q a t.val, cylinderClock_mem a q hq J t⟩
  invFun s := ⟨parabolicTimeInv q a s.val, ⟨s.val, s.property, rfl⟩⟩
  left_inv t := Subtype.ext (parabolicTimeInv_parabolicTime q hq a t.val)
  right_inv s := Subtype.ext (parabolicTime_parabolicTimeInv q hq a s.val)
  continuous_toFun := by unfold parabolicTime; fun_prop
  continuous_invFun := by unfold parabolicTimeInv; fun_prop

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)

noncomputable def rawCylinderMap
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
    R.spacetime.Point :=
  e.pointMap (cylinderClockHomeomorph a q e.scale_pos J p.1).val
    (cylinderClockHomeomorph a q e.scale_pos J p.1).property p.2.val

theorem rawCylinderMap_time
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
    R.spacetime.timeFunction (rawCylinderMap R e p) = p.1.val :=
  parabolicTimeInv_parabolicTime q e.scale_pos a p.1.val

theorem rawCylinderMap_embedding : Topology.IsEmbedding (rawCylinderMap R e) :=
  e.embedding.comp ((cylinderClockHomeomorph a q e.scale_pos J).isEmbedding.prodMap
    Topology.IsEmbedding.id)

theorem rawCylinderMap_at_parameter (s : J.domain) (x : U) :
    rawCylinderMap R e ((cylinderClockHomeomorph a q e.scale_pos J).symm s, x) =
      e.pointMap s.val s.property x.val := by
  unfold rawCylinderMap
  simp only [Homeomorph.apply_symm_apply]

end PoincareConjecture.Proofs.M12
