import PoincareConjecture.Proofs.M48.RegularSpacetime
import PoincareConjecture.Proofs.M12.GeneralizedCylinderMetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M48RegularSpacetimeData

open Proofs.M12

variable {F : SurgeryFlowData.{u}} {T : ℝ} {L : RepairedPreterminalSlab F T}
  (R : M48RegularSpacetimeData L) {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder R.history.generalized C a q J.domain U)
  (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ R.history.generalized.interval)

noncomputable def regularCylinder :
    CompatibleSpacetimeCylinder R.geometry.realization.spacetime
      (R.geometry.realization.timeIntervals.interval
        (cylinderPhysicalInterval a q e.scale_pos J)) U :=
  rawCylinderTransport R.geometry.realization e hI

noncomputable def regularCylinderMetric : SpacetimeCylinderMetric (R.regularCylinder e hI) :=
  rawCylinderMetric R.geometry.realization e hI

theorem regularCylinder_point (s : J.domain) (x : U) :
    (R.regularCylinder e hI).toSpacetime
        ((cylinderClockHomeomorph a q e.scale_pos J).symm s, x) =
      e.pointMap s.val s.property x.val :=
  rawCylinderMap_at_parameter R.geometry.realization e s x

theorem regularCylinder_metric (s : J.domain) (x : U) (v w : TangentSpace (𝓡 3) x) :
    ((R.regularCylinderMetric e hI).metric (a + s.val / q)).inner x v w =
      e.pullbackInner s.val s.property x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) / q :=
  rawCylinderMetric_eq R.geometry.realization e hI (R.regularCylinderMetric e hI) s
    (R.geometry.sliceIdentification (a + s.val / q)) x v w

end PoincareConjecture.M48RegularSpacetimeData
