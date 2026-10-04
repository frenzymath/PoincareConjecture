import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.OrdinaryFlow
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderMetric

/-!
# Ordinary flow on a compatible generalized cylinder

M12 realizes the generalized spacetime and transports an actual compatible
cylinder to an ordinary Ricci flow on its open source carrier.  The source
metric is the existing raw-cylinder metric, so this producer exposes the
metric pullback instead of introducing a new cylinder hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

noncomputable section

variable {F : GeneralizedRicciFlowData.{u}}
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)
  (hI : (Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)

/-- A generalized cylinder has an actual ordinary Ricci-flow witness on its
open source carrier.  The witness is obtained from the intrinsic equation of
the realized generalized flow and M12's compatible-cylinder realization.
-/
theorem exists_raw_cylinder_ordinary_flow :
    ∃ G : Proofs.M12.FlowBoxRicciGeometry F,
      ∃ K : SpacetimeCylinderMetric
          (Proofs.M12.rawCylinderTransport G.realization e hI),
        Nonempty (OrdinaryGaugeWitness G.leafwise
          (Proofs.M12.rawCylinderTransport G.realization e hI) K) := by
  let hM11 : GeneralizedSpacetimeGeometryTheory.{u} 3 :=
    generalizedSpacetimeGeometry 3
  let hM12 : GeneralizedRicciGaugeTheory.{u} 3 :=
    generalizedRicciGaugeGeometry_from_M03_M04_M11 3
  obtain ⟨G⟩ := Proofs.M12.flowBoxRicciGeometry F hM11 hM12
  let R := G.realization
  let eR := Proofs.M12.rawCylinderTransport R e hI
  let H := hM12.gauges F.point Sigma.fst (Proofs.M12.flowInterval F)
    R.spacetime R.slices R.timeIntervals R.gaugeCover G.leafwise
  have hOn : IntrinsicGeneralizedRicciEquationOn G.leafwise
      (Set.range eR.toSpacetime) := by
    intro p hp u v
    exact G.equation p u v
  let K : SpacetimeCylinderMetric eR :=
    Proofs.M12.rawCylinderMetric R e hI
  obtain ⟨W⟩ := H.compatible_ordinary U
    (Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J) eR K hOn
  exact ⟨G, K, ⟨W⟩⟩

end

end PoincareMT.M28
