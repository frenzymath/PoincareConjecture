import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Proof
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.LGeodesics
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.ReducedLength
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.ReducedVolume
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Proof

/-!
# M15 ordinary services and complete predecessor application

The compact branch uses the actual M08/M09/M10 outputs on one ordinary flow.
The supplier preserves each selected L-geodesic and reduced-length witness.
These checked theorem proofs add no admission.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Supply the ordinary Chapter 6/7 services for M14's conditional capture.
Sources: M08's Lemmas 6.10/6.12 and Proposition 6.33, M09's Proposition 7.5,
and M10's Theorem 7.10, with the corrections recorded in their proof entries. -/
theorem m15OrdinaryProvidersFromMilestones (n : ℕ) :
    M14OrdinaryProviders.{u} n := by
  refine { m08 := ?_, m09 := ?_, m10 := ?_ }
  · intro M _ _ _ _ _ _ J F T R hT hR hwindow hcurv
    exact lGeodesicExistenceAndVariation_from_M04 F T R hT hR hwindow hcurv
  · intro M _ _ _ _ _ _ J F T R hT hR hwindow hcurv L
    exact reducedLengthDifferentialInequalities F T R hT hR hwindow hcurv
      ricciFlowCurvatureTheory L
  · intro M _ _ _ _ _ _ _ _ J F T R hT hR hwindow hcurv L D
    exact reducedVolumeMonotonicity F T R hT hR hwindow hcurv L D

/-- Apply M15 with M04/M12/M13/M14 in every required dimension and the
dimension-three M08/M09/M10 services. This yields the dimension-n Theorem 8.1
and compact dimension-three Theorem 8.10 conclusions under their original
primitive geometric hypotheses, without a provider hypothesis for callers. -/
theorem noncollapsingGeneralizedAndCompact_from_predecessors (n : ℕ) :
    NoncollapsingConclusion.{u} n :=
  noncollapsingGeneralizedAndCompact n ricciFlowCurvatureTheory
    generalizedRicciGaugeGeometry_from_M03_M04_M11
    generalizedParabolicRescaling_from_M12
    generalizedLGeometryTheory_from_predecessors
    (m15OrdinaryProvidersFromMilestones 3)

end PoincareMT
