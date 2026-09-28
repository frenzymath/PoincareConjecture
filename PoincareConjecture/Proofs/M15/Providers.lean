import PoincareConjecture.Proofs.M15
import PoincareConjecture.Proofs.M08
import PoincareConjecture.Proofs.M09
import PoincareConjecture.Proofs.M10
import PoincareConjecture.Proofs.M14

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

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

theorem noncollapsingGeneralizedAndCompact_from_predecessors (n : ℕ) :
    NoncollapsingConclusion.{u} n :=
  noncollapsingGeneralizedAndCompact n ricciFlowCurvatureTheory
    generalizedRicciGaugeGeometry_from_M03_M04_M11
    generalizedParabolicRescaling_from_M12
    generalizedLGeometryTheory_from_predecessors
    (m15OrdinaryProvidersFromMilestones 3)

end PoincareConjecture
