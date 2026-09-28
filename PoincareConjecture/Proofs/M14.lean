import PoincareConjecture.Statements.M14GeneralizedLGeometry
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Proofs.M12
import PoincareConjecture.Proofs.M14.Ch6_7_GeneralizedAssembly
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeCoverage










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ}





































































theorem generalizedLGeometryTheory
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    GeneralizedLGeometryTheory.{u} n := by
  cases hM04
  refine ⟨?_⟩
  intro X _ time I G
  exact ⟨M14.generalizedLGeometryConclusion_of_smallTimeCoverage
    (m12MetricPredecessors.{0} n) ricciFlowCurvatureTheory.{0} hM12 hM13 G
    (M14.smallTimeCoverageStatement (m12MetricPredecessors.{0} n) hM12 G)⟩




theorem generalizedLGeometryTheory_from_predecessors (n : ℕ) :
    GeneralizedLGeometryTheory.{u} n :=
  generalizedLGeometryTheory
    (generalizedRicciGaugeGeometry_from_M03_M04_M11 n)
    (generalizedParabolicRescaling_from_M12 n) ricciFlowCurvatureTheory

end PoincareConjecture
