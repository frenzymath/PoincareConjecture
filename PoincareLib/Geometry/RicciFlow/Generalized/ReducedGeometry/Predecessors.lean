import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Assembly
import PoincareLib.Geometry.RicciFlow.Rescaling.Generalized
import PoincareLib.Geometry.Spacetime.Realization
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Regularity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.CurvatureCalculus

/-! Compatibility names used by the unchanged Mapher generalized L-geometry proof.
The metric and gauge services are supplied by the existing subject modules. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

theorem m12MetricPredecessors (n : ℕ) : M12MetricPredecessors.{u} n where
  connection_exists _ _ _ _ _ _ g := normalization_exists_leviCivitaData g
  connection_regular _ _ _ _ _g D _ hU Y hY :=
    D.normalization_contMDiffOn_connection hU Y hY
  curvature_calculus _ _ _ _ _g D := D.normalization_curvatureTensorCalculus

theorem generalizedRicciGaugeGeometry_from_M03_M04_M11 (n : ℕ) :
    GeneralizedRicciGaugeTheory.{u} n :=
  generalizedRicciGaugeGeometry n (generalizedSpacetimeGeometry n)
    (m12MetricPredecessors.{u} n) (m12MetricPredecessors.{0} n)

theorem generalizedParabolicRescaling_from_M12 (n : ℕ) :
    GeneralizedParabolicRescalingTheory.{u} n :=
  generalizedParabolicRescaling n (generalizedRicciGaugeGeometry_from_M03_M04_M11 n)

end PoincareMT
