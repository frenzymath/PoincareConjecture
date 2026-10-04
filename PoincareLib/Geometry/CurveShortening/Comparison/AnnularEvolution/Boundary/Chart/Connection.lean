import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Metric.RowFrame
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients

/-! The actual connection of a locally realized chart metric is the
Christoffel coefficient in the minimum's coordinate equation.
Source: MT Lemma 19.15, pp. 447-449; M64 finite collar derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology

namespace PoincareMT.M64

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Agreement of the actual metric germ identifies its connection coefficient with the
original local Christoffel coefficient. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem connectionCoefficient_eq_of_metric_germ
    {g : RiemannianMetric n E} (D : LeviCivitaData g)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q : E}
    (hB : g.euclideanCoefficients =ᶠ[𝓝 q] B) :
    M65Gauss.connectionCoefficient D q = CoordinateExponential.christoffelBilinear B q := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change D.connection (fun _ : E => v) q u = _
  rw [D.connection_const_eq_inverse, hB.self_of_nhds, hB.fderiv_eq]
  rfl

end PoincareMT.M64
