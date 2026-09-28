import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.MetricRowFrame
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology

namespace PoincareConjecture.M64

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

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

end PoincareConjecture.M64
