import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.StereographicConnection
import PoincareLib.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrace
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Connection.Variation
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvaturePairExchange
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureRicciSecondDerivative
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrace
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrilinear
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Energy.CurvatureRateAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coefficients.CompactFiniteCoefficient
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.RateFiniteAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.ScalarEnergyComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coordinates.FamilyBundleCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricCompactBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricDifferenceEvolution
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricInverse

/-!
# Actual curvature and Ricci of the stereographic cylinder

The Christoffel matrices commute. Differentiating their scalar entries
and taking the actual curvature trace in the ordinary coordinate basis
therefore gives Ric = rho * H, independently of the positive angular
scale. This is Morgan-Tian Proposition 12.7, pp. 298-299 and
stereographic-cylinder-euclidean.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareMT.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The logarithmic coefficient is smooth on the whole coordinate space
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderLogDerivative_contDiff (i : Fin 2) :
    ContDiff ℝ ∞ (stereographicCylinderLogDerivative i) := by
  have hd : ContDiff ℝ ∞ stereographicCylinderDenominator := by
    change ContDiff ℝ ∞ (fun x : E3 => 4 + EuclideanSpace.proj 0 x ^ 2 +
      EuclideanSpace.proj 1 x ^ 2)
    fun_prop
  exact (contDiff_const.mul
    (EuclideanSpace.proj i.castSucc : E3 →L[ℝ] ℝ).contDiff).div hd
    (fun x => (stereographicCylinderDenominator_pos x).ne')

/-- The actual vector derivative of the Christoffel field is obtained by
differentiating its two scalar logarithmic coefficients
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderChristoffel_fderiv (x u v w : E3) :
    fderiv ℝ (fun y => stereographicCylinderChristoffel y u v) x w =
      WithLp.toLp 2
        ![fderiv ℝ (stereographicCylinderLogDerivative 0) x w *
            (u 0 * v 0 - u 1 * v 1) +
            fderiv ℝ (stereographicCylinderLogDerivative 1) x w *
              (u 1 * v 0 + u 0 * v 1),
          fderiv ℝ (stereographicCylinderLogDerivative 1) x w *
            (u 1 * v 1 - u 0 * v 0) +
            fderiv ℝ (stereographicCylinderLogDerivative 0) x w *
              (u 0 * v 1 + u 1 * v 0), 0] := by
  let V0 : E3 := WithLp.toLp 2 ![u 0 * v 0 - u 1 * v 1,
    u 0 * v 1 + u 1 * v 0, 0]
  let V1 : E3 := WithLp.toLp 2 ![u 1 * v 0 + u 0 * v 1,
    u 1 * v 1 - u 0 * v 0, 0]
  have heq : (fun y => stereographicCylinderChristoffel y u v) =
      (fun y => stereographicCylinderLogDerivative 0 y • V0 +
        stereographicCylinderLogDerivative 1 y • V1) := by
    funext y
    ext i
    fin_cases i <;> simp [stereographicCylinderChristoffel, V0, V1]
    ring
  have h0 := ((stereographicCylinderLogDerivative_contDiff 0).differentiable
    (by simp) x).hasFDerivAt.smul_const V0
  have h1 := ((stereographicCylinderLogDerivative_contDiff 1).differentiable
    (by simp) x).hasFDerivAt.smul_const V1
  have h := h0.add h1
  change HasFDerivAt (fun y => stereographicCylinderLogDerivative 0 y • V0 +
    stereographicCylinderLogDerivative 1 y • V1) _ x at h
  rw [heq, h.fderiv]
  ext i
  fin_cases i <;> simp [V0, V1]
  ring

/-- The quadratic connection terms cancel in the actual retained
curvature tensor (Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderCurvature_eq {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v w : E3) :
    D.curvature x u v w =
      fderiv ℝ (fun y => stereographicCylinderChristoffel y v w) x u -
        fderiv ℝ (fun y => stereographicCylinderChristoffel y u w) x v := by
  rw [D.curvature_eq_euclideanConnection]
  simp only [stereographicCylinderEuclideanConnection_eq hb D]
  rw [stereographicCylinderChristoffel_comp_comm x u v w]
  abel

/-- The first contribution to the ordinary-basis Ricci trace has the
positive spherical sign (Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderCurvature_trace_zero {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v : E3) :
    (EuclideanSpace.proj 0 : E3 →L[ℝ] ℝ) (D.curvature x (EuclideanSpace.single 0 1) u v) =
      stereographicCylinderDensity x * u 1 * v 1 := by
  rw [stereographicCylinderCurvature_eq hb D]
  simp only [stereographicCylinderChristoffel_fderiv,
    stereographicCylinderLogDerivative_fderiv]
  have hne := (stereographicCylinderDenominator_pos x).ne'
  simp [stereographicCylinderDensity]
  field_simp
  simp only [stereographicCylinderDenominator]
  ring

/-- The second contribution to the ordinary-basis Ricci trace
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderCurvature_trace_one {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v : E3) :
    (EuclideanSpace.proj 1 : E3 →L[ℝ] ℝ) (D.curvature x (EuclideanSpace.single 1 1) u v) =
      stereographicCylinderDensity x * u 0 * v 0 := by
  rw [stereographicCylinderCurvature_eq hb D]
  simp only [stereographicCylinderChristoffel_fderiv,
    stereographicCylinderLogDerivative_fderiv]
  have hne := (stereographicCylinderDenominator_pos x).ne'
  simp [stereographicCylinderDensity]
  field_simp
  simp only [stereographicCylinderDenominator]
  ring

/-- There is no axial contribution to the actual Ricci trace
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderCurvature_trace_two {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v : E3) :
    (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ) (D.curvature x (EuclideanSpace.single 2 1) u v) = 0 := by
  rw [stereographicCylinderCurvature_eq hb D]
  simp [stereographicCylinderChristoffel_fderiv]

/-- The actual Ricci tensor of the cylinder is the unit-sphere angular
form, independently of the angular scale b
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderRicci {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v : E3) :
    D.ricci x u v = stereographicCylinderDensity x * (u 0 * v 0 + u 1 * v 1) := by
  let K : E3 → E3 := fun a => D.curvature x a u v
  have hr : D.ricci x u v = ∑ i : Fin 3,
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
        (K ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i)) i := by
    convert! PoincareMT.Proofs.M03.ricci_eq_sum_basis D x u v
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis using 1
  rw [hr]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change (∑ i : Fin 3, (EuclideanSpace.proj i : E3 →L[ℝ] ℝ)
    (D.curvature x (EuclideanSpace.single i 1) u v)) = _
  rw [Fin.sum_univ_three]
  rw [stereographicCylinderCurvature_trace_zero hb D,
    stereographicCylinderCurvature_trace_one hb D,
    stereographicCylinderCurvature_trace_two hb D]
  ring

end PoincareMT.M34
