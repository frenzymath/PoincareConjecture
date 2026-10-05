import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.StereographicCalculus
import PoincareLib.Geometry.Riemannian.Curvature.Euclidean

/-!
# The actual stereographic cylinder connection

Constant-frame Koszul identifies every retained compatible connection
with the two horizontal conformal matrices. Those matrices commute, so
the quadratic curvature terms cancel. This is Morgan-Tian Proposition
12.7, pp. 298-299 and stereographic-cylinder-euclidean.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareMT.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The two-dimensional conformal Christoffel vector, with zero axial
component; the first vector is the direction, the second the section
value (Proposition 12.7, pp. 298-299). -/
noncomputable def stereographicCylinderChristoffel (x u v : E3) : E3 :=
  WithLp.toLp 2
    ![stereographicCylinderLogDerivative 0 x * (u 0 * v 0 - u 1 * v 1) +
        stereographicCylinderLogDerivative 1 x * (u 1 * v 0 + u 0 * v 1),
      stereographicCylinderLogDerivative 1 x * (u 1 * v 1 - u 0 * v 0) +
        stereographicCylinderLogDerivative 0 x * (u 0 * v 1 + u 1 * v 0), 0]

/-- The explicit coefficients satisfy the actual constant-frame Koszul
identity at every spatial point (Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderChristoffel_koszul (b : ℝ) (x u v w : E3) :
    2 * stereographicCylinderCoefficients b x (stereographicCylinderChristoffel x u v) w =
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y v w) x u +
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y w u) x v -
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y u v) x w := by
  rw [stereographicCylinderCoefficients_fderiv, stereographicCylinderCoefficients_fderiv,
    stereographicCylinderCoefficients_fderiv, stereographicCylinderCoefficients_apply]
  simp [stereographicCylinderChristoffel]
  ring

/-- The two horizontal connection matrices commute; every quadratic
connection term therefore cancels in curvature
(Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderChristoffel_comp_comm (x u v w : E3) :
    stereographicCylinderChristoffel x u (stereographicCylinderChristoffel x v w) =
      stereographicCylinderChristoffel x v (stereographicCylinderChristoffel x u w) := by
  ext i
  fin_cases i <;> simp [stereographicCylinderChristoffel] <;> ring

/-- Every actual compatible connection has precisely the computed
Christoffel vector (Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderConnection_formula {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v : E3) :
    D.connection (fun _ => v) x u = stereographicCylinderChristoffel x u v := by
  apply ((stereographicCylinderMetric b hb).inner_isInvertible x).injective
  ext w
  have hk := D.inner_connection_const x u v w
  change 2 * stereographicCylinderCoefficients b x (D.connection (fun _ => v) x u) w =
    fderiv ℝ (fun y => stereographicCylinderCoefficients b y v w) x u +
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y w u) x v -
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y u v) x w at hk
  have he := stereographicCylinderChristoffel_koszul b x u v w
  change stereographicCylinderCoefficients b x (D.connection (fun _ => v) x u) w =
    stereographicCylinderCoefficients b x (stereographicCylinderChristoffel x u v) w
  linarith only [hk, he]

/-- Whole-function equality permits differentiation of the actual
retained connection field (Proposition 12.7, pp. 298-299). -/
theorem stereographicCylinderEuclideanConnection_eq {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (u v : E3) :
    D.euclideanConnection u v = fun x => stereographicCylinderChristoffel x u v :=
  funext (fun x => stereographicCylinderConnection_formula hb D x u v)

end PoincareMT.M34
