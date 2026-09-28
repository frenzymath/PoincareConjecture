import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.StereographicCalculus
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable def stereographicCylinderChristoffel (x u v : E3) : E3 :=
  WithLp.toLp 2
    ![stereographicCylinderLogDerivative 0 x * (u 0 * v 0 - u 1 * v 1) +
        stereographicCylinderLogDerivative 1 x * (u 1 * v 0 + u 0 * v 1),
      stereographicCylinderLogDerivative 1 x * (u 1 * v 1 - u 0 * v 0) +
        stereographicCylinderLogDerivative 0 x * (u 0 * v 1 + u 1 * v 0), 0]

theorem stereographicCylinderChristoffel_koszul (b : ℝ) (x u v w : E3) :
    2 * stereographicCylinderCoefficients b x (stereographicCylinderChristoffel x u v) w =
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y v w) x u +
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y w u) x v -
      fderiv ℝ (fun y => stereographicCylinderCoefficients b y u v) x w := by
  rw [stereographicCylinderCoefficients_fderiv, stereographicCylinderCoefficients_fderiv,
    stereographicCylinderCoefficients_fderiv, stereographicCylinderCoefficients_apply]
  simp [stereographicCylinderChristoffel]
  ring

theorem stereographicCylinderChristoffel_comp_comm (x u v w : E3) :
    stereographicCylinderChristoffel x u (stereographicCylinderChristoffel x v w) =
      stereographicCylinderChristoffel x v (stereographicCylinderChristoffel x u w) := by
  ext i
  fin_cases i <;> simp [stereographicCylinderChristoffel] <;> ring

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

theorem stereographicCylinderEuclideanConnection_eq {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (u v : E3) :
    D.euclideanConnection u v = fun x => stereographicCylinderChristoffel x u v :=
  funext (fun x => stereographicCylinderConnection_formula hb D x u v)

end PoincareConjecture.M34
