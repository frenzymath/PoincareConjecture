import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateJacobian
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationIsothermalMetric













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)





theorem scalarConjugateForm_metric_identity (H : Plane → ℝ) (x v w : Plane) :
    fderiv ℝ H x v * fderiv ℝ H x w +
      scalarConjugateForm D H x v * scalarConjugateForm D H x w =
      g.inner x (D.gradient H x) (D.gradient H x) * g.inner x v w := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let a := g.inner x (e 0) (e 0)
  let b := g.inner x (e 0) (e 1)
  let c := g.inner x (e 1) (e 1)
  let Z : Plane := D.gradient H x
  let rho := g.pullbackVolumeDensity id x
  have hrho : rho ^ 2 = a * c - b ^ 2 := by
    have hrhop := (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x)
      contMDiffAt_id (by simpa using Function.injective_id)).2
    have hrhoe : rho = Real.sqrt (a * c - b ^ 2) := by
      simp only [rho, RiemannianMetric.pullbackVolumeDensity, mfderiv_id,
        Matrix.det_fin_two, Matrix.of_apply]
      change Real.sqrt (a * c - b * g.inner x (e 1) (e 0)) = _
      rw [g.symm x (e 1) (e 0)]
      simp only [b, pow_two]
    change 0 < rho at hrhop
    rw [hrhoe] at hrhop ⊢
    exact Real.sq_sqrt (Real.sqrt_pos.mp hrhop).le
  have hgradient (z : Plane) : fderiv ℝ H x z = g.inner x Z z := by
    change fderiv ℝ H x z = g.inner x (D.gradient H x) z
    rw [D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  have hconjugate (z : Plane) :
      scalarConjugateForm D H x z = rho * (-Z 1 * z 0 + Z 0 * z 1) := by
    simp only [scalarConjugateForm, M60.rotatedFlux, scalarMetricFlux,
      add_apply, smul_apply, smul_eq_mul,
      EuclideanSpace.coe_proj, rho, Z]
    ring
  rw [hgradient, hgradient, hconjugate, hconjugate]
  rw [M60.plane_metric_expand g x Z v, M60.plane_metric_expand g x Z w,
    M60.plane_metric_expand g x (D.gradient H x) (D.gradient H x),
    M60.plane_metric_expand g x v w]
  change (a * Z 0 * v 0 + b * (Z 0 * v 1 + Z 1 * v 0) + c * Z 1 * v 1) *
      (a * Z 0 * w 0 + b * (Z 0 * w 1 + Z 1 * w 0) + c * Z 1 * w 1) +
      (rho * (-Z 1 * v 0 + Z 0 * v 1)) *
      (rho * (-Z 1 * w 0 + Z 0 * w 1)) =
      (a * Z 0 * Z 0 + b * (Z 0 * Z 1 + Z 1 * Z 0) + c * Z 1 * Z 1) *
      (a * v 0 * w 0 + b * (v 0 * w 1 + v 1 * w 0) + c * v 1 * w 1)
  linear_combination (Z 1 * v 0 - Z 0 * v 1) *
    (Z 1 * w 0 - Z 0 * w 1) * hrho





theorem scalarConjugateLinear_inner (H : Plane → ℝ) (x v w : Plane) :
    inner ℝ (scalarConjugateLinear D H x v) (scalarConjugateLinear D H x w) =
      g.inner x (D.gradient H x) (D.gradient H x) * g.inner x v w := by
  convert! scalarConjugateForm_metric_identity D H x v w using 1
  simp [scalarConjugateLinear, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two, mul_comm]

end PoincareConjecture.M64Uniformization
