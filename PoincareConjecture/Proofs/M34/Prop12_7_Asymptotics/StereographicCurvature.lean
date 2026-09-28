import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.StereographicConnection
import PoincareConjecture.Proofs.M03.CurvatureTrace











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)



theorem stereographicCylinderLogDerivative_contDiff (i : Fin 2) :
    ContDiff ℝ ∞ (stereographicCylinderLogDerivative i) := by
  have hd : ContDiff ℝ ∞ stereographicCylinderDenominator := by
    change ContDiff ℝ ∞ (fun x : E3 => 4 + EuclideanSpace.proj 0 x ^ 2 +
      EuclideanSpace.proj 1 x ^ 2)
    fun_prop
  exact (contDiff_const.mul
    (EuclideanSpace.proj i.castSucc : E3 →L[ℝ] ℝ).contDiff).div hd
    (fun x => (stereographicCylinderDenominator_pos x).ne')




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



theorem stereographicCylinderCurvature_eq {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v w : E3) :
    D.curvature x u v w =
      fderiv ℝ (fun y => stereographicCylinderChristoffel y v w) x u -
        fderiv ℝ (fun y => stereographicCylinderChristoffel y u w) x v := by
  rw [D.curvature_eq_euclideanConnection]
  simp only [stereographicCylinderEuclideanConnection_eq hb D]
  rw [stereographicCylinderChristoffel_comp_comm x u v w]
  abel



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



theorem stereographicCylinderCurvature_trace_two {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v : E3) :
    (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ) (D.curvature x (EuclideanSpace.single 2 1) u v) = 0 := by
  rw [stereographicCylinderCurvature_eq hb D]
  simp [stereographicCylinderChristoffel_fderiv]




theorem stereographicCylinderRicci {b : ℝ} (hb : 0 < b)
    (D : LeviCivitaData (stereographicCylinderMetric b hb)) (x u v : E3) :
    D.ricci x u v = stereographicCylinderDensity x * (u 0 * v 0 + u 1 * v 1) := by
  let K : E3 → E3 := fun a => D.curvature x a u v
  have hr : D.ricci x u v = ∑ i : Fin 3,
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
        (K ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i)) i := by
    convert! PoincareConjecture.Proofs.M03.ricci_eq_sum_basis D x u v
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

end PoincareConjecture.M34
