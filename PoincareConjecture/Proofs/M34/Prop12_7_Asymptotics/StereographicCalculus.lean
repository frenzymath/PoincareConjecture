import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.StereographicMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable def stereographicCylinderLogDerivative (i : Fin 2) (x : E3) : ℝ :=
  -2 * x i.castSucc / stereographicCylinderDenominator x

theorem stereographicCylinderDenominator_hasFDerivAt (x : E3) :
    HasFDerivAt stereographicCylinderDenominator
      ((2 * x 0) • (EuclideanSpace.proj 0 : E3 →L[ℝ] ℝ) +
        (2 * x 1) • (EuclideanSpace.proj 1 : E3 →L[ℝ] ℝ)) x := by
  convert! ((hasFDerivAt_const (4 : ℝ) x).add
    ((EuclideanSpace.proj 0 : E3 →L[ℝ] ℝ).hasFDerivAt.pow 2)).add
      ((EuclideanSpace.proj 1 : E3 →L[ℝ] ℝ).hasFDerivAt.pow 2) using 1
  simp

theorem stereographicCylinderDensity_fderiv (x w : E3) :
    fderiv ℝ stereographicCylinderDensity x w =
      -64 * (x 0 * w 0 + x 1 * w 1) / stereographicCylinderDenominator x ^ 3 := by
  have hne := (stereographicCylinderDenominator_pos x).ne'
  have ho : HasDerivAt (fun s : ℝ => 16 / s ^ 2)
      (-32 / stereographicCylinderDenominator x ^ 3) (stereographicCylinderDenominator x) := by
    convert! (hasDerivAt_const (stereographicCylinderDenominator x) (16 : ℝ)).div
      ((hasDerivAt_id _).pow 2) (pow_ne_zero 2 hne) using 1
    simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
    field_simp
    ring
  have h := ho.comp_hasFDerivAt x (stereographicCylinderDenominator_hasFDerivAt x)
  change HasFDerivAt stereographicCylinderDensity _ x at h
  rw [h.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change (-32 / stereographicCylinderDenominator x ^ 3) *
    (2 * x 0 * w 0 + 2 * x 1 * w 1) = _
  field_simp
  ring

theorem stereographicCylinderLogDerivative_fderiv (i : Fin 2) (x w : E3) :
    fderiv ℝ (stereographicCylinderLogDerivative i) x w =
      -2 * w i.castSucc / stereographicCylinderDenominator x +
        4 * x i.castSucc * (x 0 * w 0 + x 1 * w 1) /
          stereographicCylinderDenominator x ^ 2 := by
  have hne := (stereographicCylinderDenominator_pos x).ne'
  have hinv := (hasDerivAt_inv hne).comp_hasFDerivAt x
    (stereographicCylinderDenominator_hasFDerivAt x)
  have h := ((EuclideanSpace.proj i.castSucc : E3 →L[ℝ] ℝ).hasFDerivAt.const_mul
    (-2 : ℝ)).mul hinv
  rw [show stereographicCylinderLogDerivative i =
    (fun y : E3 => (-2 * y i.castSucc) * (stereographicCylinderDenominator y)⁻¹) from
      funext (fun y => by simp only [stereographicCylinderLogDerivative, div_eq_mul_inv])]
  change HasFDerivAt (fun y : E3 => (-2 * y i.castSucc) *
    (stereographicCylinderDenominator y)⁻¹) _ x at h
  rw [h.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul, Function.comp_apply]
  change (-2 * x i.castSucc) * (-(stereographicCylinderDenominator x ^ 2)⁻¹ *
    (2 * x 0 * w 0 + 2 * x 1 * w 1)) +
      (stereographicCylinderDenominator x)⁻¹ * (-2 * w i.castSucc) = _
  field_simp
  ring

theorem stereographicCylinderCoefficients_fderiv (b : ℝ) (x u v w : E3) :
    fderiv ℝ (fun y => stereographicCylinderCoefficients b y u v) x w =
      2 * b * stereographicCylinderDensity x *
        (stereographicCylinderLogDerivative 0 x * w 0 +
          stereographicCylinderLogDerivative 1 x * w 1) * (u 0 * v 0 + u 1 * v 1) := by
  have hd := (stereographicCylinderDensity_contDiff.differentiable (by simp) x).hasFDerivAt
  have h := ((hd.const_mul b).mul_const (u 0 * v 0 + u 1 * v 1)).add_const (u 2 * v 2)
  have heq : (fun y => stereographicCylinderCoefficients b y u v) =
      (fun y => b * stereographicCylinderDensity y * (u 0 * v 0 + u 1 * v 1) + u 2 * v 2) :=
    funext (fun y => stereographicCylinderCoefficients_apply b y u v)
  rw [heq, h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [stereographicCylinderDensity_fderiv]
  have hne := (stereographicCylinderDenominator_pos x).ne'
  dsimp only [stereographicCylinderDensity, stereographicCylinderLogDerivative]
  norm_num only [Fin.castSucc_zero, Fin.castSucc_one]
  field_simp
  ring

end PoincareConjecture.M34
