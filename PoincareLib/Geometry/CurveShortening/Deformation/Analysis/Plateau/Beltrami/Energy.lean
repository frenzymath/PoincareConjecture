import PoincareLib.Geometry.CurveShortening.Deformation.Analysis.Plateau.Beltrami.Isothermal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Star.Real

/-!
# The exact energy weight in disk isothermal coordinates

The actual metric pullback identity determines the Jacobian and hence
the half-trace energy change. Positive regularization gives the required
upper estimate without discarding rank-deficient original metrics.
Source: M65 derivation 30, Morrey ICM 1950, pp. 181-182, and
Fitzi--Wenger Theorem 4.1, for MT Lemma 19.2, printed p. 438.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace Matrix

/-- The literal energy weight after the actual isothermal change of
variables. Source: derivation 30, Morrey ICM pp. 181-182. -/
def isothermalEnergyWeight (K H : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (1 / 2 : ℝ) * (K⁻¹ * H).trace * Real.sqrt K.det

/-- The isothermal pullback identity determines the actual energy
Jacobian. Both determinant signs are covered by the absolute value.
Source: derivation 30, the exact energy formula for MT Lemma 19.2. -/
theorem isothermal_energy_change
    (K B H : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) {c : ℝ} (hc : 0 < c)
    (hiso : B.transpose * K * B = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    (1 / 2 : ℝ) * (B.transpose * H * B).trace =
      |B.det| * isothermalEnergyWeight K H := by
  have hdet := congrArg Matrix.det hiso
  simp only [det_mul, det_transpose, det_smul, det_one, Fintype.card_fin, mul_one] at hdet
  have hB : B.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul, mul_zero] at hdet
    nlinarith [sq_pos_of_pos hc]
  have huB : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have huBT : IsUnit B.transpose.det := by simpa only [det_transpose] using huB
  have huK : IsUnit K.det := isUnit_iff_ne_zero.mpr hK.det_pos.ne'
  have hJac : |B.det| * Real.sqrt K.det = c := by
    have hsq := Real.sq_sqrt hK.det_pos.le
    have hnorm : |B.det| ^ 2 = B.det ^ 2 := sq_abs _
    have hprod : (|B.det| * Real.sqrt K.det) ^ 2 = c ^ 2 := by
      rw [mul_pow, hnorm, hsq]
      nlinarith only [hdet]
    nlinarith [mul_nonneg (abs_nonneg B.det) (Real.sqrt_nonneg K.det)]
  have hKB : K * B = c • B.transpose⁻¹ := by
    calc
      _ = B.transpose⁻¹ * (B.transpose * K * B) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
          nonsing_inv_mul _ huBT, one_mul]
      _ = c • B.transpose⁻¹ := by rw [hiso, Matrix.mul_smul, Matrix.mul_one]
  have hKBB : K * (B * B.transpose) = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← Matrix.mul_assoc, hKB, smul_mul_assoc, nonsing_inv_mul _ huBT]
  have hBB : B * B.transpose = c • K⁻¹ := by
    calc
      _ = K⁻¹ * (K * (B * B.transpose)) := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ huK, one_mul]
      _ = c • K⁻¹ := by rw [hKBB, Matrix.mul_smul, Matrix.mul_one]
  have htrace : (B.transpose * H * B).trace = c * (K⁻¹ * H).trace := by
    rw [trace_mul_cycle, hBB, smul_mul_assoc, trace_smul, smul_eq_mul]
  rw [htrace, isothermalEnergyWeight, ← hJac]
  ring

/-- Adding a positive scalar metric to a semidefinite actual Gram
matrix gives a positive metric, including zero and rank-one matrices.
Source: derivation 30, positive regularization for MT Lemma 19.2. -/
theorem positive_regularized_gram (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    (H + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef :=
  Matrix.PosDef.posSemidef_add hH (Matrix.PosDef.one.smul hδ)

/-- The limiting regularized energy weight is bounded by the actual
regularized area density. No positive rank is required of H.
Source: derivation 30, epsilon-conformal competitors for MT Lemma 19.2. -/
theorem isothermalEnergyWeight_regularized_le
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : H.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    isothermalEnergyWeight (H + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) H ≤
      Real.sqrt (H + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det := by
  let K := H + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have hK : K.PosDef := positive_regularized_gram H hH hδ
  have hrep : H = K - δ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    dsimp only [K]
    abel
  have htrace : (K⁻¹ * H).trace = 2 - δ * K⁻¹.trace := by
    rw [hrep, mul_sub, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hK.det_pos.ne'),
      Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, smul_eq_mul]
    norm_num
  have hbound : (1 / 2 : ℝ) * (K⁻¹ * H).trace ≤ 1 := by
    rw [htrace]
    have hp := hK.inv.posSemidef.trace_nonneg
    nlinarith [mul_nonneg hδ.le hp]
  change (1 / 2 : ℝ) * (K⁻¹ * H).trace * Real.sqrt K.det ≤ Real.sqrt K.det
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg K.det)

end Matrix
