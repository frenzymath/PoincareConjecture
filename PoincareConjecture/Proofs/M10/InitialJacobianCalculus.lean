import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M10

theorem tendsto_scaled_sqrt_det {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hA : Tendsto (fun s : ℝ ↦ (s⁻¹) ^ 2 • A s) (𝓝[>] (0 : ℝ))
      (𝓝 ((4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))) :
    Tendsto (fun s : ℝ ↦ (s ^ n)⁻¹ * Real.sqrt (A s).det)
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ) ^ n)) := by
  have hdet := (Real.continuous_sqrt.comp continuous_id.matrix_det).continuousAt.tendsto.comp hA
  simp only [Function.comp_def, id_eq] at hdet
  have hlimit : Real.sqrt (((4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det) =
      (2 : ℝ) ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    have hp : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [hp, Real.sqrt_sq (pow_nonneg (by norm_num) n)]
  rw [hlimit] at hdet
  apply hdet.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Matrix.det_smul, Fintype.card_fin]
  have hp : ((s⁻¹) ^ 2) ^ n = ((s⁻¹) ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hp, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (pow_nonneg (inv_nonneg.2 hs.le) n), inv_pow]

end PoincareConjecture.M10
