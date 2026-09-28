import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.LogarithmicContinuity

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M64

theorem uniformEquicontinuous_of_monotone_logarithmic_gap
    {I : Type*} (f : I → ℝ → ℝ) (hmono : ∀ i, Monotone (f i))
    {rho : ℝ} (hrho : 0 < rho) (C : ℝ)
    (hgap : ∀ i x, ∀ N : ℕ, 0 < N →
      (f i (x + rho * Real.exp (-(N : ℝ))) - f i (x - rho * Real.exp (-(N : ℝ)))) ^ 2 ≤ C / N) :
    UniformEquicontinuous f := by
  apply Metric.uniformEquicontinuous_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C / eps ^ 2))
  have hNpos : 0 < N := by
    have hh : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hN)
    exact_mod_cast hh
  have hsmall : C / N < eps ^ 2 := by
    apply (div_lt_iff₀ (by exact_mod_cast hNpos : (0 : ℝ) < N)).mpr
    have hh := (div_lt_iff₀ (sq_pos_of_pos heps)).mp ((le_max_right _ _).trans_lt hN)
    nlinarith
  let d := rho * Real.exp (-(N : ℝ))
  have hd : 0 < d := mul_pos hrho (Real.exp_pos _)
  refine ⟨d, hd, ?_⟩
  intro x y hxy i
  rw [Real.dist_eq] at hxy
  have hxy' := abs_lt.mp hxy
  have hlx := hmono i (show x - d ≤ x by linarith)
  have hxu := hmono i (show x ≤ x + d by linarith)
  have hly := hmono i (show x - d ≤ y by linarith)
  have hyu := hmono i (show y ≤ x + d by linarith)
  have hgap' := (hgap i x N hNpos).trans_lt hsmall
  have hspan : f i (x + d) - f i (x - d) < eps := by
    change (f i (x + d) - f i (x - d)) ^ 2 < eps ^ 2 at hgap'
    nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end PoincareConjecture.M64
