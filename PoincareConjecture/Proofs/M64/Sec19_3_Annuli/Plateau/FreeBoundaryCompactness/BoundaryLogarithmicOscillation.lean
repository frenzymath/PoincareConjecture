import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.BoundaryShellOscillation

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain

def upperBoundaryDisk (x rho : ℝ) : Set LoopPlane :=
  Metric.closedBall (annulusPoint x 0) rho ∩ {p | 0 < p 1}

theorem upperBoundaryDisk_measurable (x rho : ℝ) : MeasurableSet (upperBoundaryDisk x rho) :=
  measurableSet_closedBall.inter (measurableSet_lt measurable_const (by fun_prop))

theorem upperBoundaryDisk_mono (x : ℝ) {r R : ℝ} (h : r ≤ R) :
    upperBoundaryDisk x r ⊆ upperBoundaryDisk x R :=
  inter_subset_inter_left _ (Metric.closedBall_subset_closedBall h)

theorem upperBoundaryShell_eq_sdiff (x rho : ℝ) :
    upperBoundaryShell x rho =
      upperBoundaryDisk x rho \ upperBoundaryDisk x (rho * Real.exp (-1)) := by
  ext p
  simp only [upperBoundaryShell, upperBoundaryDisk, mem_inter_iff, Set.mem_sdiff]
  tauto

theorem upperBoundaryShell_integral_eq
    (x : ℝ) {rho : ℝ} (hrho : 0 ≤ rho) {F : LoopPlane → ℝ}
    (hF : IntegrableOn F (upperBoundaryDisk x rho)) :
    (∫ p in upperBoundaryShell x rho, F p) =
      (∫ p in upperBoundaryDisk x rho, F p) -
        ∫ p in upperBoundaryDisk x (rho * Real.exp (-1)), F p := by
  rw [upperBoundaryShell_eq_sdiff]
  apply setIntegral_sdiff (upperBoundaryDisk_measurable _ _) hF
  exact upperBoundaryDisk_mono x (mul_le_of_le_one_right hrho
    (Real.exp_le_one_iff.mpr (by norm_num)))

theorem boundary_logarithmic_oscillation
    (L : LoopPlane → ℝ) (hLc : Continuous L) (hL : ContDiffOn ℝ 1 L S)
    (hmono : MonotoneOn (fun t => L (annulusPoint t 0)) (Icc (0 : ℝ) curvePeriod))
    {x rho : ℝ} (hrho : 0 < rho) (hx : rho < x)
    (hP : x + rho < curvePeriod) (hr : rho < 1)
    (hF : IntegrableOn (phaseGradientDensity L) (upperBoundaryDisk x rho))
    {N : ℕ} (hN : 0 < N) :
    (L (annulusPoint (x + rho * Real.exp (-(N : ℝ))) 0) -
      L (annulusPoint (x - rho * Real.exp (-(N : ℝ))) 0)) ^ 2 ≤
        Real.pi * (∫ p in upperBoundaryDisk x rho, phaseGradientDensity L p) / N := by
  let R : ℕ → ℝ := fun j => rho * Real.exp (-(j : ℝ))
  let E : ℕ → ℝ := fun j => ∫ p in upperBoundaryDisk x (R j), phaseGradientDensity L p
  have hEpos (j : ℕ) : 0 ≤ E j :=
    integral_nonneg (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))
  obtain ⟨j, hj, hdrop⟩ := m64_exists_small_energy_drop E hN (hEpos N)
  have hR (k : ℕ) : 0 < R k := mul_pos hrho (Real.exp_pos _)
  have hRle (k : ℕ) : R k ≤ rho :=
    mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k)))
  have hRanti {k l : ℕ} (hkl : k ≤ l) : R l ≤ R k := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hrho.le
    exact neg_le_neg (by exact_mod_cast hkl)
  have hRsucc : R (j + 1) = R j * Real.exp (-1) := by
    simp only [R, Nat.cast_add, Nat.cast_one, neg_add_rev, Real.exp_add]
    ring
  have hR0 : R 0 = rho := by simp [R]
  have hint (k : ℕ) : IntegrableOn (phaseGradientDensity L) (upperBoundaryDisk x (R k)) :=
    hF.mono_set (upperBoundaryDisk_mono x (hRle k))
  have hshell : IntegrableOn (phaseGradientDensity L) (upperBoundaryShell x (R j)) := by
    rw [upperBoundaryShell_eq_sdiff]
    exact (hint j).mono_set sdiff_subset
  have hosc := boundary_shell_oscillation L hLc hL hmono (hR j)
    ((hRle j).trans_lt hx) (by linarith [hRle j]) ((hRle j).trans_lt hr) hshell
  rw [upperBoundaryShell_integral_eq x (hR j).le (hint j), ← hRsucc] at hosc
  have hsmall := monotone_boundary_oscillation_sq_mono L hmono (hR N).le
    (hRanti (Nat.succ_le_iff.mpr hj)) ((hRle (j + 1)).trans_lt hx)
    (by linarith [hRle (j + 1)])
  have hfinal := hsmall.trans (hosc.trans (mul_le_mul_of_nonneg_left hdrop Real.pi_pos.le))
  change _ ≤ Real.pi * (E 0 / N) at hfinal
  rw [show E 0 = ∫ p in upperBoundaryDisk x rho, phaseGradientDensity L p by
    simp only [E, hR0]] at hfinal
  simpa only [R, mul_div_assoc] using hfinal

end PoincareConjecture.M64
