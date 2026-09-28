import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFourierTrace
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.PSeries












set_option autoImplicit false

open Set MeasureTheory AddCircle
open scoped ENNReal

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

private noncomputable def fourierModeProduct (n : ℤ) :
    ℂ →L[ℂ] ℂ →L[ℂ] C(AddCircle L, ℂ) :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (fourier n))

private theorem norm_fourierModeProduct_le (n : ℤ) :
    ‖fourierModeProduct (L := L) n‖ ≤ (1 : NNReal) := by
  simp [fourierModeProduct, ContinuousLinearMap.norm_smulRight_apply,
    ContinuousLinearMap.norm_id, fourier_norm]




noncomputable def weightedFourier (w : lp (fun _ : ℤ => ℂ) 2) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] C(AddCircle L, ℂ) :=
  lp.dualPairing 2 2 (fourierModeProduct (L := L)) (norm_fourierModeProduct_le (L := L)) w



theorem norm_weightedFourier_le (w u : lp (fun _ : ℤ => ℂ) 2) :
    ‖weightedFourier (L := L) w u‖ ≤ ‖w‖ * ‖u‖ := by
  have h := (lp.dualPairing 2 2 (fourierModeProduct (L := L))
    (norm_fourierModeProduct_le (L := L))).le_of_opNorm₂_le_of_le
      (lp.norm_dualPairing (p := 2) (q := 2) (fourierModeProduct (L := L))
        (norm_fourierModeProduct_le (L := L)))
      (le_refl ‖w‖) (le_refl ‖u‖)
  simpa only [weightedFourier, NNReal.coe_one, one_mul] using h




theorem weightedFourier_hasSum (w u : lp (fun _ : ℤ => ℂ) 2) :
    HasSum (fun n : ℤ => (w n * u n) • (fourier n : C(AddCircle L, ℂ)))
      (weightedFourier w u) := by
  have hm := (lp.memℓp w).holder 1 (lp.memℓp u)
    (fourierModeProduct (L := L)) (norm_fourierModeProduct_le (L := L))
  have hn : Summable (fun n : ℤ => ‖fourierModeProduct (L := L) n (w n) (u n)‖) := by
    simpa using hm.summable
  simpa only [weightedFourier, lp.dualPairing_apply, fourierModeProduct,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul]
    using hn.of_norm.hasSum




theorem weightedFourier_eq_of_coeff (w u : lp (fun _ : ℤ => ℂ) 2)
    (f : C(AddCircle L, ℂ)) (hcoeff : ∀ n, w n * u n = fourierCoeff f n) :
    weightedFourier w u = f := by
  have hm := (lp.memℓp w).holder 1 (lp.memℓp u)
    (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
  have hn : Summable (fun n : ℤ => ‖w n * u n‖) := by simpa using hm.summable
  have hc : Summable (fourierCoeff f) := by simpa only [hcoeff] using hn.of_norm
  apply (weightedFourier_hasSum w u).unique
  simpa only [hcoeff] using (hasSum_fourier_series_of_summable hc)

omit [Fact (0 < L)] in



theorem memℓp_periodic_decayWeight (hL : 0 < L) :
    Memℓp (fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)) 2 := by
  have hseries : Summable (fun n : ℤ =>
      (L / (2 * Real.pi)) ^ 2 * (1 / (n : ℝ) ^ 2) + if n = 0 then 1 else 0) :=
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
      ((L / (2 * Real.pi)) ^ 2)).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  have hmajor (n : ℤ) : 1 / (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) ≤
      (L / (2 * Real.pi)) ^ 2 * (1 / (n : ℝ) ^ 2) + if n = 0 then 1 else 0 := by
    by_cases hn : n = 0
    · subst n
      norm_num
    · rw [if_neg hn, add_zero]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have homega : 2 * Real.pi * (n : ℝ) / L ≠ 0 := by
        exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnR) hL.ne'
      calc
        _ ≤ 1 / (2 * Real.pi * (n : ℝ) / L) ^ 2 := by
          exact one_div_le_one_div_of_le (sq_pos_of_ne_zero homega) (by linarith)
        _ = _ := by field_simp
  have hs : Summable (fun n : ℤ => 1 / (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hmajor hseries
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  convert hs using 1
  ext n
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]

end PoincareConjecture.M63
