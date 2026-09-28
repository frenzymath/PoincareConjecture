import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.CutoffGradient

open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

theorem exists_uniform_cutoff_gradient_bound
    {a : Fin n → Fin n → Spacetime n → ℝ} {χ : Spacetime n → ℝ} {κ M : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hEll : ∀ z ∈ tsupport χ, ∀ ξ : Euclid n,
      κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j z * ξ i * ξ j) :
    ∃ B : ℝ, 0 < B ∧ ∀ {u f : Spacetime n → ℝ} {F : Fin n → Spacetime n → ℝ},
      ContDiff ℝ ∞ u → ContDiff ℝ ∞ f → (∀ i, ContDiff ℝ ∞ (F i)) →
      (∀ z ∈ tsupport χ, |u z| ≤ M) → (∀ z ∈ tsupport χ, |f z| ≤ M) →
      (∀ i z, z ∈ tsupport χ → |F i z| ≤ M) →
      (∀ z ∈ tsupport χ, timeDeriv u z -
        ∑ i, spatialDeriv i (fun y => ∑ j, a i j y * spatialDeriv j u y) z =
        f z + ∑ i, spatialDeriv i (F i) z) →
      (∫ z, ∑ i, (χ z * spatialDeriv i u z) ^ 2) ≤ B := by
  let S : Spacetime n → ℝ := fun z => χ z ^ 2
  let T : Spacetime n → ℝ := fun z => |χ z * timeDeriv χ z|
  let C : Spacetime n → ℝ := fun z => ∑ i, |χ z * spatialDeriv i χ z|
  let P : Spacetime n → ℝ := fun z => ∑ i,
    (|χ z| + 2 * ∑ j, |spatialDeriv j χ z * a j i z|) ^ 2
  have hzero {z : Spacetime n} (hz : z ∉ tsupport χ) :
      χ z = 0 ∧ ∀ i, spatialDeriv i χ z = 0 := by
    refine ⟨image_eq_zero_of_notMem_tsupport hz, fun i => ?_⟩
    exact image_eq_zero_of_notMem_tsupport
      (fun h => hz (tsupport_fderiv_apply_subset ℝ (spatialDirection i) h))
  have hint {g : Spacetime n → ℝ} (hg : Continuous g)
      (hg0 : ∀ z, z ∉ tsupport χ → g z = 0) : Integrable g :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.intro hχc hg0)
  have hS : Integrable S := hint (hχ.continuous.pow 2) (fun z hz => by simp [S, (hzero hz).1])
  have hT : Integrable T := hint
    ((hχ.continuous.mul (contDiff_timeDeriv hχ).continuous).abs)
    (fun z hz => by simp [T, (hzero hz).1])
  have hC : Integrable C := hint
    (continuous_finsetSum _ (fun i _ =>
      (hχ.continuous.mul (contDiff_spatialDeriv hχ i).continuous).abs))
    (fun z hz => by simp [C, (hzero hz).1])
  have hP : Integrable P := hint
    (continuous_finsetSum _ (fun i _ =>
      (hχ.continuous.abs.add (continuous_const.mul (continuous_finsetSum _ (fun j _ =>
        ((contDiff_spatialDeriv hχ j).continuous.mul (ha j i).continuous).abs)))).pow 2))
    (fun z hz => by simp [P, (hzero hz).1, (hzero hz).2])
  let A : ℝ := M ^ 2 * (∫ z, S z) + M ^ 2 * (∫ z, T z) +
    2 * (M ^ 2 * (∫ z, C z)) + (1 / (2 * κ)) * (M ^ 2 * (∫ z, P z))
  refine ⟨|2 * A / κ| + 1, by positivity, ?_⟩
  intro u f F hu hf hF huB hfB hFB heq
  have hmul {v w : ℝ} (hv : |v| ≤ M) (hw : |w| ≤ M) : |v * w| ≤ M ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hv hw (abs_nonneg _) hM
  have hsq {v : ℝ} (hv : |v| ≤ M) : v ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg v) hv 2
  have hSb : |∫ z, χ z ^ 2 * f z * u z| ≤ M ^ 2 * (∫ z, S z) := by
    have h := norm_integral_le_of_norm_le (hS.const_mul (M ^ 2))
      (Eventually.of_forall (fun z => show ‖χ z ^ 2 * f z * u z‖ ≤ M ^ 2 * S z from by
        by_cases hz : z ∈ tsupport χ
        · have hb := mul_le_mul_of_nonneg_left (hmul (hfB z hz) (huB z hz)) (sq_nonneg (χ z))
          simpa only [S, Real.norm_eq_abs, abs_mul, abs_sq, mul_assoc, mul_comm (M ^ 2)] using hb
        · simp [S, (hzero hz).1]))
    simpa only [Real.norm_eq_abs, integral_const_mul] using h
  have hTb : |∫ z, χ z * timeDeriv χ z * u z ^ 2| ≤ M ^ 2 * (∫ z, T z) := by
    have h := norm_integral_le_of_norm_le (hT.const_mul (M ^ 2))
      (Eventually.of_forall (fun z => show ‖χ z * timeDeriv χ z * u z ^ 2‖ ≤ M ^ 2 * T z from by
        by_cases hz : z ∈ tsupport χ
        · have hb := mul_le_mul_of_nonneg_left (hsq (huB z hz)) (abs_nonneg (χ z * timeDeriv χ z))
          simpa only [T, Real.norm_eq_abs, abs_mul, abs_sq, mul_comm (M ^ 2)] using hb
        · simp [T, (hzero hz).1]))
    simpa only [Real.norm_eq_abs, integral_const_mul] using h
  have hCb : |∫ z, ∑ i, χ z * u z * F i z * spatialDeriv i χ z| ≤
      M ^ 2 * (∫ z, C z) := by
    have h := norm_integral_le_of_norm_le (hC.const_mul (M ^ 2))
      (Eventually.of_forall (fun z => show ‖∑ i, χ z * u z * F i z * spatialDeriv i χ z‖ ≤ M ^ 2 * C z from by
        rw [Real.norm_eq_abs]
        by_cases hz : z ∈ tsupport χ
        · calc
            |∑ i, χ z * u z * F i z * spatialDeriv i χ z| ≤
                ∑ i, |χ z * u z * F i z * spatialDeriv i χ z| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, M ^ 2 * |χ z * spatialDeriv i χ z| := by
              apply Finset.sum_le_sum
              intro i hi
              have hb := mul_le_mul_of_nonneg_left (hmul (huB z hz) (hFB i z hz))
                (abs_nonneg (χ z * spatialDeriv i χ z))
              simpa only [abs_mul, mul_assoc, mul_left_comm, mul_comm] using hb
            _ = _ := by simp only [C, Finset.mul_sum]
        · simp [C, (hzero hz).1]))
    simpa only [Real.norm_eq_abs, integral_const_mul] using h
  have hPb : (∫ z, ∑ i,
      (χ z * F i z + 2 * u z * ∑ j, spatialDeriv j χ z * a j i z) ^ 2) ≤
      M ^ 2 * (∫ z, P z) := by
    have hpoint (z : Spacetime n) :
        ‖∑ i, (χ z * F i z + 2 * u z * ∑ j, spatialDeriv j χ z * a j i z) ^ 2‖ ≤ M ^ 2 * P z := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      by_cases hz : z ∈ tsupport χ
      · rw [show M ^ 2 * P z = ∑ i, M ^ 2 *
          (|χ z| + 2 * ∑ j, |spatialDeriv j χ z * a j i z|) ^ 2 by simp only [P, Finset.mul_sum]]
        apply Finset.sum_le_sum
        intro i hi
        have hb : |χ z * F i z + 2 * u z * ∑ j, spatialDeriv j χ z * a j i z| ≤
            M * (|χ z| + 2 * ∑ j, |spatialDeriv j χ z * a j i z|) := by
          calc
            _ ≤ |χ z * F i z| + |2 * u z * ∑ j, spatialDeriv j χ z * a j i z| := abs_add_le _ _
            _ ≤ |χ z| * M + 2 * M * ∑ j, |spatialDeriv j χ z * a j i z| := by
              simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              have habs : |∑ j, spatialDeriv j χ z * a j i z| ≤
                  ∑ j, |spatialDeriv j χ z * a j i z| :=
                Finset.abs_sum_le_sum_abs _ _
              gcongr
              · exact hFB i z hz
              · exact huB z hz
              · simpa only [abs_mul] using habs
            _ = _ := by ring
        have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
        simpa only [sq_abs, mul_pow] using hs
      · simp [P, (hzero hz).1, (hzero hz).2]
    have h := norm_integral_le_of_norm_le (hP.const_mul (M ^ 2)) (Eventually.of_forall hpoint)
    rw [integral_const_mul] at h
    exact (le_abs_self _).trans h
  have he := parabolic_cutoff_gradient_energy hκ ha hF hu hf hχ hχc hEll heq
  have hbound : (κ / 2) * (∫ z, ∑ i, (χ z * spatialDeriv i u z) ^ 2) ≤ A := by
    have hPf := mul_le_mul_of_nonneg_left hPb (by positivity : 0 ≤ 1 / (2 * κ))
    dsimp only [A]
    linarith [le_abs_self (∫ z, χ z ^ 2 * f z * u z),
      le_abs_self (∫ z, χ z * timeDeriv χ z * u z ^ 2),
      neg_le_abs (∫ z, ∑ i, χ z * u z * F i z * spatialDeriv i χ z)]
  have hbound' : (∫ z, ∑ i, (χ z * spatialDeriv i u z) ^ 2) ≤ 2 * A / κ := by
    apply (le_div_iff₀ hκ).2
    linarith
  exact hbound'.trans ((le_abs_self _).trans (by linarith))

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
