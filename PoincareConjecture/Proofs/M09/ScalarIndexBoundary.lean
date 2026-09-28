import PoincareConjecture.Proofs.M09.ScalarIndexForm
import Mathlib.Analysis.Normed.Group.Bounded








set_option autoImplicit false

open scoped ContDiff Topology intervalIntegral

namespace PoincareConjecture.Proofs.M09

theorem scalarMixedIndex_linear_boundary (B C : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hw0 : w 0 = 0) :
    scalarMixedIndex B C c (fun s ↦ s / c) w = (1 / c + B c / 2) * w c +
      ∫ s in 0..c, (C s - deriv B s / 2) * (s / c) * w s := by
  let Q : ℝ → ℝ := fun s ↦ (1 / c + B s / 2 * (s / c)) * w s
  have hQ : ContDiffOn ℝ ∞ Q U :=
    (contDiffOn_const.add ((hB.div_const 2).mul (contDiffOn_id.div_const c))).mul hw
  have hQi : IntervalIntegrable (deriv Q) MeasureTheory.volume 0 c :=
    (((hQ.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn).mono hKU).intervalIntegrable_of_Icc hc.le
  have hRi : IntervalIntegrable (fun s ↦ (C s - deriv B s / 2) * (s / c) * w s)
      MeasureTheory.volume 0 c :=
    ((((hC.continuousOn.sub (((hB.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn).div_const 2)).mul
      (continuousOn_id.div_const c)).mul hw.continuousOn).mono hKU).intervalIntegrable_of_Icc hc.le
  have hder (s : ℝ) (hs : s ∈ Set.Icc 0 c) :
      scalarMixedIndexDensity B C (fun r ↦ r / c) w s =
        deriv Q s + (C s - deriv B s / 2) * (s / c) * w s := by
    have hBd := ((hB.contDiffAt (hU.mem_nhds (hKU hs))).differentiableAt (by simp)).hasDerivAt
    have hwd := ((hw.contDiffAt (hU.mem_nhds (hKU hs))).differentiableAt (by simp)).hasDerivAt
    have hyd : HasDerivAt (fun r : ℝ ↦ r / c) (1 / c) s :=
      (hasDerivAt_id s).div_const c
    have hQd := ((((hBd.div_const 2).mul hyd).const_add (1 / c)).mul hwd).deriv
    change deriv Q s = _ at hQd
    dsimp only [scalarMixedIndexDensity]
    rw [hQd, hyd.deriv]
    simp only [Pi.mul_apply]
    ring
  have hFTC : (∫ s in 0..c, deriv Q s) = Q c - Q 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hQi
    intro s hs
    have hs' : s ∈ Set.Icc 0 c := by simpa only [Set.uIcc_of_le hc.le] using hs
    exact ((hQ.contDiffAt (hU.mem_nhds (hKU hs'))).differentiableAt (by simp)).hasDerivAt
  unfold scalarMixedIndex
  calc
    (∫ s in 0..c, scalarMixedIndexDensity B C (fun r ↦ r / c) w s) =
        ∫ s in 0..c, deriv Q s + (C s - deriv B s / 2) * (s / c) * w s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hder s (by simpa only [Set.uIcc_of_le hc.le] using hs)
    _ = _ := by
      rw [intervalIntegral.integral_add hQi hRi, hFTC]
      simp only [Q, div_self hc.ne', mul_one, hw0, mul_zero, sub_zero]

theorem integral_normalized_power (c : ℝ) (hc : 0 < c) (m : ℕ) :
    (∫ s in 0..c, (s / c) ^ m) = c / (m + 1 : ℝ) := by
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, pow_succ]
  field_simp [hc.ne']

theorem scalarIndex_boundary_rigidity (B C : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (d : ℝ)
    (hcompare : ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f U → f 0 = 0 →
      d * f c ^ 2 ≤ scalarIndex B C c f)
    (heq : scalarIndex B C c (fun s ↦ s / c) = d) :
    d = 1 / c + B c / 2 := by
  let R : ℝ → ℝ := fun s ↦ C s - deriv B s / 2
  have hR : ContinuousOn R (Set.Icc 0 c) :=
    (hC.continuousOn.sub (((hB.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn).div_const 2)).mono hKU
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  have hK0 : 0 ≤ K := (norm_nonneg (R 0)).trans (hK 0 ⟨le_rfl, hc.le⟩)
  let a := d - (1 / c + B c / 2)
  have hbound (m : ℕ) : |a| ≤ K * c / ((m : ℝ) + 3) := by
    let w : ℝ → ℝ := fun s ↦ (s / c) ^ (m + 1)
    have hw : ContDiffOn ℝ ∞ w U := (contDiffOn_id.div_const c).pow (m + 1)
    have hw0 : w 0 = 0 := by simp [w]
    have hwc : w c = 1 := by simp [w, hc.ne']
    have hstat := scalarIndex_stationary B C c hc U hU hKU hB.continuousOn hC.continuousOn
      d hcompare heq w hw hw0
    rw [scalarMixedIndex_linear_boundary B C c hc U hU hKU hB hC w hw hw0,
      hwc, mul_one, mul_one] at hstat
    have hpower : (fun s ↦ (C s - deriv B s / 2) * (s / c) * w s) =
        fun s ↦ R s * (s / c) ^ (m + 2) := by
      funext s
      dsimp only [R, w]
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring
    rw [hpower] at hstat
    have ha : a = ∫ s in 0..c, R s * (s / c) ^ (m + 2) := by
      dsimp only [a]
      linarith
    have hki : IntervalIntegrable (fun s : ℝ ↦ K * (s / c) ^ (m + 2))
        MeasureTheory.volume 0 c :=
      ((continuous_const.mul ((continuous_id.div_const c).pow (m + 2))).intervalIntegrable 0 c)
    have hi := intervalIntegral.norm_integral_le_of_norm_le hc.le
      (f := fun s ↦ R s * (s / c) ^ (m + 2))
      (Filter.Eventually.of_forall (fun s (hs : s ∈ Set.Ioc 0 c) ↦ by
        have hp : 0 ≤ (s / c) ^ (m + 2) := pow_nonneg (div_nonneg hs.1.le hc.le) _
        rw [norm_mul, Real.norm_of_nonneg hp]
        exact mul_le_mul_of_nonneg_right (hK s ⟨hs.1.le, hs.2⟩) hp)) hki
    rw [← ha, Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_normalized_power c hc (m + 2)] at hi
    simpa only [Nat.cast_add, Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num,
      add_assoc, mul_div_assoc] using hi
  have ha0 : a = 0 := by
    by_contra hne
    have hapos : 0 < |a| := abs_pos.mpr hne
    obtain ⟨m, hm⟩ := exists_nat_gt (K * c / |a|)
    have hlt := (div_lt_iff₀ hapos).mp hm
    have hle := (le_div_iff₀ (by positivity : 0 < (m : ℝ) + 3)).mp (hbound m)
    nlinarith
  dsimp only [a] at ha0
  linarith

end PoincareConjecture.Proofs.M09
